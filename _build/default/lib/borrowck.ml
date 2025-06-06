open Type
open Minimir
open Active_borrows

(* This function computes the set of alive lifetimes at every program point. *)
let compute_lft_sets prog mir : lifetime -> PpSet.t =
  (* The [outlives] variable contains all the outlives relations between the
     lifetime variables of the function. *)
  let outlives = ref LMap.empty in

  (* Helper functions to add outlives constraints. *)
  let add_outlives (l1, l2) = outlives := add_outlives_edge l1 l2 !outlives in
  let unify_lft l1 l2 =
    add_outlives (l1, l2);
    add_outlives (l2, l1)
  in

  (* First, we add in [outlives] the constraints implied by the type of locals. *)
  Hashtbl.iter
    (fun _ typ ->
       outlives := outlives_union !outlives (implied_outlives prog typ))
    mir.mlocals;

  (* Then, we add the outlives relations needed for the instructions to be safe. *)
  
  (* TODO: generate these constraints by
       - unifying types that need be equal (note that MiniRust does not support subtyping, that is,
         if a variable x: &'a i32 is used as type &'b i32, then this requires that lifetimes 'a and
         'b are equal),
       - adding constraints required by function calls,
       - generating constraints corresponding to reborrows. More precisely, if we create a borrow
         of a place that dereferences  borrows, then the lifetime of the borrow we
         create should be shorter than the lifetimes of the borrows the place dereference.
         For example, if x: &'a &'b i32, and we create a borrow y = &**x of type &'c i32,
         then 'c should be shorter than 'a and 'b.

    SUGGESTION: use functions [typ_of_place], [fields_types_fresh] and [fn_prototype_fresh].
  *)
  
  Array.iter (fun (instr, _loc) ->
  (* Fonction de unification des types pour gérer les contraintes de lifetime *)
  let rec unify t1 t2 =
    match (t1, t2) with
    | Tborrow (l1, _, inner1), Tborrow (l2, _, inner2) ->
        (* Toute lifetime libre dans inner2 doit outliver l2, et dans inner1 doit outliver l1 *)
        outlives := outlives_union !outlives (implied_outlives prog inner2);
        outlives := outlives_union !outlives (implied_outlives prog inner1);
        (* Les lifetimes doivent correspondre *)
        unify_lft l1 l2;
        (* Récurse sur les types poin­tés *)
        unify inner1 inner2

    | Tstruct (_, lts1), Tstruct (_, lts2) ->
        (* Pour chaque paire de lifetimes dans deux struct identiques, unifier et ajouter contraintes *)
        List.iter2
          (fun lf1 lf2 ->
             outlives := outlives_union !outlives (implied_outlives prog t1);
             outlives := outlives_union !outlives (implied_outlives prog t2);
             unify_lft lf1 lf2)
          lts1 lts2

    | _ -> ()
  in

  (* Gère l'affectation pl := rv *)
  let handle_assign pl rv =
    match (pl, rv) with
    (* Cas spécial : attribution à la variable de retour Lret *)
    | (PlLocal Lret, RVplace pl') ->
        let ty_decl = typ_of_place prog mir (PlLocal Lret) in
        let ty_act  = typ_of_place prog mir pl' in
        (* Ajout des outlives implicites pour les deux types *)
        outlives := outlives_union !outlives (implied_outlives prog ty_decl);
        outlives := outlives_union !outlives (implied_outlives prog ty_act);
        (match (ty_decl, ty_act) with
         | Tborrow (l_decl, _, inner_decl), Tborrow (l_act, _, inner_act) ->
             (* Exiger que la lifetime réelle l_act outlive la déclarée l_decl *)
             add_outlives (l_act, l_decl);
             (* Unifier récursivement les types intérieurs si ce sont des borrows *)
             unify inner_act inner_decl
         | _ ->
             (* Sinon, unifier normalement *)
             unify ty_decl ty_act)

    | _ ->
        (* Tous les autres cas d'affectation *)
        (match rv with
         | RVplace pl' ->
             let ty_l = typ_of_place prog mir pl in
             let ty_r = typ_of_place prog mir pl' in
             outlives := outlives_union !outlives (implied_outlives prog ty_l);
             outlives := outlives_union !outlives (implied_outlives prog ty_r);
             unify ty_l ty_r

         | RVborrow (_, pl2) ->
             (* Si on emprunte pl2 vers pl, vérifier que chaque deref à l'intérieur outlives la destination *)
             (match typ_of_place prog mir pl with
              | Tborrow (l_dest, _, _) ->
                  let rec fold_place p =
                    match p with
                    | PlDeref p_inner ->
                        (match typ_of_place prog mir p_inner with
                         | Tborrow (l_src, _, _) ->
                             add_outlives (l_src, l_dest);
                             fold_place p_inner
                         | _ -> ())
                    | PlField (p_parent, _) ->
                        fold_place p_parent
                    | _ -> ()
                  in
                  fold_place pl2
              | _ -> ())

         | RVmake (struct_name, args) ->
             (* Construction d'une struct : on obtient des lifetimes fraîches pour chaque champ *)
             let (fields_lfts, struct_ty) = fields_types_fresh prog struct_name in
             List.iter2
               (fun expected_ty arg_pl ->
                  outlives := outlives_union !outlives (implied_outlives prog expected_ty);
                  let actual_ty = typ_of_place prog mir arg_pl in
                  unify expected_ty actual_ty)
               fields_lfts
               args;
             (* Unification des lifetimes de la struct fraîche avec la place cible *)
             (match (struct_ty, typ_of_place prog mir pl) with
              | Tstruct (_, fresh_lfts), Tstruct (_, actual_lfts) ->
                  List.iter2 unify_lft fresh_lfts actual_lfts
              | _ -> ())

         | RVbinop (_, pl1, pl2) ->
             let ty1 = typ_of_place prog mir pl1 in
             let ty2 = typ_of_place prog mir pl2 in
             outlives := outlives_union !outlives (implied_outlives prog ty1);
             outlives := outlives_union !outlives (implied_outlives prog ty2)

         | RVunop (_, pl1) ->
             let ty1 = typ_of_place prog mir pl1 in
             outlives := outlives_union !outlives (implied_outlives prog ty1)

         | _ -> ())
  in

  (* Traitement de chaque instruction MIR *)
  match instr with
  | Iassign (pl, rv, _) ->
      handle_assign pl rv

  | Icall (f, args, ret_pl, _) ->
      (* Appel de fonction : on récupère protos et outlives déclarées *)
      let (formals, ret_ty, proto_outlives) = fn_prototype_fresh prog f in
      (* On unifie le type de retour suivi de chaque paramètre dans l'ordre *)
      List.iter2
        (fun expected_ty actual_pl ->
           outlives := outlives_union !outlives (implied_outlives prog expected_ty);
           let actual_ty = typ_of_place prog mir actual_pl in
           unify expected_ty actual_ty)
        (ret_ty :: formals)
        (ret_pl :: args);
      (* Ajouter les contraintes outlives provenant de la signature de la fonction *)
      List.iter add_outlives proto_outlives

  | Iif (pl, _, _) ->
      (* Condition : le type de la place peut contenir des lifetimes libres *)
      let cond_ty = typ_of_place prog mir pl in
      outlives := outlives_union !outlives (implied_outlives prog cond_ty)

  | Ireturn ->
      (* Retour : on ajoute les outlives implicites pour le type de retour déclaré
         et toutes les contraintes explicites déjà présentes *)
      let ret_ty_decl = typ_of_place prog mir (PlLocal Lret) in
      let ret_edges =
        LMap.fold
          (fun lft set acc ->
             LSet.fold (fun lft' acc' -> (lft, lft') :: acc') set acc)
          mir.moutlives_graph
          []
      in
      outlives := outlives_union !outlives (implied_outlives prog ret_ty_decl);
      List.iter add_outlives ret_edges

  | _ -> ())
  mir.minstrs;


  (* The [living] variable contains constraints of the form "lifetime 'a should be
     alive at program point p". *)
  let living : PpSet.t LMap.t ref = ref LMap.empty in

  (* Helper function to add living constraint. *)
  let add_living pp lft =
    living :=
      LMap.update lft
        (fun s -> Some (PpSet.add pp (Option.value ~default:PpSet.empty s)))
        !living
  in

  (* Run the live local analysis. *)
  let live_locals = Live_locals.go mir in

  Array.iteri
  (fun lbl (_instr, _loc) ->
     let pp = PpLocal lbl in

     (* Fonction pour gérer les variables locales vivantes à lbl *)
     let process_live_locals () =
       let locals_live = live_locals lbl in
       LocSet.iter
         (fun local ->
            let ty = Hashtbl.find mir.mlocals local in
            (* Pour chaque lifetime libre dans le type, on l’ajoute comme vivante à pp *)
            LSet.iter (fun lft -> add_living pp lft) (free_lfts ty))
         locals_live
     in

     (* Fonction pour traiter les lifetimes génériques à chaque point de programme *)
     let process_generic_lfts () =
       List.iter (fun lft -> add_living pp lft) mir.mgeneric_lfts
     in

     (* 1) Pour chaque variable locale vivante à lbl, toute lifetime libre doit être marquée vivante *)
     process_live_locals ();

     (* 2) Les lifetimes génériques sont vivantes à chaque point de programme *)
     process_generic_lfts ())
  mir.minstrs;


  (* If [lft] is a generic lifetime, [lft] is always alive at [PpInCaller lft]. *)
  List.iter (fun lft -> add_living (PpInCaller lft) lft) mir.mgeneric_lfts;

  (* Now, we compute lifetime sets by finding the smallest solution of the constraints. *)
  let module Fix =
    Fix.Fix.ForType (struct type t = lifetime end) (Fix.Prop.Set (PpSet))
  in
  Fix.lfp (fun lft lft_sets ->
      LSet.fold
        (fun lft acc -> PpSet.union (lft_sets lft) acc)
        (Option.value ~default:LSet.empty (LMap.find_opt lft !outlives))
        (Option.value ~default:PpSet.empty (LMap.find_opt lft !living)))


let borrowck prog mir =
  (* We check initializedness requirements for every instruction. *)
  let uninitialized_places = Uninitialized_places.go prog mir in
  Array.iteri
    (fun lbl (instr, loc) ->
       let uninit : PlaceSet.t = uninitialized_places lbl in

       let check_initialized pl =
         if PlaceSet.exists (fun pluninit -> is_subplace pluninit pl) uninit then
           Error.error loc "Use of a place which is not fully initialized at this point."
       in

       (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) -> (
          match pl with
          | PlDeref pl0 ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into an uninitialized borrow."
          | PlField (pl0, _) ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into a field of an uninitialized struct."
          | _ -> ())
      | _ -> ());

       match instr with
       | Iassign (_, RVplace pl, _) | Iassign (_, RVborrow (_, pl), _) ->
           check_initialized pl
       | Iassign (_, RVbinop (_, pl1, pl2), _) ->
           check_initialized pl1;
           check_initialized pl2
       | Iassign (_, RVunop (_, pl), _) | Iif (pl, _, _) -> check_initialized pl
       | Iassign (_, RVmake (_, pls), _) | Icall (_, pls, _, _) ->
           List.iter check_initialized pls
       | Ireturn -> check_initialized (PlLocal Lret)
       | Iassign (_, (RVunit | RVconst _), _) | Ideinit _ | Igoto _ -> ())
    mir.minstrs;

  (* We check the code honors the non-mutability of shared borrows. *)
  Array.iteri
  (fun _ (instr, loc) ->
     (* Vérifie qu’on ne crée pas un borrow mutable sous un borrow partagé *)
     let check_mutable_borrow_under_shared pl =
       if place_mut prog mir pl = NotMut then
         Error.error loc
           "Attempting to create a mutable borrow below a shared reference."
     in
     (* Vérifie qu’on n’écrit pas dans une référence partagée *)
     let check_write_into_shared pl =
       if place_mut prog mir pl <> Mut then
         Error.error loc
           "Writing into a shared reference."
     in

     match instr with
     | Iassign (_, RVborrow (Mut, pl), _) ->
         check_mutable_borrow_under_shared pl

     | Iassign (pl, _, _) ->
         check_write_into_shared pl

     | _ -> ())
  mir.minstrs;


  let lft_sets = compute_lft_sets prog mir in

  (* Check that outlives constraints declared in the function’s signature suffice. *)
  List.iter
  (fun lft ->
     (* Vérifie la contrainte d’outlives pour un point de programme donné *)
     let check_constraint_at_pp pp =
       match pp with
       | PpInCaller lft' ->
           (* On ne vérifie que si ce n’est pas la même lifetime *)
           if lft <> lft' then
             let verify_outlives () =
               match LMap.find_opt lft mir.moutlives_graph with
               | Some set when LSet.mem lft' set -> ()
               | _ ->
                   Error.error mir.mloc
                     "Missing outlives constraint: lifetime %s must outlive %s"
                     (string_of_lft lft) (string_of_lft lft')
             in
             verify_outlives ()
       | _ -> ()
     in

     (* Parcourt tous les points où [lft] est vivant et applique la vérification *)
     let process_lft_points () =
       PpSet.iter check_constraint_at_pp (lft_sets lft)
     in

     process_lft_points ())
  mir.mgeneric_lfts;


  (* We check that we never perform any operation which would conflict with an existing
     borrow. *)
  let bor_active_at = Active_borrows.go prog lft_sets mir in
  Array.iteri
    (fun lbl (instr, loc) ->
       (* The list of bor_info for borrows active at this instruction. *)
       let active_borrows_info : bor_info list =
         List.map (get_bor_info prog mir) (BSet.to_list (bor_active_at lbl))
       in

       (* Does there exist a borrow of a place pl', which is active at program point [lbl],
          such that a *write* to [pl] conflicts with this borrow? *)
       let conflicting_borrow_no_deref pl =
         List.exists
           (fun bi -> is_subplace pl bi.bplace || is_subplace_no_deref bi.bplace pl) active_borrows_info
       in

       (match instr with
        | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
            if conflicting_borrow_no_deref pl then
              Error.error loc "Assigning a borrowed place."
        | Ideinit (l, _) ->
            if conflicting_borrow_no_deref (PlLocal l) then
              Error.error loc
                "A local declared here leaves its scope while still being borrowed."
        | Ireturn ->
            Hashtbl.iter
              (fun l _ ->
                 match l with
                 | Lparam p ->
                     if conflicting_borrow_no_deref (PlLocal l) then
                       Error.error loc
                         "When returning from this function, parameter `%s` is still \
                          borrowed."
                         p
                 | _ -> ())
              mir.mlocals
        | _ -> ());

       (* Variant of [conflicting_borrow_no_deref]: does there exist a borrow of a place pl',
          which is active at program point [lbl], such that a *read* to [pl] conflicts with this
          borrow? If [write] is true, we consider an operation which is both a read and a write. *)
       let conflicting_borrow write pl =
         List.exists
           (fun bi ->
              (bi.bmut = Mut || write)
              && (is_subplace pl bi.bplace || is_subplace bi.bplace pl))
           active_borrows_info
       in

       (* Check a "use" (copy or move) of place [pl]. *)
       let check_use pl =
         let consumes = not (typ_is_copy prog (typ_of_place prog mir pl)) in
         if conflicting_borrow consumes pl then
           Error.error loc "A borrow conflicts with the use of this place.";
         if consumes && contains_deref_borrow pl then
           Error.error loc "Moving a value out of a borrow."
       in

       match instr with
      (* — consommation simple ou move d’une place isolée *)
      | Iassign (_, RVplace pl, _) ->
          check_use pl

      (* — opérations binaires : deux lectures potentielles *)
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
          check_use pl1; check_use pl2

      (* — opérations unaires (déréf) *)
      | Iassign (_, RVunop (_, pl), _) ->
          check_use pl

      (* — construction de structure : chaque champ est lu *)
      | Iassign (_, RVmake (_, pls), _) ->
          List.iter check_use pls

      | Iassign (_, RVborrow (mut, pl), _) ->
          if conflicting_borrow (mut = Mut) pl then
            Error.error loc
              "There is a borrow conflicting this borrow."

      (* — branchement : lecture de la condition *)
      | Iif (pl, _, _) ->
          check_use pl

      (* — appel de fonction : tous les arguments sont lus *)
      | Icall (_, pls, _, _) ->
          List.iter check_use pls

      (* — retour : on lit la place de retour *)
      | Ireturn ->
          check_use (PlLocal Lret)
      | _ -> ()) 
    mir.minstrs

