(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27"]

open Type
open Minimir
open Active_borrows

(* This function computes the set of alive lifetimes at every program point. *)
let compute_lft_sets prog mir : lifetime -> PpSet.t =
  (* 0) Préparation des contraintes d’outlives *)
  let outlives = ref LMap.empty in
  let add_outlives (l1, l2) =
    outlives := add_outlives_edge l1 l2 !outlives
  in
  let unify_lft l1 l2 =
    add_outlives (l1, l2);
    add_outlives (l2, l1)
  in

  (* 1) Contraintes issues des types des locaux *)
  Hashtbl.iter
    (fun _ typ ->
      outlives := outlives_union !outlives (implied_outlives prog typ))
    mir.mlocals;

  (* 2) TÂCHE 3 : génération des contraintes “outlives” *)
  let rec unify_types t1 t2 =
    match (t1, t2) with
    | Tborrow (l1, _, u1), Tborrow (l2, _, u2) ->
        unify_lft l1 l2; unify_types u1 u2
    | Tstruct (s1, ls1), Tstruct (s2, ls2) when s1 = s2 ->
        List.iter2 unify_lft ls1 ls2; ()
    | Ti32, Ti32 | Tbool, Tbool | Tunit, Tunit -> ()
    | _ -> ()
  in
  Array.iteri
    (fun _ (instr, _) ->
      match instr with
      | Iassign (dst, RVplace src, _) ->
          let td = typ_of_place prog mir dst in
          let ts = typ_of_place prog mir src in
          unify_types td ts

      | Iassign (dst, RVborrow (_, src), _) ->
          let lnew =
            match typ_of_place prog mir dst with
            | Tborrow (l, _, _) -> l
            | _ -> assert false
          in
          let frees = free_lfts (typ_of_place prog mir src) in
          LSet.iter (fun lold -> add_outlives (lold, lnew)) frees

      | Icall (fid, args, dst, _) ->
          let (params, ret_t, out_rels) = fn_prototype_fresh prog fid in
          List.iter2
            (fun pl p_t -> unify_types (typ_of_place prog mir pl) p_t)
            args params;
          unify_types ret_t (typ_of_place prog mir dst);
          List.iter add_outlives out_rels

      | _ -> ())
    mir.minstrs;

  (* 3) TÂCHE 4 : génération des contraintes “living” *)
  let living = ref LMap.empty in
  let add_living pp l =
    living := LMap.update l
      (function None -> Some (PpSet.singleton pp)
               | Some s -> Some (PpSet.add pp s))
      !living
  in
  let live_locals = Live_locals.go mir in
  Array.iteri
    (fun lbl _ ->
      LocSet.iter
        (fun loc ->
          let pl = PlLocal loc in
          let frees = free_lfts (typ_of_place prog mir pl) in
          LSet.iter (fun l -> add_living (PpLocal lbl) l) frees)
        (live_locals lbl))
    mir.minstrs;
  List.iter (fun l -> add_living (PpInCaller l) l) mir.mgeneric_lfts;

  (* 4) Résolution du point fixe *)
  let module Fix = Fix.Fix.ForType
    (struct type t = lifetime end)
    (Fix.Prop.Set (PpSet))
  in
  Fix.lfp (fun lft lft_sets ->
    (* 4.1) on replie les “outlives” (LSet.t -> PpSet.t) *)
    let outl_set =
      Option.value ~default:LSet.empty (LMap.find_opt lft !outlives)
    in
    let out_ps =
      LSet.fold
        (fun l acc -> PpSet.union (lft_sets l) acc)
        outl_set
        PpSet.empty
    in
    (* 4.2) on ajoute les contraintes “living” directes *)
    let liv_ps =
      Option.value ~default:PpSet.empty (LMap.find_opt lft !living)
    in
    PpSet.union out_ps liv_ps)

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
  
    
  (* TODO: check that we never write to shared borrows, and that we never create mutable borrows
  below shared borrows. Function [place_mut] can be used to determine if a place is mutable, i.e., if it
  does not dereference a shared borrow. *)
  Array.iteri
  (fun _ (instr, loc) ->
    match instr with
    (* Création d’un emprunt mutable : la place doit être mutable *)
    | Iassign (_, RVborrow (Mut, pl), _) ->
        if place_mut prog mir pl = NotMut then
          Error.error loc
            "Creating a mutable borrow under a shared borrow."
    (* Toute écriture (assign ou call sur place) : la place doit être mutable *)
    | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
        if place_mut prog mir pl = NotMut then
          Error.error loc
            "Writing through a shared borrow."
    | _ -> ())
  mir.minstrs;

  let lft_sets = compute_lft_sets prog mir in

  (* TODO: check that outlives constraints declared in the prototype of the function are
    enough to ensure safety. I.e., if [lft_sets lft] contains program point [PpInCaller lft'], this
    means that we need that [lft] be alive when [lft'] dies, i.e., [lft'] outlives [lft]. This relation
    has to be declared in [mir.outlives_graph]. *)
  (* === TÂCHE 5 : vérifier que les contraintes outlives du prototype sont suffisantes === *)
  (* On récupère d’abord l’ensemble de toutes les lifetimes apparues dans les types des locaux *)
  let all_lfts =
    Hashtbl.fold
      (fun _ typ acc -> LSet.union acc (free_lfts typ))
      mir.mlocals
      LSet.empty
  in
  (* Pour chaque lifetime l1, si l1 est encore “vivante” au point PpInCaller l2,
     alors il faut que l2 outlives l1 ait été déclaré dans mir.moutlives_graph. *)
  LSet.iter
    (fun l1 ->
      let pts = lft_sets l1 in
      PpSet.iter
        (function
          | PpInCaller l2 ->
              let declared =
                match LMap.find_opt l2 mir.moutlives_graph with
                | Some deps -> LSet.mem l1 deps
                | None -> false
              in
              if not declared then
                Error.error mir.mloc
                  "Missing outlives constraint: lifetime %s must outlive %s"
                  (string_of_lft l2) (string_of_lft l1)
          | _ -> ())
        pts)
    all_lfts;
  (* === fin de la vérification des outlives du prototype === *)
  (* We check that we never perform any operation which would conflict with an existing
    borrows. *)
  let bor_active_at = Active_borrows.go prog lft_sets mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      (* The list of bor_info for borrows active at this instruction. *)
      let active_borrows_info : bor_info list =
        List.map (get_bor_info prog mir) (BSet.to_list (bor_active_at lbl))
      in

      (* Does there exist a borrow of a place pl', which is active at program point [lbl],
        such that a *write* to [pl] conflicts with this borrow?

         If [pl] is a subplace of pl', then writing to [pl] is always conflicting, because
        it is aliasing with the borrow of pl'.

         If pl' is a subplace of [pl], the situation is more complex:
           - if pl' involves as many dereferences as [pl] (e.g., writing to [x.f1] while
            [x.f1.f2] is borrowed), then the write to [pl] will overwrite pl', hence this is
            conflicting.
           - BUT, if pl' involves more dereferences than [pl] (e.g., writing to [x.f1] while
            [*x.f1.f2] is borrowed), then writing to [pl] will *not* modify values accessible
            from pl'. Hence, subtlely, this is not a conflict. *)
      let conflicting_borrow_no_deref pl =
        List.exists
          (fun bi -> is_subplace pl bi.bplace || is_subplace_no_deref bi.bplace pl)
          active_borrows_info
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
        borrow? In addition, if parameter [write] is true, we consider an operation which is
        both a read and a write. *)
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

            (* === Phase 2 : vérification des lectures, moves et emprunts conflictuels === *)
            (* === Phase 2 : vérification des lectures, moves et emprunts conflictuels === *)
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