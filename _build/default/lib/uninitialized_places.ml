(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27-33"]

(* You should read and understand active_borrows.ml *fully*, before filling the holes
  in this file. The analysis in this file follows the same structure. *)

  
open Type
open Minimir

type analysis_results = label -> PlaceSet.t

let go prog mir : analysis_results =
  (* The set of all places appearing in the MIR code. We are not interesting in initializedness for places
    which are not member of this set. *)
  let all_places =
    let acc =
      Hashtbl.fold
        (fun l _ acc -> PlaceSet.add (PlLocal l) acc)
        mir.mlocals PlaceSet.empty
    in
    Array.fold_left
      (fun acc (i, _) ->
        match i with
        | Ideinit _ | Igoto _ | Ireturn -> acc
        | Iif (pl, _, _) -> PlaceSet.add pl acc
        | Icall (_, pls, pl, _) -> PlaceSet.add_seq (Seq.cons pl (List.to_seq pls)) acc
        | Iassign (pl, rv, _) -> (
            let acc = PlaceSet.add pl acc in
            match rv with
            | RVplace pl | RVborrow (_, pl) | RVunop (_, pl) -> PlaceSet.add pl acc
            | RVbinop (_, pl1, pl2) -> PlaceSet.add pl1 (PlaceSet.add pl2 acc)
            | RVmake (_, pls) -> PlaceSet.add_seq (List.to_seq pls) acc
            | RVunit | RVconst _ -> acc))
      acc mir.minstrs
  in

  (* The set of subplaces of a given place. *)
  let subplaces = Hashtbl.create 7 in
  let () =
    PlaceSet.iter
      (fun pl ->
        let pls = PlaceSet.filter (fun pl_sub -> is_subplace pl_sub pl) all_places in
        Hashtbl.add subplaces pl pls)
      all_places
  in

  (* Effect of initializing a place [pl] on the abstract state [state]: [pl] and all its subplaces
    become initialized. Hence, given that the state is the set of uninitialized places, we remove
    the subplaces [pl] from the abstract state.

    It is important to understand that places can be nested. In order to make a place uninitialized,
    it is *not* enough to remove it from the state. One should also remove subplaces. *)
  let initialize pl state = PlaceSet.diff state (Hashtbl.find subplaces pl) in

  (* This is the dual: we are consuming or deinitiailizing place [pl], so all its subplaces
    become uninitialized, so they are added to [state]. *)
  let deinitialize pl state = PlaceSet.union state (Hashtbl.find subplaces pl) in

  (* Effect of using (copying or moving) a place [pl] on the abstract state [state]. *)
  let move_or_copy pl state =
    let ty = typ_of_place prog mir pl in
    if typ_is_copy prog ty then state
    else deinitialize pl state
  in

  (* These modules are parameters of the [Fix.DataFlow.ForIntSegment] functor below. *)
  let module Instrs = struct let n = Array.length mir.minstrs end in
  let module Prop = struct
    type property = PlaceSet.t

    let leq_join p q = if PlaceSet.subset p q then q else PlaceSet.union p q
  end in
  let module Graph = struct
    type variable = int
    type property = PlaceSet.t

    (* To complete this module, one can read file active_borrows.ml, which contains a
      similar data flow analysis. *)

  let foreach_root go =
      (* On récupère l'ensemble des places correspondant aux paramètres formels *)
      let param_places =
        Hashtbl.fold
          (fun l _ acc ->
            match l with
            | Lparam _ -> PlaceSet.add (PlLocal l) acc
            | _        -> acc)
          mir.mlocals
          PlaceSet.empty
      in
      (* L'état abstrait est l'ensemble des places non initialisées.
         On enlève de all_places **les paramètres et toutes leurs sous-places**. *)
      let initial =
        PlaceSet.fold
          (fun pl acc -> initialize pl acc)
          param_places
          all_places
    in
    go mir.mentry initial
    
    let foreach_successor lbl state go =
      let instr, _loc = mir.minstrs.(lbl) in
      match instr with
      | Iassign (dst, rv, next) ->
          (* analyse du rvalue *)
          let st1 =
            match rv with
            | RVplace p
            | RVunop (_, p)       -> move_or_copy p state
            | RVborrow (_, _)     -> state
            | RVbinop (_, p1, p2) -> move_or_copy p2 (move_or_copy p1 state)
            | RVmake (_, ps)      -> List.fold_left (fun st p -> move_or_copy p st) state ps
            | RVunit | RVconst _  -> state
          in
          (* affectation initialise dst *)
          go next (initialize dst st1)

      | Ideinit (l, next) ->
          go next (deinitialize (PlLocal l) state)

      | Igoto next ->
          go next state

      | Iif (p, t1, t2) ->
          let st' = move_or_copy p state in
          go t1 st'; go t2 st'

      | Ireturn ->
          ()

      | Icall (_f, args, dst, next) ->
          let st1 = List.fold_left (fun st p -> move_or_copy p st) state args in
          go next (initialize dst st1)
  end in
  let module Fix = Fix.DataFlow.ForIntSegment (Instrs) (Prop) (Graph) in
  fun i -> Option.value (Fix.solution i) ~default:PlaceSet.empty
