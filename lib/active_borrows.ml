open Type
open Minimir

(* Borrows are identified with the label of the instruction that creates them. *)
type bor = label
type bor_info = { blft : lifetime; bmut : mut; bplace : place }

let get_bor_info prog mir bor =
  match fst mir.minstrs.(bor) with
  | Iassign (pl_to, RVborrow (bmut, bplace), _) -> (
      match typ_of_place prog mir pl_to with
      | Tborrow (blft, _, _) -> { blft; bmut; bplace }
      | _ -> assert false)
  | _ -> assert false

module BSet = Set.Make (Int)

type analysis_results = label -> BSet.t

let go prog lft_sets mir : analysis_results =
  (* The dataflow analysis is computed using the Fix library.
    It requires us to provide: *)

  (* - A description of the set of instructions. *)
  let module Instrs = struct let n = Array.length mir.minstrs end in
  (* - A description of "properties", the abstract domain of the analysis. Here we
    track sets of borrows at every program point. *)
  let module Prop = struct
    type property = BSet.t (* Sets of borrows. *)

    (* [leq_join] should compute the join of the two parameters, and the result
      should be physically equal to [q] if [p] is included in [q]. *)
    let leq_join p q = if BSet.subset p q then q else BSet.union p q
  end in
  (* - A description of the "graph" of the analysis: we describe to Fix the control
    flow graph, together with the effect of instructions to the abstract state. *)
  let module Graph = struct
    type variable = label
    type property = BSet.t

    (* The function [foreach_root] should call the [go] parameter for each entry point
      of the CFG, with the corresponding initial abstract state. *)
    let foreach_root go =
      (* The only entry point is [mir.mentry], with initial abstract state [BSet.empty]. *)
      go mir.mentry BSet.empty

    (* The function [foreach_successor] should call the [go] parameter for each successor
      of [lbl], with the corresponding modified abstract state.

      For a given label, [Fix] will then automatically compute the join of the initial
      abstract state (if it exists) and of the modified states propagated by each of its
      predecessors. *)
    let foreach_successor lbl state go =
      let go next state =
        (* The state of the successor [next] of [lbl] should not contain any borrow
          whose lifetime is dead at [next]. We filter them out here. *)
        go next
          (BSet.filter
             (fun bor -> PpSet.mem (PpLocal next) (lft_sets (get_bor_info prog mir bor).blft))
             state)
      in

      let assign pl state =
        (* When writing to a place, we de-activate any borrows of any of its sub-place. *)
        BSet.filter (fun bor -> not (is_subplace (get_bor_info prog mir bor).bplace pl)) state
      in

      match fst mir.minstrs.(lbl) with
      | Iassign (pl, RVborrow (_, _), next) ->
          (* In the case the current instruction is the creation of a borrow, we make that
            borrow active, then perform the assignment and propagate to the successor (with [go]). *)
          let state = BSet.add lbl state in
          go next (assign pl state)
      | Iassign (pl, _, next) -> go next (assign pl state)
      | Ideinit (l, next) -> go next (assign (PlLocal l) state)
      | Igoto next -> go next state
      | Iif (_, next1, next2) ->
          (* [Iif] instructions do not modify the abstract state, but propagate to two accessors. *)
          go next1 state;
          go next2 state
      | Ireturn -> ()
      | Icall (_, _, pl, next) -> go next (assign pl state)
  end in
  let module Fix = Fix.DataFlow.ForIntSegment (Instrs) (Prop) (Graph) in
  fun i -> Option.value (Fix.solution i) ~default:BSet.empty
