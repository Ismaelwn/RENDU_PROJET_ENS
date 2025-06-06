open Type
open Minimir

(** Given the lifetime sets, describing at which program point a lifetime is alive, this
    modules computes which {i borrow} is active at which program point.

    Here, a {i borrow} correspond to a [Iassign(pl, RVborrow _, _)] instruction in
    minimir, Such a borrow "freezes" the place [pl]: as long as it is active, some
    accesses conflicting with this place are forbidden. If this borrow is mutable, then no
    other access is allowed. It it is shared, then only reads are allowed.

    A borrow becomes active after its corresponding borrowing instruction. It becomes
    inactive either when its lifetime dies, or when the borrowed place is behind a
    pointer, which is overwritten. This may happen, for example, in the following
    situation:
    {v
            let mut x : &mut i32 = ....;
            let mut b : &mut i32 = &mut * x;  // Creating a borrow of *x
            x = ...;   // We overwrite x. The borrow created above is no longer active,
                       // because x refers to another memory location
            *x = 1;    // Thus, we can access x in writing
    v}

    This module contains an analysis which computes this information. *)

type bor
(** The type of borrows. *)

module BSet : Set.S with type elt = bor

type bor_info = { blft : lifetime; bmut : mut; bplace : place }
(** Information about borrows: their lifetime, mutability, and the place they are
    borrowing. *)

val get_bor_info : Ast.program -> mir_body -> bor -> bor_info
(** Getter for [bor_info] values, given the body of a Mir function, and a borrow id. *)

type analysis_results = label -> BSet.t
(** The result of the analysis is a function which, given a label, returns the set of
    active borrows at that label. *)

val go : Ast.program -> (lifetime -> PpSet.t) -> mir_body -> analysis_results
(** Does the analysis, given lifetimes sets. Applying this function is costly, so it is
    better to call it once, and then use the analysis result as many times as needed. *)
