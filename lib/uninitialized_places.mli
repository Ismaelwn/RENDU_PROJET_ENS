open Minimir

(** This modules contains the initializedness analysis for MiniMir. The word
    "initializedness" has to be taken in a broad meaning: when a variable contains a value
    which is not Copy, and its content is consumed by moving its resources, then this
    variable is considered uninitialized, even though it has been initialized earlier in
    the code.

    For example, consider this piece of MiniRust code:
    {v
            struct Box { } // A type which is not Copy

            fn f(mut x : Box) -> Box {
                let mut y : Box = x;
                // x is considered uninitialized at this code point.
                return x // Error: use of uninitialized variable x
            }
    v}

    Hence, this analysis effectively tracks the fact that resources cannot be duplicated.
    For this reason, this analysis is crucial to the borrow checker.

    This analysis determines initializedness at the {b place} level: in MiniRust (and in
    Rust), a place can be partially initialized. For example, consider this piece of
    MiniRust code:
    {v
            struct Box { }
            struct Pair { a : Box, b : Box }

            fn swap_pair(mut p : Pair) -> Pair {
                let mut a : Box = p.a;
                // p.a is uninitialized, but p.b is initialized
                let mut b : Box = p.b;
                // Neither p.a nor p.b are initialized
                p.b = a;
                p.a = b;
                // p and all its descendants are now initialized
                return p;
            }
    v}

    Interestingly, the analysis computes sets of {b un}initialized places rather than sets
    of initialized places. Of course, this is equivalent, because the latter is the
    complement of the former. This is more convenient to compute sets of uninitialized
    places, because this better fits the usual pattern of dataflow analyses: after a join
    point, we consider conservatively that the set of uninitialized places is the
    {b union} of the set of uninitialized places of all the predecessors.

    At function entry, all the places are uninitialized, execpt subplaces of the
    parameters. A place becomes uninitialized
    - when it is a local on which the [Ideinit] instruction is executed, or
    - when it has a non-Copy type, and its value is moved,
    - when a larger place becomes uninitialized.

    Conversely, a place becomes initiliazed (i.e., it no longer belongs to the
    uninitialized set) when it is assigned to, or when a larger place is assigned to.

    Enumerating all the places could be non-terminating in the case of recursive data
    structures. (MiniRust cannot have recursive data structures because it does not have
    sum types, but in Rust they exist, of course.) In order to avoid this source of
    non-termination, this analysis only considers the places that actually appear in the
    MiniMir code. *)

type analysis_results = label -> PlaceSet.t
(** The result of the analysis is a function which, given a label, returns the set of
    uninitialized places at that label. *)

val go : Ast.program -> mir_body -> analysis_results
(** Do the analysis. Applying this function is costly, so it is better to call it once,
    and then use the analysis result as many times as needed. *)
