open Minimir

(** This module contains the {i liveness} static analysis, used by the borrow checker. A
    local variable is {i live} if the value it contains may be used in the future. *)

type analysis_results = label -> LocSet.t
(** The type of the result of the analysis. *)

val go : Minimir.mir_body -> analysis_results
(** Perform the analysis, given the body of a MIR function. Performing this analysis is
    costly, but querying its results is not. Hence, this function should be applied
    partially with only one parameter once per function, and, then, its result can be
    applied as many times as needed. *)
