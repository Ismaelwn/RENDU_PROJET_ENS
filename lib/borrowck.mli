(** This module performs the borrow checking. *)

val borrowck : Ast.program -> Minimir.mir_body -> unit
