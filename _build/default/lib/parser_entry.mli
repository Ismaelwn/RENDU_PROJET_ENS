open Ast

(** This module provides is the entry point of the parser. *)

val parse_file : string -> program
(** [parse_file filename] parses the content of the file [filename] into an AST. *)

val parse_string : string -> program
(** [parse_string s] parses the string [s] into an AST. *)
