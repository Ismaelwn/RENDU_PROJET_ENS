(** This module defines the types of the abstract syntax tree of the input program,
    together with some some utility functions on these types. *)

(******* Locations, identifiers *******)

type location = Lexing.position * Lexing.position
type ident = { iloc : location; id : string }

val dummy_loc : location

(******* Types and lifetimes ******)

type mut = Mut | NotMut
type lifetime = Lnamed of string | Lanon of int

type 'lft typ =
  | Tstruct of string * 'lft list
  | Tborrow of 'lft * mut * 'lft typ
  | Tunit
  | Ti32
  | Tbool

and full_typ = lifetime typ
and erased_typ = unit typ

(******* Expressions *******)

type unop = Uneg | Unot
type binop = Badd | Bsub | Bmul | Bdiv | Bmod | Beqeq | Bneq | Blt | Ble | Bgt | Bge
type constant = Ci32 of string | Cbool of bool

type expr = { edesc : expr_desc; eloc : location; mutable etyp : erased_typ option }

and expr_desc =
  | Econst of constant  (** 1i32, true, false*)
  | Eunit (* () *)
  | Evar of ident (* x *)
  | Ederef of expr (* *e *)
  | Eassign of expr * expr (* e=e *)
  | Eborrow of mut * expr (* &e, &mut e *)
  | Ebinop of binop * expr * expr  (** e+e, e/e, e<e, e<=e, ... *)
  | Eunop of unop * expr (* !e, -e *)
  | Eand of expr * expr (* e && e *)
  | Eor of expr * expr (* e || e  *)
  | Econstr_stru of ident * (ident * expr) list (* S { ... } (struct constructor) *)
  | Edot of expr * ident (* e.f *)
  | Ecall of ident * expr list (* f(...) (function call) *)
  | Eif of expr * expr * expr (* if e { e } else { e } *)
  | Eloop of expr (* loop { e } *)
  | Ewhile of expr * expr (* while e { e } *)
  | Ereturn of expr option (* return e, return *)
  | Ebreak (* break *)
  | Elet of ident * mut * erased_typ * expr option * block (* let mut? x : T = e in e *)
  | Eblock of block (* { e; e; e; ... e }*)

and block = expr list * expr

(******* Declarations *******)

type struct_decl = {
  sname : ident;
  slfts : lifetime list;
  sfields : (ident * full_typ) list;
  scopy : bool;
  sloc : location;
}

type fun_decl = {
  fname : ident;
  flfts : lifetime list;
  fformals : (ident * mut * full_typ) list;
  freturn : full_typ;
  foutlives : (lifetime * lifetime) list;
  fbody : expr;
  floc : location;
}

type decl = Dstruct of struct_decl | Dfundef of fun_decl
type program = (string, decl) Hashtbl.t

(******* Accessors *******)

val decl_name : decl -> ident
val decl_lfts : decl -> lifetime list
val decl_loc : decl -> location
val get_struct_def : program -> string -> struct_decl
val get_fun_def : program -> string -> fun_decl
