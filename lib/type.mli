(** {1 Type definitions} *)

type lifetime = Ast.lifetime
type mut = Ast.mut = Mut | NotMut

type 'lft typ = 'lft Ast.typ =
  | Tstruct of string * 'lft list
  | Tborrow of 'lft * mut * 'lft typ
  | Tunit
  | Ti32
  | Tbool

and erased_typ = unit typ

and full_typ = lifetime typ
(** The type of types is parameterized over the type of lifetimes :
    - *erased types* do no contain lifetimes, so they are instantiated with unit. They are
      mostly used in the parser and type checker.
    - *full types* are annotated with lifetimes. *)

(** {1 Printing helpers} *)

val string_of_lft : lifetime -> string
val string_of_full_typ : full_typ -> string
val string_of_erased_typ : erased_typ -> string

(** {1 Handling lifetimes} *)

module LMap : Map.S with type key = lifetime
module LSet : Set.S with type elt = lifetime

val fresh_lft : unit -> lifetime

(** {1 Functions over types} *)

val typ_is_copy : Ast.program -> full_typ -> bool
(** Is this type Copy? I.e., can it be copied without being of ownership issues? *)

val free_lfts : full_typ -> LSet.t
(** The set of free lifetimes of a type. *)

(** * Substitutions *)

type subst = lifetime LMap.t
(** A substitution is a mapping over lifetimes. *)

val mk_subst : lifetime list -> lifetime list -> subst
(** [mk_subst formals actuals] create a substitution which replaces the lifetimes in
    [formals] by the lifetimes in [actuals]. *)

val subst_typ : subst -> full_typ -> full_typ
(** Applying a substitution to a type. *)

val fields_types_fresh : Ast.program -> string -> full_typ list * full_typ
(** Given a {v struct v} identifier, instantiate this {v struct v} with fresh lifetime variables, then
    returns the (substituted) type of its fields, and the (substituted) {v struct v} type. *)

val fn_prototype_fresh : Ast.program -> string -> full_typ list * full_typ * (lifetime * lifetime) list
(** Given a function identifier, instantiate its prototype with fresh lifetime variables,
    then returns the (substituted) types of its parameters, its (substituted) return type,
    and the list of its (substituted) outlives constraints. *)

(** * The outlives relation *)

type outlives_graph = LSet.t LMap.t
(** An outlive graph contains a set of outlives relations {v 'a : 'b v} between lifetimes. *)

val add_outlives_edge : lifetime -> lifetime -> outlives_graph -> outlives_graph
(** Adds an edge to a graph. *)

val outlives_union : outlives_graph -> outlives_graph -> outlives_graph
(** Merge two graphs. *)

val implied_outlives : Ast.program -> full_typ -> outlives_graph
(** The graph containing all the outlives relations {i implied} by a type. For
    example, the type {v &'a &'b i32 v} implies the relation {v 'b : 'a v}*)
