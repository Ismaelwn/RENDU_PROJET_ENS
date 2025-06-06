open Type

(** MiniMir is the intermediate language on which our borrow checker executes. It is
    heavily inspired on Rust's MIR intermediate representation, but heavily simplified.

    MiniMir functions are control flow graphs: each node is an instruction containing the
    label of the next instruction to execute (except for [Ireturn] and [Iif], see below).
*)

(** {1 Type definitions} *)

type label = int
(** Labels of nodes of the control flow graph. *)

(** Local variables are either... *)
type local =
  | Lparam of string  (** function parameters, *)
  | Lvar of int  (** temporaries, which include locals declared by the user, *)
  | Lret  (** or a special local used to return a value from the function. *)

(** Places are "memory access paths", which include... *)
type place =
  | PlLocal of local  (** local variables, *)
  | PlDeref of place  (** dereference of a place (of borrow type), *)
  | PlField of place * string  (** or a field access. *)

(** It is guaranteed that a MiniMir instruction does not refer twice to the same local
    variable.
    Such an instruction can be...*)
type instr =
  | Iassign of place * rvalue * label
      (** an assignment to a place, from an right-value (see below), *)
  | Ideinit of local * label
      (** the deinitialization of a local, which happens when a local goes out of its
          scope, *)
  | Igoto of label  (** jumping to another instruction, *)
  | Iif of place * label * label
      (** branching to one of two instructions, depending on the value of a local, *)
  | Ireturn
      (** returning from the function, using the value of [Lret] as a return value, *)
  | Icall of string * place list * place * label
      (** calling a function, with some parameters, assigning the return value to a place,
          and the jumping to another instruction. *)

(** A right-value, which can be assigned to a place, is either...*)
and rvalue =
  | RVplace of place
      (** copying/moving from another place (copying only if the type is Copy), *)
  | RVconst of Ast.constant  (** a constant, *)
  | RVunit  (** the unit value, *)
  | RVborrow of mut * place  (** creating a new borrow of a place (mutable or shared), *)
  | RVbinop of Ast.binop * place * place  (** performing a binary operation, *)
  | RVunop of Ast.unop * place  (** performing a unary operation, *)
  | RVmake of string * place list  (** constructing a {v struct v} value.*)

type mir_body = {
  mgeneric_lfts : lifetime list;
      (** The generic lifetimes of the function. E.g., if the function prototype starts
          with {v fn f<'a, 'b>(...) v}, then [mgeneric_lfts] contains {v 'a v} and
          {v 'b v}. *)
  moutlives_graph : outlives_graph;
      (** The outlives graph of generic liftimes, as implied by the prototype declaration.
          This graph includes relations explicitely mentionned by the user, but also
          relations implied by the types of the parameters and return values. It is
          reflexively and transitively closed. *)
  mlocals : (local, full_typ) Hashtbl.t;
      (** All the local variables of this MiniMir function body, with their types. This
          includes the function parameters and the [Lret] special local. Types of internal
          locals (i.e., [Lvar _]) are instantiated with as many fresh lifetime variables
          as they have placeholders, *)
  mentry : label;  (** The entry of the control flow graph.*)
  minstrs : (instr * Ast.location) array;
      (** CFG instructions, together with location information in the input file. *)
  mloc : Ast.location;  (** Location information for the whole function. *)
}

(** {1 Functions over places} *)

val local_of_place : place -> local
(** The local at the begining of a place. *)

val typ_of_place : Ast.program -> mir_body -> place -> full_typ
(** Compute the type of a place. *)

val place_mut : Ast.program -> mir_body -> place -> mut
(** Is this place mutable? I.e., does it contain no dereference of a shared borrow? *)

val is_subplace : place -> place -> bool
(** A subplace of a place corresponds to a subset of memory locations. I.e., a subplace
    can be obtained from a place by {b adding} field accesses or dereferences. *)

val is_subplace_no_deref : place -> place -> bool
(** Same as above, but only allowing field accesses. I.e.,
    [is_subplace_no_deref (PlDeref x) x] returns [false], while
    [is_subplace_no_deref (PlField (x, "foo")) x] returns [true] *)

val contains_deref_borrow : place -> bool
(** Does this place contains the dereference of a borrow? *)

(** Sets of locals and places: *)

module LocSet : Set.S with type elt = local
module PlaceSet : Set.S with type elt = place

(** {1 Program points} *)

(** This type is used by the borrow checker: each lifetime is assocated with a set of
    program point, which is either a CFG label, or the end of a generic lifetime in the
    caller's code. *)
type program_point = PpLocal of label | PpInCaller of lifetime

module PpSet : Set.S with type elt = program_point
