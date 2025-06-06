open Type
open Ast

type label = int
type local = Lparam of string | Lvar of int | Lret
type place = PlLocal of local | PlDeref of place | PlField of place * string

type rvalue =
  | RVplace of place (* Copy or move, depending on the type. *)
  | RVconst of constant
  | RVunit
  | RVborrow of mut * place
  | RVbinop of binop * place * place
  | RVunop of unop * place
  | RVmake of string * place list

type instr =
  | Iassign of place * rvalue * label
  | Ideinit of local * label
  | Igoto of label
  | Iif of place * label * label
  | Ireturn
  | Icall of string * place list * place * label

type mir_body = {
  mgeneric_lfts : lifetime list;
  moutlives_graph : outlives_graph;
  mlocals : (local, full_typ) Hashtbl.t;
  mentry : label;
  minstrs : (instr * location) array;
  mloc : location;
}

let rec local_of_place = function
  | PlLocal l -> l
  | PlDeref pl -> local_of_place pl
  | PlField (pl, _) -> local_of_place pl

let typ_of_place prog mir pl =
  let rec aux = function
    | PlLocal l -> Hashtbl.find mir.mlocals l
    | PlDeref pl -> ( match aux pl with Tborrow (_, _, typ) -> typ | _ -> assert false)
    | PlField (pl, fld) ->
    match aux pl with
    | Tstruct (s, lfts) ->
        let struc = Ast.get_struct_def prog s in
        let typ =
          Option.get
          @@ List.find_map
               (fun (f, ftyp) -> if f.id = fld then Some ftyp else None)
               struc.sfields
        in
        subst_typ (mk_subst struc.slfts lfts) typ
    | _ -> assert false
  in
  aux pl

let place_mut prog mir pl =
  let rec aux = function
    | PlLocal _ -> Mut
    | PlField (pl, _) -> aux pl
    | PlDeref pl ->
    match typ_of_place prog mir pl with
    | Tborrow (_, Mut, _) -> aux pl
    | Tborrow (_, NotMut, _) -> NotMut
    | _ -> assert false
  in
  aux pl

let rec is_subplace pl1 pl2 =
  pl1 = pl2
  ||
  match pl1 with PlLocal _ -> false | PlDeref pl | PlField (pl, _) -> is_subplace pl pl2

let rec is_subplace_no_deref pl1 pl2 =
  pl1 = pl2
  ||
  match pl1 with
  | PlLocal _ | PlDeref _ -> false
  | PlField (pl, _) -> is_subplace_no_deref pl pl2

let rec contains_deref_borrow = function
  | PlLocal _ -> false
  | PlField (pl, _) -> contains_deref_borrow pl
  | PlDeref _ -> true

module LocSet = Set.Make (struct
  type t = local

  let compare = compare
end)

module PlaceSet = Set.Make (struct
  type t = place

  let compare = compare
end)

type program_point = PpLocal of label | PpInCaller of lifetime

module PpSet = Set.Make (struct
  type t = program_point

  let compare = compare
end)
