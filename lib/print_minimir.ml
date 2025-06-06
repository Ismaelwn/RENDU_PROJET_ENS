open Type
open Minimir
module Fmt = Format

let pp = Fmt.fprintf
let pp_string = Format.pp_print_string
let pp_list_comma pp_item fmt =
  Fmt.pp_print_list ~pp_sep:(fun fmt () -> pp fmt ", ") pp_item fmt
let pp_list_cut pp_item fmt =
  Fmt.pp_print_list ~pp_sep:Fmt.pp_print_cut pp_item fmt

let pp_lifetime fmt : Ast.lifetime -> unit = function
  | Lnamed s -> pp_string fmt s
  | Lanon n -> pp fmt "'_%d" n

let pp_outlives_graph fmt (g: outlives_graph) =
  pp fmt "@[<v>";
  pp_list_cut (fun fmt (lft, lft_set) ->
    pp fmt "@[%a -> %a@]"
      pp_lifetime lft (pp_list_comma pp_lifetime) (LSet.to_list lft_set)
  ) fmt (LMap.to_list g);
  pp fmt "@]"

let pp_local fmt : local -> unit = function
  | Lparam s -> pp fmt "%s" s
  | Lvar n -> pp fmt "_%d" n
  | Lret -> pp fmt "_ret"

let rec pp_typ pp_lft fmt : 'a typ -> unit = function
  | Tstruct (s, lfts) ->
    if List.is_empty lfts then
      pp_string fmt s
    else
      pp fmt "%s<%a>" s (pp_list_comma pp_lft) lfts
  | Tborrow (lft, is_mut, ty) ->
    pp fmt "&%a %s%a"
      pp_lft lft
      (match is_mut with Mut -> "mut " | NotMut -> "")
      (pp_typ pp_lft) ty
  | Tunit ->
    pp_string fmt "()"
  | Ti32 ->
    pp_string fmt "i32"
  | Tbool ->
    pp_string fmt "bool"

let pp_locals fmt (ls: (local, full_typ) Hashtbl.t) =
  pp fmt "@[<v>";
  pp_list_cut (fun fmt (l, ty) ->
    pp fmt "@[%a : %a@]"
      pp_local l (pp_typ pp_lifetime) ty
  ) fmt (List.of_seq @@ Hashtbl.to_seq ls);
  pp fmt "@]"

let pp_label fmt lbl =
  Fmt.fprintf fmt "%d" lbl

let rec pp_place fmt : place -> unit = function
  | PlDeref pl -> pp fmt "*%a" pp_place pl
  | pl -> pp_place1 fmt pl
and pp_place1 fmt : place -> unit = function
  | PlField (pl, s) -> pp fmt "%a.%s" pp_place1 pl s
  | PlLocal l -> pp_local fmt l
  | pl -> pp fmt "(%a)" pp_place pl

let pp_constant fmt : Ast.constant -> unit = function
  | Ci32 s -> pp_string fmt s
  | Cbool b -> Fmt.pp_print_bool fmt b

let string_of_binop : Ast.binop -> string = function
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*"
  | Bdiv -> "/"
  | Bmod -> "mod"
  | Beqeq -> "=="
  | Bneq -> "!="
  | Blt -> "<"
  | Ble -> "<="
  | Bgt -> ">"
  | Bge -> ">="

let string_of_unop : Ast.unop -> string = function
  | Uneg -> "-"
  | Unot -> "not"

let pp_rvalue fmt : rvalue -> unit = function
  | RVplace pl -> pp_place fmt pl
  | RVconst cst -> pp_constant fmt cst
  | RVunit -> pp fmt "()"
  | RVborrow (ismut, pl) ->
    pp fmt "&%s %a" (match ismut with Mut -> "mut" | NotMut -> "")
      pp_place pl
  | RVbinop (op, pl1, pl2) ->
    pp fmt "%a %s %a"
      pp_place pl1 (string_of_binop op) pp_place pl2
  | RVunop (op, pl) ->
    pp fmt "%s %a"
      (string_of_unop op) pp_place pl
  | RVmake (s, pls) ->
    pp fmt "%s(%a)" s (pp_list_comma pp_place) pls

let pp_instr fmt : instr -> unit = function
  | Iassign (pl, rv, lbl) ->
    pp fmt "%a = %a ; -> %a"
      pp_place pl pp_rvalue rv pp_label lbl
  | Ideinit (l, lbl) ->
    pp fmt "deinit %a ; -> %a"
      pp_local l pp_label lbl
  | Igoto lbl ->
    pp fmt "goto %a"
      pp_label lbl
  | Iif (pl, lbl1, lbl2) ->
    pp fmt "if %a -> %a else %a"
      pp_place pl pp_label lbl1 pp_label lbl2
  | Ireturn ->
    pp fmt "return"
  | Icall (fn, pls, pl, lbl) ->
    pp fmt "%a = %s(%a) ; -> %a"
      pp_place pl fn (pp_list_comma pp_place) pls pp_label lbl

let pp_instrs fmt (instrs: (instr * Ast.location) array) =
  pp fmt "@[<v>";
  pp_list_cut (fun fmt (lbl, (instr, _)) ->
    pp fmt "@[%a: %a@]" pp_label lbl pp_instr instr
  ) fmt (List.of_seq @@ Array.to_seqi instrs);
  pp fmt "@]"

let pp_body fmt (body: mir_body) =
  pp fmt "@[<v>";
  if not (List.is_empty body.mgeneric_lfts) then
    pp fmt "@[generic lifetimes:@ %a@]@,"
      (pp_list_comma pp_lifetime) body.mgeneric_lfts;
  if not (LMap.is_empty body.moutlives_graph) then
    pp fmt "@[<v>outlives graph:@,  %a@]@,"
      pp_outlives_graph body.moutlives_graph;
  if Hashtbl.length body.mlocals > 0 then
    pp fmt "@[<v>locals:@,  %a@]@,"
      pp_locals body.mlocals;
  pp fmt "@[entry: %a@]@,"
    pp_label body.mentry;
  pp fmt "@[<v>instrs:@,  %a@]@,"
    pp_instrs body.minstrs;
  pp fmt "@]";
  ()

let print (body: mir_body) =
  pp Format.std_formatter "%a@." pp_body body
