open Ast

type mut = Ast.mut = Mut | NotMut
type lifetime = Ast.lifetime

type 'lft typ = 'lft Ast.typ =
  | Tstruct of string * 'lft list
  | Tborrow of 'lft * mut * 'lft typ
  | Tunit
  | Ti32
  | Tbool

type erased_typ = Ast.erased_typ
type full_typ = Ast.full_typ

let string_of_lft = function Lnamed l -> l | Lanon n -> Printf.sprintf "'%d" n

let string_of_typ string_of_lft typ =
  let buf = Buffer.create 100 in
  let rec aux = function
    | Tborrow (lft, mut, typ) ->
        Buffer.add_string buf "&";
        let lft = string_of_lft lft in
        Buffer.add_string buf lft;
        if lft <> "" then Buffer.add_char buf ' ';
        if mut = Mut then Buffer.add_string buf "mut ";
        aux typ
    | Tstruct (id, lfts) ->
        Buffer.add_string buf id;
        let fst = ref true in
        List.iter
          (fun lft ->
            if !fst then Buffer.add_string buf "<" else Buffer.add_string buf ", ";
            Buffer.add_string buf (string_of_lft lft);
            fst := false)
          lfts;
        if not !fst then Buffer.add_char buf '>'
    | Ti32 -> Buffer.add_string buf "i32"
    | Tbool -> Buffer.add_string buf "bool"
    | Tunit -> Buffer.add_string buf "()"
  in
  aux typ;
  Buffer.contents buf

let string_of_full_typ typ = string_of_typ string_of_lft typ
let string_of_erased_typ typ = string_of_typ (fun _ -> "") typ

module LMap = Map.Make (struct
  type t = lifetime

  let compare = compare
end)

module LSet = Set.Make (struct
  type t = lifetime

  let compare = compare
end)

let fresh_lft =
  let cnt = ref (-1) in
  fun () ->
    incr cnt;
    Lanon !cnt

type subst = lifetime LMap.t

let mk_subst formal_lfts actual_lfts =
  List.fold_left2
    (fun lsubst id lft -> LMap.add id lft lsubst)
    LMap.empty formal_lfts actual_lfts

let subst_typ subst typ =
  let lsubst lft = LMap.find lft subst in
  let rec aux = function
    | Tborrow (lft, mut, typ) -> Tborrow (lsubst lft, mut, aux typ)
    | (Tunit | Ti32 | Tbool) as typ -> typ
    | Tstruct (id, lfts) -> Tstruct (id, List.map lsubst lfts)
  in
  aux typ

let subst_fields_types prog sid lfts =
  let sd = get_struct_def prog sid in
  let subst = mk_subst sd.slfts lfts in
  List.map (fun (_, typ) -> subst_typ subst typ) sd.sfields

let fields_types_fresh prog sid =
  let lfts = List.map (fun _ -> fresh_lft ()) (get_struct_def prog sid).slfts in
  subst_fields_types prog sid lfts, Tstruct (sid, lfts)

let fn_prototype_fresh prog fid =
  let fd = get_fun_def prog fid in
  let lfts = List.map (fun _ -> fresh_lft ()) fd.flfts in
  let subst = mk_subst fd.flfts lfts in
  ( List.map (fun (_, _, typ) -> subst_typ subst typ) fd.fformals,
    subst_typ subst fd.freturn,
    List.map (fun (lft1, lft2) -> LMap.find lft1 subst, LMap.find lft2 subst) fd.foutlives
  )

let typ_is_copy prog = function
  | Tbool | Ti32 | Tunit | Tborrow (_, NotMut, _) -> true
  | Tborrow (_, Mut, _) -> false
  | Tstruct (id, _) -> (get_struct_def prog id).scopy

let free_lfts typ =
  let rec aux acc = function
    | Ti32 | Tbool | Tunit -> acc
    | Tstruct (_, lfts) -> LSet.add_seq (List.to_seq lfts) acc
    | Tborrow (lft, _, typ) -> aux (LSet.add lft acc) typ
  in
  aux LSet.empty typ

type outlives_graph = LSet.t LMap.t

let add_outlives_edge l1 l2 g =
  LMap.update l1 (fun s -> Some (LSet.add l2 (Option.value s ~default:LSet.empty))) g

let implied_outlives prog typ =
  let seen = Hashtbl.create 5 in
  let rec aux acc = function
    | Ti32 | Tbool | Tunit -> acc
    | Tborrow (lft2, _, typ) ->
        let acc =
          LSet.fold (fun lft1 acc -> add_outlives_edge lft1 lft2 acc) (free_lfts typ) acc
        in
        aux acc typ
    | Tstruct (id, lfts) ->
        if not (Hashtbl.mem seen (id, lfts)) then (
          Hashtbl.add seen (id, lfts) ();
          let fields_typs = subst_fields_types prog id lfts in
          List.fold_left aux acc fields_typs)
        else acc
  in
  aux LMap.empty typ

let outlives_union bnd1 bnd2 =
  LMap.union (fun _ s1 s2 -> Some (LSet.union s1 s2)) bnd1 bnd2
