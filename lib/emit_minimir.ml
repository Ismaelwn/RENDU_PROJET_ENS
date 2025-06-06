open Type
open Ast
open Minimir
module SMap = Map.Make (String)

type env = { locals : local SMap.t; brk : label Lazy.t }

let saturate_outlives ol =
  (* Floyd-Warshall algorithm. *)
  LMap.fold
    (fun b _ acc ->
      LMap.fold
        (fun a _ acc ->
          if LSet.mem b (LMap.find a acc) then
            LSet.fold (fun c acc -> add_outlives_edge a c acc) (LMap.find b acc) acc
          else acc)
        acc acc)
    ol ol

let all_outlives_fn prog f =
  let res =
    List.fold_left (fun acc lft -> add_outlives_edge lft lft acc) LMap.empty f.flfts
  in
  let res =
    List.fold_left
      (fun acc (_, _, typ) -> outlives_union acc (implied_outlives prog typ))
      res f.fformals
  in
  let res = outlives_union res (implied_outlives prog f.freturn) in
  let res =
    List.fold_left (fun acc (l1, l2) -> add_outlives_edge l1 l2 acc) res f.foutlives
  in
  saturate_outlives res

let rec freshen_lfts prog = function
  | (Tbool | Ti32 | Tunit) as typ -> typ
  | Tborrow (_, mut, typ) -> Tborrow (fresh_lft (), mut, freshen_lfts prog typ)
  | Tstruct (id, _) ->
      Tstruct (id, List.map (fun _ -> fresh_lft ()) (get_struct_def prog id).slfts)

exception NotAPlace

let rec pl_of_expr env e =
  match e.edesc with
  | Evar x -> PlLocal (SMap.find x.id env.locals)
  | Edot (e, f) -> PlField (pl_of_expr env e, f.id)
  | Ederef e -> PlDeref (pl_of_expr env e)
  | _ -> raise NotAPlace

let rec locs_uniq = function
  | [] -> true
  | l :: locs -> (not (List.mem l locs)) && locs_uniq locs

let emit_fun prog fd =
  let mlocals = Hashtbl.create 7 in
  List.iter (fun (id, _, typ) -> Hashtbl.add mlocals (Lparam id.id) typ) fd.fformals;
  Hashtbl.add mlocals Lret fd.freturn;

  let instrs = Queue.create () in
  let fresh_instr_ref () =
    let id = Queue.length instrs in
    let r = ref None in
    Queue.push r instrs;
    id, r
  in
  let emit loc instr =
    let id, r = fresh_instr_ref () in
    r := Some (instr, loc);
    id
  in

  let cnt_locals = ref 0 in
  let scoped_var env loc typ next =
    incr cnt_locals;
    let l = Lvar !cnt_locals in
    Hashtbl.add mlocals l (freshen_lfts prog typ);
    let env = { env with brk = lazy (emit loc @@ Ideinit (l, Lazy.force env.brk)) } in
    env, emit loc @@ Ideinit (l, next), l
  in

  let rec translate_lval env expr next =
    match expr.edesc with
    | Evar x -> env, next, (fun next -> next), PlLocal (SMap.find x.id env.locals)
    | Edot (e, f) ->
        let env, next, k, pl = translate_lval env e next in
        env, next, k, PlField (pl, f.id)
    | Ederef e ->
        let env, next, k, pl = translate_lval env e next in
        env, next, k, PlDeref pl
    | _ ->
        let env, next, tmp = scoped_var env expr.eloc (Option.get expr.etyp) next in
        let pl = PlLocal tmp in
        env, next, (fun next -> translate_expr env (Some pl) next expr), pl
  and translate_exprs_to_pls env forbid_pls el next =
    let forbid_locs = List.map local_of_place forbid_pls in
    let rec aux env next el =
      let exception NotUnique in
      try
        let pls = List.map (pl_of_expr env) el in
        if not (locs_uniq (List.map local_of_place pls @ forbid_locs)) then
          raise NotUnique;
        env, next, Fun.id, pls
      with NotUnique | NotAPlace -> (
        match el with
        | [] -> assert false
        | e :: el ->
            let env_end, next, tmp = scoped_var env e.eloc (Option.get e.etyp) next in
            let env_end, next, k2, pls = aux env_end next el in
            let k next = translate_expr env (Some (PlLocal tmp)) (k2 next) e in
            env_end, next, k, PlLocal tmp :: pls)
    in
    aux env next el
  and translate_expr env dest next expr =
    let emit = emit expr.eloc in
    let get_dest () =
      match dest, expr.etyp with
      | None, Some typ ->
          let _, next, l = scoped_var env expr.eloc typ next in
          next, PlLocal l
      | Some x, _ -> next, x
      | None, None -> assert false
    in
    let return_unit () =
      match dest with Some dest -> emit @@ Iassign (dest, RVunit, next) | None -> next
    in
    match expr.edesc with
    | Evar _ | Edot _ | Ederef _ ->
        let next, dest = get_dest () in
        let _, next, k, pl = translate_lval env expr next in
        k @@ emit @@ Iassign (dest, RVplace pl, next)
    | Econst cst ->
        let next, dest = get_dest () in
        emit @@ Iassign (dest, RVconst cst, next)
    | Eunit -> return_unit ()
    | Eborrow (mut, e) ->
        let next, dest = get_dest () in
        let env, next, k, pl = translate_lval env e next in
        if local_of_place pl = local_of_place dest then
          let _, next, tmp = scoped_var env expr.eloc (Option.get expr.etyp) next in
          let next = emit @@ Iassign (dest, RVplace (PlLocal tmp), next) in
          k @@ emit @@ Iassign (PlLocal tmp, RVborrow (mut, pl), next)
        else k @@ emit @@ Iassign (dest, RVborrow (mut, pl), next)
    | Ebinop (op, e1, e2) ->
        let next, dest = get_dest () in
        let _, next, k, pls = translate_exprs_to_pls env [ dest ] [ e1; e2 ] next in
        k @@ emit @@ Iassign (dest, RVbinop (op, List.hd pls, List.nth pls 1), next)
    | Eunop (op, e) ->
        let next, dest = get_dest () in
        let _, next, k, pls = translate_exprs_to_pls env [ dest ] [ e ] next in
        k @@ emit @@ Iassign (dest, RVunop (op, List.hd pls), next)
    | Eand (e1, e2) ->
        let next, dest = get_dest () in
        let env, next, k, pls = translate_exprs_to_pls env [] [ e1 ] next in
        let mid = translate_expr env (Some dest) next e2 in
        let shortcut = emit @@ Iassign (dest, RVconst (Cbool false), next) in
        k @@ emit @@ Iif (List.hd pls, mid, shortcut)
    | Eor (e1, e2) ->
        let next, dest = get_dest () in
        let env, next, k, pls = translate_exprs_to_pls env [] [ e1 ] next in
        let mid = translate_expr env (Some dest) next e2 in
        let shortcut = emit @@ Iassign (dest, RVconst (Cbool true), next) in
        k @@ emit @@ Iif (List.hd pls, shortcut, mid)
    | Eassign (e1, e2) -> (
        let next = return_unit () in
        match pl_of_expr env e1 with
        | pl -> translate_expr env (Some pl) next e2
        | exception NotAPlace ->
            let env_e1, next, tmp = scoped_var env expr.eloc (Option.get e2.etyp) next in
            let _, next, k, pl = translate_lval env_e1 e1 next in
            let next = k @@ emit @@ Iassign (pl, RVplace (PlLocal tmp), next) in
            translate_expr env (Some (PlLocal tmp)) next e2)
    | Econstr_stru (id, flds) ->
        let next, dest = get_dest () in
        let _, next, k, pls = translate_exprs_to_pls env [ dest ] (List.map snd flds) next in
        let idpls = List.map2 (fun (id, _) pl -> id.id, pl) flds pls in
        let fields_def = (get_struct_def prog id.id).sfields in
        let pls = List.map (fun (id, _) -> List.assoc id.id idpls) fields_def in
        k @@ emit @@ Iassign (dest, RVmake (id.id, pls), next)
    | Ecall (id, params) ->
        let next, dest = get_dest () in
        let _, next, k, pls = translate_exprs_to_pls env [ dest ] params next in
        k @@ emit @@ Icall (id.id, pls, dest, next)
    | Eif (c, e1, e2) ->
        let env, next, k, pls = translate_exprs_to_pls env [] [ c ] next in
        let ifalse = translate_expr env dest next e2 in
        let itrue = translate_expr env dest next e1 in
        k @@ emit @@ Iif (List.hd pls, itrue, ifalse)
    | Eloop e ->
        let brk = lazy (return_unit ()) in
        let tail, rtail = fresh_instr_ref () in
        let head = translate_expr { env with brk } None tail e in
        rtail := Some (Igoto head, expr.eloc);
        head
    | Ewhile (c, e) ->
        let next = return_unit () in
        let env, brk, k, pls = translate_exprs_to_pls env [] [ c ] next in
        let tail, rtail = fresh_instr_ref () in
        let next = translate_expr { env with brk = lazy brk } None tail e in
        let head = k @@ emit @@ Iif (List.hd pls, next, brk) in
        rtail := Some (Igoto head, expr.eloc);
        head
    | Ereturn None ->
        let next = emit @@ Ireturn in
        emit @@ Iassign (PlLocal Lret, RVunit, next)
    | Ereturn (Some e) ->
        let next = emit @@ Ireturn in
        translate_expr env (Some (PlLocal Lret)) next e
    | Ebreak -> emit @@ Igoto (Lazy.force env.brk)
    | Elet (x, _, typ, e, b) -> (
        let env, next, xl = scoped_var env expr.eloc typ next in
        let env = { env with locals = SMap.add x.id xl env.locals } in
        let next = translate_block env dest next b in
        match e with
        | Some e -> translate_expr env (Some (PlLocal xl)) next e
        | None -> next)
    | Eblock b -> translate_block env dest next b
  and translate_block env dest next (el, e) =
    let next = translate_expr env dest next e in
    List.fold_right (fun ei next -> translate_expr env None next ei) el next
  in

  let env =
    {
      locals =
        List.fold_left
          (fun locals (id, _, _) -> SMap.add id.id (Lparam id.id) locals)
          SMap.empty fd.fformals;
      brk = lazy (assert false);
    }
  in
  let next = emit fd.fbody.eloc @@ Ireturn in
  let mentry = translate_expr env (Some (PlLocal Lret)) next fd.fbody in

  let moutlives_graph = all_outlives_fn prog fd in
  let minstrs = Array.of_seq @@ Seq.map (fun i -> Option.get !i) @@ Queue.to_seq instrs in
  { mgeneric_lfts = fd.flfts; moutlives_graph; mlocals; mentry; minstrs; mloc = fd.floc }

(* Reverse MIR code, because we are building it backwards, which makes it hard to read. *)
let reverse_mir body =
  let revid =
    let n = Array.length body.minstrs - 1 in
    fun id -> n - id
  in
  let mentry = revid body.mentry in
  let trans_instr (instr, loc) =
    match instr with
    | Iassign (pl, rv, id) -> Iassign (pl, rv, revid id), loc
    | Ideinit (l, id) -> Ideinit (l, revid id), loc
    | Igoto id -> Igoto (revid id), loc
    | Iif (c, id1, id2) -> Iif (c, revid id1, revid id2), loc
    | Ireturn -> Ireturn, loc
    | Icall (f, lcls, pl, id) -> Icall (f, lcls, pl, revid id), loc
  in
  let minstrs = Array.of_list @@ List.rev_map trans_instr @@ Array.to_list body.minstrs in
  { body with minstrs; mentry }

let emit_fun prog fd = reverse_mir @@ emit_fun prog fd
