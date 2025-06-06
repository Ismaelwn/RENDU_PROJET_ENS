open Type
open Ast

let rec erase_typ = function
  | Tborrow (_, mut, typ) -> Tborrow ((), mut, erase_typ typ)
  | Tstruct (id, _) -> Tstruct (id, [])
  | (Ti32 | Tbool | Tunit) as typ -> typ

let check_lfts loc lfts =
  let used_lfts = Hashtbl.create 5 in
  List.iter
    (fun lft ->
      if Hashtbl.mem used_lfts lft then
        Error.error loc "Multiply declared lifetime parameter: %s" (string_of_lft lft);
      Hashtbl.add used_lfts lft false)
    lfts;
  used_lfts

let check_unused_lfts loc used_lfts where =
  Hashtbl.iter
    (fun lft used ->
      if not used then
        Error.error loc "Lifetime parameter %s is not used in %s." (string_of_lft lft)
          where)
    used_lfts

let check_typ prog loc check_lvar_num visit_lvar typ =
  let rec aux = function
    | Tbool | Ti32 | Tunit -> ()
    | Tborrow (lft, _, typ) ->
        visit_lvar lft;
        aux typ
    | Tstruct (id, lfts) ->
    match Hashtbl.find prog id with
    | exception Not_found -> Error.error loc "Unbound type constructor %s." id
    | Dfundef _ ->
        Error.error loc "Identifier %s refers to a function, expected a type." id
    | Dstruct s ->
        if check_lvar_num && List.length s.slfts <> List.length lfts then
          Error.error loc
            "Type constructor %s does not have the right number of lifetime parameters."
            id;
        List.iter visit_lvar lfts
  in
  aux typ

let check_typ_in_decl prog loc used_lfts typ =
  check_typ prog loc true
    (fun lft ->
      if not (Hashtbl.mem used_lfts lft) then
        Error.error loc "Unbound lifetime %s." (string_of_lft lft);
      Hashtbl.replace used_lfts lft true)
    typ

let check_struct_decl prog used_lfts struc =
  let field_names = Hashtbl.create 5 in
  List.iter
    (fun (id, typ) ->
      if Hashtbl.mem field_names id.id then
        Error.error id.iloc "Several fields have name %s" id.id;
      Hashtbl.add field_names id.id ();
      check_typ_in_decl prog struc.sloc used_lfts typ;
      if struc.scopy && not (typ_is_copy prog typ) then
        Error.error struc.sloc
          "This struct is marked as being Copy, but its field %s is not." id.id)
    struc.sfields;
  check_unused_lfts struc.sloc used_lfts "this struct declaration"

let check_fun_decl prog used_lfts fd =
  let param_names = Hashtbl.create 5 in
  List.iter
    (fun (param, _, typ) ->
      if Hashtbl.mem param_names param.id then
        Error.error param.iloc "Several parameters have name %s" param.id;
      Hashtbl.add param_names param.id ();
      check_typ_in_decl prog fd.floc used_lfts typ)
    fd.fformals;
  check_typ_in_decl prog fd.floc used_lfts fd.freturn;
  check_unused_lfts fd.floc used_lfts "this functions declaration";
  List.iter
    (fun (l1, l2) ->
      if not (Hashtbl.mem used_lfts l1) then
        Error.error fd.floc "Unbound lifetime %s." (string_of_lft l1);
      if not (Hashtbl.mem used_lfts l2) then
        Error.error fd.floc "Unbound lifetime %s." (string_of_lft l2))
    fd.foutlives

let check_lifetimes prog =
  Hashtbl.iter
    (fun _ decl ->
      let used_lfts = check_lfts (decl_loc decl) (decl_lfts decl) in
      match decl with
      | Dstruct s -> check_struct_decl prog used_lfts s
      | Dfundef f -> check_fun_decl prog used_lfts f)
    prog

module SMap = Map.Make (String)

let unify_ty loc typ1 typ2 =
  if typ1 <> typ2 then
    Error.error loc "This expression has type %s but is expected to have type %s."
      (string_of_erased_typ typ2) (string_of_erased_typ typ1)

let unify_ty_opt loc typ1 typ2 =
  match typ1, typ2 with
  | Some t1, Some t2 ->
      unify_ty loc t1 t2;
      typ1
  | None, _ -> typ2
  | _, None -> typ1

type tenv = { te_locals : (mut * erased_typ) SMap.t; te_has_break : location option ref }

let check_fun_body prog fd =
  let not_an_lval exp_lval expr =
    if Option.is_some exp_lval then
      Error.error expr.eloc "This expression should be an l-value."
  in
  let rec infer env expr =
    match check_infer env None expr with
    | Some typ -> typ
    | None ->
        Error.error expr.eloc
          "Expressions that never return are not allowed at this position."
  and infer_lvalue mut env expr =
    match check_infer env ~exp_lval:(Some mut) None expr with
    | Some typ -> typ
    | None -> assert false (* No lvalue has a non-returning type. *)
  and check env ?(never_allowed = true) expr typ =
    if never_allowed then ignore (check_infer env (Some typ) expr)
    else unify_ty expr.eloc typ (infer env expr)
  and check_infer env ?(exp_lval = None) exp_typ expr =
    let res =
      match expr.edesc with
      | Econst (Ci32 _) ->
          not_an_lval exp_lval expr;
          Some Ti32
      | Econst (Cbool _) ->
          not_an_lval exp_lval expr;
          Some Tbool
      | Eunit ->
          not_an_lval exp_lval expr;
          Some Tunit
      | Evar id -> (
          match SMap.find id.id env.te_locals with
          | mut, ty ->
              if mut = NotMut && exp_lval = Some Mut then
                Error.error expr.eloc "This variable is immutable.";
              Some ty
          | exception Not_found -> Error.error id.iloc "Unbound variable %s." id.id)
      | Edot (e, f) -> (
          let typ = (Option.fold exp_lval ~none:infer ~some:infer_lvalue) env e in
          let exception WrongType in
          try
            match typ with
            | Tstruct (id, _) -> (
                match Hashtbl.find_opt prog id with
                | Some (Dstruct { sfields; _ }) -> (
                    match List.find_opt (fun (id, _) -> id.id = f.id) sfields with
                    | Some (_, typ) -> Some (erase_typ typ)
                    | None ->
                        Error.error expr.eloc "No such field %s in struct %s" f.id id)
                | _ -> raise WrongType)
            | _ -> raise WrongType
          with WrongType ->
            Error.error e.eloc "This expression has type %s, expected a struct."
              (string_of_erased_typ typ))
      | Ebinop ((Badd | Bsub | Bmul | Bdiv | Bmod), e1, e2) ->
          not_an_lval exp_lval expr;
          check env ~never_allowed:false e1 Ti32;
          check env ~never_allowed:false e2 Ti32;
          Some Ti32
      | Ebinop ((Beqeq | Bneq | Blt | Ble | Bgt | Bge), e1, e2) ->
          not_an_lval exp_lval expr;
          check env ~never_allowed:false e1 Ti32;
          check env ~never_allowed:false e2 Ti32;
          Some Tbool
      | Eunop (Uneg, e) ->
          not_an_lval exp_lval expr;
          check env ~never_allowed:false e Ti32;
          Some Ti32
      | Eunop (Unot, e) ->
          not_an_lval exp_lval expr;
          check env e Tbool;
          Some Tbool
      | Ederef e -> (
          let typ = infer env e in
          match typ with
          | Tborrow (_, _, typ) -> Some typ
          | _ ->
              Error.error expr.eloc "Expected a pointer type, got %s."
                (string_of_erased_typ typ))
      | Eborrow (mut, e) ->
          not_an_lval exp_lval expr;
          let typ = infer_lvalue mut env e in
          Some (Tborrow ((), mut, typ))
      | Eand (e1, e2) | Eor (e1, e2) ->
          not_an_lval exp_lval expr;
          check env e1 Tbool;
          check env e2 Tbool;
          Some Tbool
      | Eassign (e1, e2) ->
          not_an_lval exp_lval expr;
          let typ = infer_lvalue Mut env e1 in
          check env e2 typ;
          Some Tunit
      | Econstr_stru (stru, fields) -> (
          not_an_lval exp_lval expr;
          match Hashtbl.find_opt prog stru.id with
          | Some (Dstruct { sfields; _ }) ->
              let our_fields = List.map (fun (f, _) -> f.id) fields in
              let their_fields = List.map (fun (f, _) -> f.id) sfields in
              if List.sort compare our_fields <> List.sort compare their_fields then
                Error.error expr.eloc
                  "This struct constructor does not have the right set of fields.";
              List.iter
                (fun (f, e) ->
                  let _, their_typ = List.find (fun (tf, _) -> tf.id = f.id) sfields in
                  let their_typ = erase_typ their_typ in
                  unify_ty e.eloc their_typ (infer env e))
                fields;
              Some (Tstruct (stru.id, []))
          | _ -> Error.error stru.iloc "This is not a struct identifier.")
      | Ecall (f, params) -> (
          not_an_lval exp_lval expr;
          match Hashtbl.find_opt prog f.id with
          | Some (Dfundef { fformals; freturn; _ }) ->
              if List.length fformals <> List.length params then
                Error.error expr.eloc
                  "This function call does not have the right number of parameters.";
              List.iter2
                (fun (_, _, their_typ) param ->
                  let their_typ = erase_typ their_typ in
                  unify_ty param.eloc their_typ (infer env param))
                fformals params;
              Some (erase_typ freturn)
          | _ -> Error.error f.iloc "This is not a function.")
      | Eif (c, e1, e2) ->
          not_an_lval exp_lval expr;
          check env c Tbool;
          unify_ty_opt e2.eloc (check_infer env exp_typ e1) (check_infer env exp_typ e2)
      | Eloop e ->
          not_an_lval exp_lval expr;
          let te_has_break = ref None in
          check { env with te_has_break } e Tunit;
          if !te_has_break = None then None else Some Tunit
      | Ewhile (c, e) ->
          not_an_lval exp_lval expr;
          let te_has_break = ref None in
          check { env with te_has_break } c Tbool;
          (match !te_has_break with
          | None -> ()
          | Some loc ->
              Error.error loc "Break statements are forbidden in while loop conditions.");
          check { env with te_has_break = ref None } e Tunit;
          Some Tunit
      | Ereturn None ->
          not_an_lval exp_lval expr;
          if fd.freturn <> Tunit then
            Error.error expr.eloc
              "A return statement without a parameter assumes the function returns ().";
          None
      | Ereturn (Some e) ->
          not_an_lval exp_lval expr;
          check env e (erase_typ fd.freturn);
          None
      | Ebreak ->
          not_an_lval exp_lval expr;
          env.te_has_break := Some expr.eloc;
          None
      | Elet (x, mut, typ, e, b) ->
          not_an_lval exp_lval expr;
          check_typ prog expr.eloc false (fun () -> ()) typ;
          (match e with Some e -> check env e typ | None -> ());
          let env = { env with te_locals = SMap.add x.id (mut, typ) env.te_locals } in
          check_block env exp_typ b
      | Eblock b ->
          not_an_lval exp_lval expr;
          check_block env exp_typ b
    in
    expr.etyp <- unify_ty_opt expr.eloc exp_typ res;
    expr.etyp
  and check_block env exp_typ (el, e) =
    List.iter (fun e -> ignore (check_infer env None e)) el;
    check_infer env exp_typ e
  in

  let te_locals =
    List.fold_left
      (fun env (id, mut, typ) -> SMap.add id.id (mut, erase_typ typ) env)
      SMap.empty fd.fformals
  in
  let env = { te_locals; te_has_break = ref None } in
  check env fd.fbody (erase_typ fd.freturn);
  match !(env.te_has_break) with
  | Some loc -> Error.error loc "This break statement does not belong to a function."
  | None -> ()

let check_types prog =
  Hashtbl.iter
    (fun _ decl -> match decl with Dfundef f -> check_fun_body prog f | _ -> ())
    prog

let go prog =
  check_lifetimes prog;
  check_types prog;
  ()
