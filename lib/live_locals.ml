open Minimir
module Fix = Fix.Fix.ForType (struct type t = int end) (Fix.Prop.Set (LocSet))

type analysis_results = label -> LocSet.t

let add_place pl live =
  LocSet.add (local_of_place pl) live

let go mir : analysis_results =
  Fix.lfp (fun lbl live ->
      match fst mir.minstrs.(lbl) with
      | Iassign (pl, rv, next) -> (
          let live = live next in
          let live = match pl with PlLocal l -> LocSet.remove l live | _ -> live in
          let live =
            if contains_deref_borrow pl then add_place pl live else live
          in
          match rv with
          | RVplace pl | RVborrow (_, pl) -> add_place pl live
          | RVconst _ | RVunit -> live
          | RVbinop (_, pl1, l2) -> add_place pl1 live |> add_place l2
          | RVunop (_, pl) -> add_place pl live
          | RVmake (_, pls) -> List.fold_left (fun live pl -> add_place pl live) live pls)
      | Ideinit (l, next) ->
          let live = live next in
          LocSet.remove l live
      | Igoto next -> live next
      | Iif (c, lt, lf) -> add_place c (LocSet.union (live lt) (live lf))
      | Ireturn -> LocSet.singleton Lret
      | Icall (_, pls, pl, next) ->
          let live = live next in
          let live = match pl with PlLocal l -> LocSet.remove l live | _ -> live in
          List.fold_left (fun live pl -> add_place pl live) live pls)
