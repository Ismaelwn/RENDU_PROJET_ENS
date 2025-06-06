open Lexing

let usage () =
  Printf.eprintf "Usage: minirust <filename>\n";
  exit 1

exception Error of Lexing.position * Lexing.position * string

let error (start, end_) format =
  let start = { start with pos_bol = start.pos_bol - 1 } in
  let end_ = { end_ with pos_bol = end_.pos_bol - 1 } in
  Printf.ksprintf (fun msg -> raise (Error (start, end_, msg)))
    format
