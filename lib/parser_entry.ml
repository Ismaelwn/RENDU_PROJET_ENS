open Ast

let parse_lexbuf lexbuf =
  let decls =
    try Parser.prog Lexer.token lexbuf
    with Parser.Error ->
      let startp = Lexing.lexeme_start_p lexbuf and endp = Lexing.lexeme_end_p lexbuf in
      Error.error (startp, endp) "Syntax error." in
  let program = Hashtbl.create 17 in
  let add id decl =
    if Hashtbl.mem program id.id then
      Error.error id.iloc "This identifier is already defined.";
    Hashtbl.add program id.id decl
  in
  List.iter (fun decl -> add (decl_name decl) decl) decls;
  program

let parse_file filename =
  let _, lexbuf = MenhirLib.LexerUtil.read filename in
  parse_lexbuf lexbuf

let parse_string s =
  parse_lexbuf (Lexing.from_string s)
