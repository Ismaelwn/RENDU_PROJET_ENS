
{
  open Lexing
  open Ast
  open Parser

  let id_or_keyword =
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      ["if", IF; "else", ELSE;
       "while", WHILE; "loop", LOOP; "break", BREAK; "return", RETURN;
       "true", CONSTANT (Cbool true); "false", CONSTANT (Cbool false);
       "let", LET; "fn", FN; "mut", MUT;
       "struct", STRUCT; "where", WHERE;
       "i32", I32; "bool", BOOL;
      ];
    fun s ->
      try Hashtbl.find h s with Not_found -> IDENT s

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = alpha (alpha | digit | '_')*
let integer = ['0'-'9']+
let space = [' ' '\t']

rule token = parse
  | '\n'                         { newline lexbuf; token lexbuf }
  | space+                       { token lexbuf }
  | ident as id                  { id_or_keyword id }
  | '+'                          { PLUS }
  | '-'                          { MINUS }
  | '*'                          { STAR }
  | '/'                          { DIV }
  | '%'                          { PERCENT }
  | '&'                          { AMP }
  | '='                          { EQ }
  | "=="                         { EQEQ }
  | "!="                         { NEQ }
  | '<'                          { LT }
  | "<="                         { LE }
  | '>'                          { GT }
  | ">="                         { GE }
  | '('                          { LPAREN }
  | ')'                          { RPAREN }
  | '{'                          { LBRA }
  | '}'                          { RBRA }
  | '.'                          { DOT }
  | ','                          { COMMA }
  | ':'                          { COLON }
  | ";"                          { SEMICOLON }
  | "&&"                         { AMPAMP }
  | "||"                         { BARBAR }
  | '!'                          { NOT }
  | "->"                         { ARROW }
  | (integer "i32") as s         { CONSTANT (Ci32 s) }
  | "'" ident as id              { LIFETIME id }
  | "#[derive(Copy, Clone)]"     { DERIVECOPY }
  | "//" [^ '\n']* ('\n' | eof)  { newline lexbuf; token lexbuf }
  | "/*"                         { comment lexbuf.lex_curr_p lexbuf; token lexbuf }
  | eof                          { EOF }
  | integer
    { Error.error (lexbuf.lex_start_p, lexbuf.lex_curr_p) "Integers should be suffixed with 'i32' in MiniRust." }
  | _
    { Error.error (lexbuf.lex_start_p, lexbuf.lex_curr_p) "Lexing error." }

and comment start = parse
  | "*/" { () }
  | "/*" { comment start lexbuf; comment start lexbuf }
  | '\n' { newline lexbuf; comment start lexbuf }
  | eof  { Error.error (start, lexbuf.lex_start_p) "Unterminated comment." }
  | _    { comment start lexbuf }


