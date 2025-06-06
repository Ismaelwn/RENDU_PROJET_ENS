
(* The type of tokens. *)

type token = 
  | WHILE
  | WHERE
  | STRUCT
  | STAR
  | SEMICOLON
  | RPAREN
  | RETURN
  | RBRA
  | PLUS
  | PERCENT
  | NOT
  | NEQ
  | MUT
  | MINUS
  | LT
  | LPAREN
  | LOOP
  | LIFETIME of (string)
  | LET
  | LE
  | LBRA
  | IF
  | IDENT of (string)
  | I32
  | GT
  | GE
  | FN
  | EQEQ
  | EQ
  | EOF
  | ELSE
  | DUMMY
  | DOT
  | DIV
  | DERIVECOPY
  | CONSTANT of (Ast.constant)
  | COMMA
  | COLON
  | BREAK
  | BOOL
  | BARBAR
  | ARROW
  | AMPAMP
  | AMP

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.decl list)
