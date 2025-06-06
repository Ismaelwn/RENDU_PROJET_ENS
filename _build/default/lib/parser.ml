
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
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
    | LIFETIME of (
# 7 "lib/parser.mly"
       (string)
# 32 "lib/parser.ml"
  )
    | LET
    | LE
    | LBRA
    | IF
    | IDENT of (
# 7 "lib/parser.mly"
       (string)
# 41 "lib/parser.ml"
  )
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
    | CONSTANT of (
# 6 "lib/parser.mly"
       (Ast.constant)
# 58 "lib/parser.ml"
  )
    | COMMA
    | COLON
    | BREAK
    | BOOL
    | BARBAR
    | ARROW
    | AMPAMP
    | AMP
  
end

include MenhirBasics

# 2 "lib/parser.mly"
  
  open Ast

# 77 "lib/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_prog) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState001 : (('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_state
    (** State 001.
        Stack shape : FN.
        Start symbol: prog. *)

  | MenhirState003 : ((('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 003.
        Stack shape : FN ident.
        Start symbol: prog. *)

  | MenhirState004 : (('s, _menhir_box_prog) _menhir_cell1_LT, _menhir_box_prog) _menhir_state
    (** State 004.
        Stack shape : LT.
        Start symbol: prog. *)

  | MenhirState007 : (('s, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_state
    (** State 007.
        Stack shape : lifetime.
        Start symbol: prog. *)

  | MenhirState013 : (((('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_state
    (** State 013.
        Stack shape : FN ident generics LPAREN.
        Start symbol: prog. *)

  | MenhirState015 : (('s, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 015.
        Stack shape : mutornot.
        Start symbol: prog. *)

  | MenhirState017 : ((('s, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 017.
        Stack shape : mutornot ident.
        Start symbol: prog. *)

  | MenhirState020 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 020.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState025 : (('s, _menhir_box_prog) _menhir_cell1_AMPAMP _menhir_cell0_DUMMY, _menhir_box_prog) _menhir_state
    (** State 025.
        Stack shape : AMPAMP DUMMY.
        Start symbol: prog. *)

  | MenhirState026 : ((('s, _menhir_box_prog) _menhir_cell1_AMPAMP _menhir_cell0_DUMMY, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 026.
        Stack shape : AMPAMP DUMMY mutornot.
        Start symbol: prog. *)

  | MenhirState027 : (('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_state
    (** State 027.
        Stack shape : AMP.
        Start symbol: prog. *)

  | MenhirState028 : ((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_state
    (** State 028.
        Stack shape : AMP lifetime.
        Start symbol: prog. *)

  | MenhirState029 : (((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 029.
        Stack shape : AMP lifetime mutornot.
        Start symbol: prog. *)

  | MenhirState034 : (('s, _menhir_box_prog) _menhir_cell1_formal, _menhir_box_prog) _menhir_state
    (** State 034.
        Stack shape : formal.
        Start symbol: prog. *)

  | MenhirState038 : ((((('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN, _menhir_box_prog) _menhir_state
    (** State 038.
        Stack shape : FN ident generics LPAREN comma_list(formal) RPAREN.
        Start symbol: prog. *)

  | MenhirState041 : ((((('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN _menhir_cell0_return_type, _menhir_box_prog) _menhir_state
    (** State 041.
        Stack shape : FN ident generics LPAREN comma_list(formal) RPAREN return_type.
        Start symbol: prog. *)

  | MenhirState043 : (('s, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_state
    (** State 043.
        Stack shape : lifetime.
        Start symbol: prog. *)

  | MenhirState045 : ((('s, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_state
    (** State 045.
        Stack shape : lifetime lifetime.
        Start symbol: prog. *)

  | MenhirState048 : ((((('s, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN _menhir_cell0_return_type _menhir_cell0_where_clause, _menhir_box_prog) _menhir_state
    (** State 048.
        Stack shape : FN ident generics LPAREN comma_list(formal) RPAREN return_type where_clause.
        Start symbol: prog. *)

  | MenhirState049 : (('s, _menhir_box_prog) _menhir_cell1_LBRA, _menhir_box_prog) _menhir_state
    (** State 049.
        Stack shape : LBRA.
        Start symbol: prog. *)

  | MenhirState050 : (('s, _menhir_box_prog) _menhir_cell1_WHILE, _menhir_box_prog) _menhir_state
    (** State 050.
        Stack shape : WHILE.
        Start symbol: prog. *)

  | MenhirState051 : (('s, _menhir_box_prog) _menhir_cell1_STAR, _menhir_box_prog) _menhir_state
    (** State 051.
        Stack shape : STAR.
        Start symbol: prog. *)

  | MenhirState052 : (('s, _menhir_box_prog) _menhir_cell1_RETURN, _menhir_box_prog) _menhir_state
    (** State 052.
        Stack shape : RETURN.
        Start symbol: prog. *)

  | MenhirState053 : (('s, _menhir_box_prog) _menhir_cell1_NOT, _menhir_box_prog) _menhir_state
    (** State 053.
        Stack shape : NOT.
        Start symbol: prog. *)

  | MenhirState054 : (('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 054.
        Stack shape : MINUS.
        Start symbol: prog. *)

  | MenhirState055 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 055.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState056 : (('s, _menhir_box_prog) _menhir_cell1_STAR, _menhir_box_prog) _menhir_state
    (** State 056.
        Stack shape : STAR.
        Start symbol: prog. *)

  | MenhirState057 : (('s, _menhir_box_prog) _menhir_cell1_RETURN, _menhir_box_prog) _menhir_state
    (** State 057.
        Stack shape : RETURN.
        Start symbol: prog. *)

  | MenhirState058 : (('s, _menhir_box_prog) _menhir_cell1_NOT, _menhir_box_prog) _menhir_state
    (** State 058.
        Stack shape : NOT.
        Start symbol: prog. *)

  | MenhirState059 : (('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 059.
        Stack shape : MINUS.
        Start symbol: prog. *)

  | MenhirState060 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 060.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState062 : (('s, _menhir_box_prog) _menhir_cell1_LOOP, _menhir_box_prog) _menhir_state
    (** State 062.
        Stack shape : LOOP.
        Start symbol: prog. *)

  | MenhirState064 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 064.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState065 : (('s, _menhir_box_prog) _menhir_cell1_DUMMY, _menhir_box_prog) _menhir_state
    (** State 065.
        Stack shape : DUMMY.
        Start symbol: prog. *)

  | MenhirState068 : ((('s, _menhir_box_prog) _menhir_cell1_DUMMY, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LBRA, _menhir_box_prog) _menhir_state
    (** State 068.
        Stack shape : DUMMY ident LBRA.
        Start symbol: prog. *)

  | MenhirState070 : (('s, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 070.
        Stack shape : ident.
        Start symbol: prog. *)

  | MenhirState073 : (('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_state
    (** State 073.
        Stack shape : AMPAMP.
        Start symbol: prog. *)

  | MenhirState074 : ((('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 074.
        Stack shape : AMPAMP mutornot.
        Start symbol: prog. *)

  | MenhirState075 : (('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_state
    (** State 075.
        Stack shape : AMP.
        Start symbol: prog. *)

  | MenhirState076 : ((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 076.
        Stack shape : AMP mutornot.
        Start symbol: prog. *)

  | MenhirState079 : (('s, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_state
    (** State 079.
        Stack shape : ident LPAREN.
        Start symbol: prog. *)

  | MenhirState085 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_STAR, _menhir_box_prog) _menhir_state
    (** State 085.
        Stack shape : expr_(true_) STAR.
        Start symbol: prog. *)

  | MenhirState087 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 087.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState090 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 090.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState092 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 092.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState094 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 094.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState096 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 096.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState098 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_MINUS, _menhir_box_prog) _menhir_state
    (** State 098.
        Stack shape : expr_(true_) MINUS.
        Start symbol: prog. *)

  | MenhirState100 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 100.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState102 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 102.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState104 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 104.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState106 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 106.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState108 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 108.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState110 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_EQ, _menhir_box_prog) _menhir_state
    (** State 110.
        Stack shape : expr_(true_) EQ.
        Start symbol: prog. *)

  | MenhirState112 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 112.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState114 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_AMPAMP, _menhir_box_prog) _menhir_state
    (** State 114.
        Stack shape : expr_(true_) AMPAMP.
        Start symbol: prog. *)

  | MenhirState116 : (('s, _menhir_box_prog) _menhir_cell1_expr__true__, _menhir_box_prog) _menhir_state
    (** State 116.
        Stack shape : expr_(true_).
        Start symbol: prog. *)

  | MenhirState120 : (('s, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LBRA, _menhir_box_prog) _menhir_state
    (** State 120.
        Stack shape : ident LBRA.
        Start symbol: prog. *)

  | MenhirState122 : (('s, _menhir_box_prog) _menhir_cell1_field, _menhir_box_prog) _menhir_state
    (** State 122.
        Stack shape : field.
        Start symbol: prog. *)

  | MenhirState133 : (('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_state
    (** State 133.
        Stack shape : AMPAMP.
        Start symbol: prog. *)

  | MenhirState134 : ((('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 134.
        Stack shape : AMPAMP mutornot.
        Start symbol: prog. *)

  | MenhirState135 : (('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_state
    (** State 135.
        Stack shape : AMP.
        Start symbol: prog. *)

  | MenhirState136 : ((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 136.
        Stack shape : AMP mutornot.
        Start symbol: prog. *)

  | MenhirState138 : (('s, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_state
    (** State 138.
        Stack shape : ident LPAREN.
        Start symbol: prog. *)

  | MenhirState144 : (((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 144.
        Stack shape : AMP mutornot expr_(false_).
        Start symbol: prog. *)

  | MenhirState145 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_DOT, _menhir_box_prog) _menhir_state
    (** State 145.
        Stack shape : expr_(false_) DOT.
        Start symbol: prog. *)

  | MenhirState147 : (((('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 147.
        Stack shape : AMPAMP mutornot expr_(false_).
        Start symbol: prog. *)

  | MenhirState148 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_STAR, _menhir_box_prog) _menhir_state
    (** State 148.
        Stack shape : expr_(false_) STAR.
        Start symbol: prog. *)

  | MenhirState149 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_STAR, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 149.
        Stack shape : expr_(false_) STAR expr_(false_).
        Start symbol: prog. *)

  | MenhirState150 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PLUS, _menhir_box_prog) _menhir_state
    (** State 150.
        Stack shape : expr_(false_) PLUS.
        Start symbol: prog. *)

  | MenhirState151 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PLUS, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 151.
        Stack shape : expr_(false_) PLUS expr_(false_).
        Start symbol: prog. *)

  | MenhirState152 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PERCENT, _menhir_box_prog) _menhir_state
    (** State 152.
        Stack shape : expr_(false_) PERCENT.
        Start symbol: prog. *)

  | MenhirState153 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PERCENT, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 153.
        Stack shape : expr_(false_) PERCENT expr_(false_).
        Start symbol: prog. *)

  | MenhirState154 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_DIV, _menhir_box_prog) _menhir_state
    (** State 154.
        Stack shape : expr_(false_) DIV.
        Start symbol: prog. *)

  | MenhirState155 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_DIV, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 155.
        Stack shape : expr_(false_) DIV expr_(false_).
        Start symbol: prog. *)

  | MenhirState156 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_NEQ, _menhir_box_prog) _menhir_state
    (** State 156.
        Stack shape : expr_(false_) NEQ.
        Start symbol: prog. *)

  | MenhirState157 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_NEQ, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 157.
        Stack shape : expr_(false_) NEQ expr_(false_).
        Start symbol: prog. *)

  | MenhirState158 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 158.
        Stack shape : expr_(false_) MINUS.
        Start symbol: prog. *)

  | MenhirState159 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 159.
        Stack shape : expr_(false_) MINUS expr_(false_).
        Start symbol: prog. *)

  | MenhirState160 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LT, _menhir_box_prog) _menhir_state
    (** State 160.
        Stack shape : expr_(false_) LT.
        Start symbol: prog. *)

  | MenhirState161 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LT, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 161.
        Stack shape : expr_(false_) LT expr_(false_).
        Start symbol: prog. *)

  | MenhirState162 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LE, _menhir_box_prog) _menhir_state
    (** State 162.
        Stack shape : expr_(false_) LE.
        Start symbol: prog. *)

  | MenhirState163 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LE, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 163.
        Stack shape : expr_(false_) LE expr_(false_).
        Start symbol: prog. *)

  | MenhirState164 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GT, _menhir_box_prog) _menhir_state
    (** State 164.
        Stack shape : expr_(false_) GT.
        Start symbol: prog. *)

  | MenhirState165 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GT, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 165.
        Stack shape : expr_(false_) GT expr_(false_).
        Start symbol: prog. *)

  | MenhirState166 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GE, _menhir_box_prog) _menhir_state
    (** State 166.
        Stack shape : expr_(false_) GE.
        Start symbol: prog. *)

  | MenhirState167 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GE, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 167.
        Stack shape : expr_(false_) GE expr_(false_).
        Start symbol: prog. *)

  | MenhirState168 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQEQ, _menhir_box_prog) _menhir_state
    (** State 168.
        Stack shape : expr_(false_) EQEQ.
        Start symbol: prog. *)

  | MenhirState169 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQEQ, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 169.
        Stack shape : expr_(false_) EQEQ expr_(false_).
        Start symbol: prog. *)

  | MenhirState170 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 170.
        Stack shape : IF expr_(false_).
        Start symbol: prog. *)

  | MenhirState171 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQ, _menhir_box_prog) _menhir_state
    (** State 171.
        Stack shape : expr_(false_) EQ.
        Start symbol: prog. *)

  | MenhirState172 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQ, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 172.
        Stack shape : expr_(false_) EQ expr_(false_).
        Start symbol: prog. *)

  | MenhirState173 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_BARBAR, _menhir_box_prog) _menhir_state
    (** State 173.
        Stack shape : expr_(false_) BARBAR.
        Start symbol: prog. *)

  | MenhirState174 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_BARBAR, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 174.
        Stack shape : expr_(false_) BARBAR expr_(false_).
        Start symbol: prog. *)

  | MenhirState175 : ((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_state
    (** State 175.
        Stack shape : expr_(false_) AMPAMP.
        Start symbol: prog. *)

  | MenhirState176 : (((('s, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 176.
        Stack shape : expr_(false_) AMPAMP expr_(false_).
        Start symbol: prog. *)

  | MenhirState178 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_block_expr _menhir_cell0_ELSE, _menhir_box_prog) _menhir_state
    (** State 178.
        Stack shape : IF expr_(false_) block_expr ELSE.
        Start symbol: prog. *)

  | MenhirState191 : ((('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 191.
        Stack shape : MINUS expr_(false_).
        Start symbol: prog. *)

  | MenhirState192 : ((('s, _menhir_box_prog) _menhir_cell1_NOT, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 192.
        Stack shape : NOT expr_(false_).
        Start symbol: prog. *)

  | MenhirState193 : ((('s, _menhir_box_prog) _menhir_cell1_RETURN, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 193.
        Stack shape : RETURN expr_(false_).
        Start symbol: prog. *)

  | MenhirState194 : ((('s, _menhir_box_prog) _menhir_cell1_STAR, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 194.
        Stack shape : STAR expr_(false_).
        Start symbol: prog. *)

  | MenhirState195 : ((('s, _menhir_box_prog) _menhir_cell1_WHILE, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_state
    (** State 195.
        Stack shape : WHILE expr_(false_).
        Start symbol: prog. *)

  | MenhirState197 : (('s, _menhir_box_prog) _menhir_cell1_SEMICOLON, _menhir_box_prog) _menhir_state
    (** State 197.
        Stack shape : SEMICOLON.
        Start symbol: prog. *)

  | MenhirState198 : (('s, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_state
    (** State 198.
        Stack shape : LET.
        Start symbol: prog. *)

  | MenhirState199 : ((('s, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 199.
        Stack shape : LET mutornot.
        Start symbol: prog. *)

  | MenhirState203 : (((('s, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 203.
        Stack shape : LET mutornot ident.
        Start symbol: prog. *)

  | MenhirState209 : (('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_state
    (** State 209.
        Stack shape : AMPAMP.
        Start symbol: prog. *)

  | MenhirState210 : ((('s, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 210.
        Stack shape : AMPAMP mutornot.
        Start symbol: prog. *)

  | MenhirState211 : (('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_state
    (** State 211.
        Stack shape : AMP.
        Start symbol: prog. *)

  | MenhirState212 : ((('s, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_state
    (** State 212.
        Stack shape : AMP mutornot.
        Start symbol: prog. *)

  | MenhirState216 : ((((('s, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_cell0_EQ, _menhir_box_prog) _menhir_state
    (** State 216.
        Stack shape : LET mutornot ident typ(__anonymous_2,__anonymous_3,__anonymous_4) EQ.
        Start symbol: prog. *)

  | MenhirState219 : ((((('s, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_cell0_option___anonymous_9_ _menhir_cell0_SEMICOLON, _menhir_box_prog) _menhir_state
    (** State 219.
        Stack shape : LET mutornot ident typ(__anonymous_2,__anonymous_3,__anonymous_4) option(__anonymous_9) SEMICOLON.
        Start symbol: prog. *)

  | MenhirState224 : (('s, _menhir_box_prog) _menhir_cell1_expr_without_block_true__ _menhir_cell0_SEMICOLON, _menhir_box_prog) _menhir_state
    (** State 224.
        Stack shape : expr_without_block(true_) SEMICOLON.
        Start symbol: prog. *)

  | MenhirState226 : (('s, _menhir_box_prog) _menhir_cell1_expr_with_block, _menhir_box_prog) _menhir_state
    (** State 226.
        Stack shape : expr_with_block.
        Start symbol: prog. *)

  | MenhirState237 : (('s, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT, _menhir_box_prog) _menhir_state
    (** State 237.
        Stack shape : option(DERIVECOPY) STRUCT.
        Start symbol: prog. *)

  | MenhirState238 : ((('s, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 238.
        Stack shape : option(DERIVECOPY) STRUCT ident.
        Start symbol: prog. *)

  | MenhirState240 : (((('s, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LBRA, _menhir_box_prog) _menhir_state
    (** State 240.
        Stack shape : option(DERIVECOPY) STRUCT ident generics LBRA.
        Start symbol: prog. *)

  | MenhirState242 : (('s, _menhir_box_prog) _menhir_cell1_struct_field, _menhir_box_prog) _menhir_state
    (** State 242.
        Stack shape : struct_field.
        Start symbol: prog. *)

  | MenhirState244 : (('s, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_state
    (** State 244.
        Stack shape : ident.
        Start symbol: prog. *)

  | MenhirState251 : (('s, _menhir_box_prog) _menhir_cell1_decl, _menhir_box_prog) _menhir_state
    (** State 251.
        Stack shape : decl.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_block_expr = 
  | MenhirCell1_block_expr of 's * ('s, 'r) _menhir_state * (Ast.expr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_comma_list_formal_ = 
  | MenhirCell1_comma_list_formal_ of 's * ('s, 'r) _menhir_state * ((Ast.ident * Ast.mut * Ast.full_typ) list)

and ('s, 'r) _menhir_cell1_decl = 
  | MenhirCell1_decl of 's * ('s, 'r) _menhir_state * (Ast.decl)

and ('s, 'r) _menhir_cell1_expr__false__ = 
  | MenhirCell1_expr__false__ of 's * ('s, 'r) _menhir_state * (Ast.expr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_expr__true__ = 
  | MenhirCell1_expr__true__ of 's * ('s, 'r) _menhir_state * (Ast.expr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_expr_with_block = 
  | MenhirCell1_expr_with_block of 's * ('s, 'r) _menhir_state * (Ast.expr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_expr_without_block_true__ = 
  | MenhirCell1_expr_without_block_true__ of 's * ('s, 'r) _menhir_state * (Ast.expr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_field = 
  | MenhirCell1_field of 's * ('s, 'r) _menhir_state * (Ast.ident * Ast.expr)

and ('s, 'r) _menhir_cell1_formal = 
  | MenhirCell1_formal of 's * ('s, 'r) _menhir_state * (Ast.ident * Ast.mut * Ast.full_typ)

and ('s, 'r) _menhir_cell1_generics = 
  | MenhirCell1_generics of 's * ('s, 'r) _menhir_state * (Ast.lifetime list)

and ('s, 'r) _menhir_cell1_ident = 
  | MenhirCell1_ident of 's * ('s, 'r) _menhir_state * (Ast.ident) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_lifetime = 
  | MenhirCell1_lifetime of 's * ('s, 'r) _menhir_state * (Ast.lifetime)

and ('s, 'r) _menhir_cell1_mutornot = 
  | MenhirCell1_mutornot of 's * ('s, 'r) _menhir_state * (Ast.mut)

and ('s, 'r) _menhir_cell1_option_DERIVECOPY_ = 
  | MenhirCell1_option_DERIVECOPY_ of 's * ('s, 'r) _menhir_state * (unit option) * Lexing.position * Lexing.position

and 's _menhir_cell0_option___anonymous_9_ = 
  | MenhirCell0_option___anonymous_9_ of 's * (Ast.expr option)

and 's _menhir_cell0_return_type = 
  | MenhirCell0_return_type of 's * (Ast.lifetime Ast.typ)

and ('s, 'r) _menhir_cell1_struct_field = 
  | MenhirCell1_struct_field of 's * ('s, 'r) _menhir_state * (Ast.ident * Ast.full_typ)

and ('s, 'r) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ = 
  | MenhirCell1_typ___anonymous_2___anonymous_3___anonymous_4_ of 's * ('s, 'r) _menhir_state * (unit Ast.typ)

and 's _menhir_cell0_where_clause = 
  | MenhirCell0_where_clause of 's * ((Ast.lifetime * Ast.lifetime) list)

and ('s, 'r) _menhir_cell1_AMP = 
  | MenhirCell1_AMP of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_AMPAMP = 
  | MenhirCell1_AMPAMP of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_AMPAMP = 
  | MenhirCell0_AMPAMP of 's * Lexing.position

and ('s, 'r) _menhir_cell1_BARBAR = 
  | MenhirCell1_BARBAR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DIV = 
  | MenhirCell1_DIV of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DOT = 
  | MenhirCell1_DOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DUMMY = 
  | MenhirCell1_DUMMY of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_DUMMY = 
  | MenhirCell0_DUMMY of 's * Lexing.position

and 's _menhir_cell0_ELSE = 
  | MenhirCell0_ELSE of 's * Lexing.position

and ('s, 'r) _menhir_cell1_EQ = 
  | MenhirCell1_EQ of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_EQ = 
  | MenhirCell0_EQ of 's * Lexing.position

and ('s, 'r) _menhir_cell1_EQEQ = 
  | MenhirCell1_EQEQ of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FN = 
  | MenhirCell1_FN of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_GE = 
  | MenhirCell1_GE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_GT = 
  | MenhirCell1_GT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IDENT = 
  | MenhirCell1_IDENT of 's * ('s, 'r) _menhir_state * (
# 7 "lib/parser.mly"
       (string)
# 792 "lib/parser.ml"
) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LBRA = 
  | MenhirCell1_LBRA of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_LBRA = 
  | MenhirCell0_LBRA of 's * Lexing.position

and ('s, 'r) _menhir_cell1_LE = 
  | MenhirCell1_LE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LOOP = 
  | MenhirCell1_LOOP of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_LPAREN = 
  | MenhirCell0_LPAREN of 's * Lexing.position

and ('s, 'r) _menhir_cell1_LT = 
  | MenhirCell1_LT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_MINUS = 
  | MenhirCell0_MINUS of 's * Lexing.position

and ('s, 'r) _menhir_cell1_NEQ = 
  | MenhirCell1_NEQ of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_PERCENT = 
  | MenhirCell1_PERCENT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PLUS = 
  | MenhirCell1_PLUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state * Lexing.position * Lexing.position

and 's _menhir_cell0_RPAREN = 
  | MenhirCell0_RPAREN of 's * Lexing.position

and ('s, 'r) _menhir_cell1_SEMICOLON = 
  | MenhirCell1_SEMICOLON of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_SEMICOLON = 
  | MenhirCell0_SEMICOLON of 's * Lexing.position

and ('s, 'r) _menhir_cell1_STAR = 
  | MenhirCell1_STAR of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_STAR = 
  | MenhirCell0_STAR of 's * Lexing.position

and 's _menhir_cell0_STRUCT = 
  | MenhirCell0_STRUCT of 's * Lexing.position

and ('s, 'r) _menhir_cell1_WHILE = 
  | MenhirCell1_WHILE of 's * ('s, 'r) _menhir_state * Lexing.position

and _menhir_box_prog = 
  | MenhirBox_prog of (Ast.decl list) [@@unboxed]

let _menhir_action_001 =
  fun _endpos__3_ _startpos__1_ sl ->
    let e =
      let e = 
# 95 "lib/parser.mly"
                                        ( Eblock sl )
# 873 "lib/parser.ml"
       in
      let (_endpos_e_, _startpos_e_) = (_endpos__3_, _startpos__1_) in
      let _endpos = _endpos_e_ in
      let _symbolstartpos = _startpos_e_ in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 882 "lib/parser.ml"
      
    in
    (
# 95 "lib/parser.mly"
                                                       ( e )
# 888 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_002 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 896 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_action_003 =
  fun l1 l2 ->
    let x = 
# 89 "lib/parser.mly"
                                                             ( (l1, l2) )
# 904 "lib/parser.ml"
     in
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 909 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_action_004 =
  fun l l1 l2 ->
    let x = 
# 89 "lib/parser.mly"
                                                             ( (l1, l2) )
# 917 "lib/parser.ml"
     in
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 922 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_action_005 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 930 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_006 =
  fun e ->
    let x = 
# 124 "lib/parser.mly"
                 ( e )
# 938 "lib/parser.ml"
     in
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 943 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_007 =
  fun e l ->
    let x = 
# 124 "lib/parser.mly"
                 ( e )
# 951 "lib/parser.ml"
     in
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 956 "lib/parser.ml"
     : (Ast.expr list))

let _menhir_action_008 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 964 "lib/parser.ml"
     : ((Ast.ident * Ast.expr) list))

let _menhir_action_009 =
  fun x ->
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 972 "lib/parser.ml"
     : ((Ast.ident * Ast.expr) list))

let _menhir_action_010 =
  fun l x ->
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 980 "lib/parser.ml"
     : ((Ast.ident * Ast.expr) list))

let _menhir_action_011 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 988 "lib/parser.ml"
     : ((Ast.ident * Ast.mut * Ast.full_typ) list))

let _menhir_action_012 =
  fun x ->
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 996 "lib/parser.ml"
     : ((Ast.ident * Ast.mut * Ast.full_typ) list))

let _menhir_action_013 =
  fun l x ->
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 1004 "lib/parser.ml"
     : ((Ast.ident * Ast.mut * Ast.full_typ) list))

let _menhir_action_014 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 1012 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_015 =
  fun x ->
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 1020 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_016 =
  fun l x ->
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 1028 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_017 =
  fun () ->
    (
# 41 "lib/parser.mly"
                              ( [] )
# 1036 "lib/parser.ml"
     : ((Ast.ident * Ast.full_typ) list))

let _menhir_action_018 =
  fun x ->
    (
# 42 "lib/parser.mly"
                              ( [x] )
# 1044 "lib/parser.ml"
     : ((Ast.ident * Ast.full_typ) list))

let _menhir_action_019 =
  fun l x ->
    (
# 43 "lib/parser.mly"
                              ( x::l )
# 1052 "lib/parser.ml"
     : ((Ast.ident * Ast.full_typ) list))

let _menhir_action_020 =
  fun _endpos__7_ _endpos_copy_ _startpos__2_ _startpos_copy_ copy fl g id ->
    let _endpos = _endpos__7_ in
    let _symbolstartpos = if _startpos_copy_ != _endpos_copy_ then
      _startpos_copy_
    else
      _startpos__2_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 59 "lib/parser.mly"
   ( Dstruct {
      sname = id;
      slfts = g;
      sfields = fl;
      scopy = copy = Some ();
      sloc = _sloc }
    )
# 1072 "lib/parser.ml"
     : (Ast.decl))

let _menhir_action_021 =
  fun _endpos_b_ _startpos__1_ b f fl g o r ->
    let _endpos = _endpos_b_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 68 "lib/parser.mly"
   ( Dfundef {
      fname = f;
      flfts = g;
      fformals = fl;
      freturn = r;
      foutlives = o;
      fbody = b;
      floc = _sloc }
    )
# 1091 "lib/parser.ml"
     : (Ast.decl))

let _menhir_action_022 =
  fun b ->
    (
# 170 "lib/parser.mly"
                    ( b.edesc )
# 1099 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_023 =
  fun e ->
    (
# 171 "lib/parser.mly"
                    ( e )
# 1107 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_024 =
  fun () ->
    (
# 172 "lib/parser.mly"
                    ( Eunit )
# 1115 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_025 =
  fun e ->
    (
# 120 "lib/parser.mly"
                                         ( e )
# 1123 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_026 =
  fun e ->
    (
# 121 "lib/parser.mly"
                                         ( e )
# 1131 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_027 =
  fun e ->
    (
# 120 "lib/parser.mly"
                                         ( e )
# 1139 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_028 =
  fun e ->
    (
# 121 "lib/parser.mly"
                                         ( e )
# 1147 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_029 =
  fun _endpos_e_ _startpos_e_ e ->
    let e =
      let _endpos = _endpos_e_ in
      let _symbolstartpos = _startpos_e_ in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 1159 "lib/parser.ml"
      
    in
    (
# 163 "lib/parser.mly"
                               ( e )
# 1165 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_030 =
  fun e ->
    (
# 157 "lib/parser.mly"
                                            ( e.edesc )
# 1173 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_031 =
  fun e ->
    (
# 158 "lib/parser.mly"
                                            ( Eloop e )
# 1181 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_032 =
  fun b e ->
    (
# 159 "lib/parser.mly"
                                            ( Ewhile (e, b) )
# 1189 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_033 =
  fun e ->
    (
# 160 "lib/parser.mly"
                                            ( e )
# 1197 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_034 =
  fun _endpos_e_ _startpos_e_ e ->
    let e =
      let _endpos = _endpos_e_ in
      let _symbolstartpos = _startpos_e_ in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 1209 "lib/parser.ml"
      
    in
    (
# 154 "lib/parser.mly"
                                           ( e )
# 1215 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_035 =
  fun _endpos_e_ _startpos_e_ e ->
    let e =
      let _endpos = _endpos_e_ in
      let _symbolstartpos = _startpos_e_ in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 1227 "lib/parser.ml"
      
    in
    (
# 154 "lib/parser.mly"
                                           ( e )
# 1233 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_036 =
  fun c ->
    (
# 127 "lib/parser.mly"
                                                   ( Econst c )
# 1241 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_037 =
  fun e1 e2 ->
    let o = 
# 178 "lib/parser.mly"
          ( Badd )
# 1249 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1254 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_038 =
  fun e1 e2 ->
    let o = 
# 179 "lib/parser.mly"
          ( Bsub )
# 1262 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1267 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_039 =
  fun e1 e2 ->
    let o = 
# 180 "lib/parser.mly"
          ( Bmul )
# 1275 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1280 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_040 =
  fun e1 e2 ->
    let o = 
# 181 "lib/parser.mly"
          ( Bdiv )
# 1288 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1293 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_041 =
  fun e1 e2 ->
    let o = 
# 182 "lib/parser.mly"
          ( Bmod )
# 1301 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1306 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_042 =
  fun e1 e2 ->
    let o = 
# 183 "lib/parser.mly"
          ( Beqeq )
# 1314 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1319 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_043 =
  fun e1 e2 ->
    let o = 
# 184 "lib/parser.mly"
          ( Bneq )
# 1327 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1332 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_044 =
  fun e1 e2 ->
    let o = 
# 185 "lib/parser.mly"
          ( Blt )
# 1340 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1345 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_045 =
  fun e1 e2 ->
    let o = 
# 186 "lib/parser.mly"
          ( Ble )
# 1353 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1358 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_046 =
  fun e1 e2 ->
    let o = 
# 187 "lib/parser.mly"
          ( Bgt )
# 1366 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1371 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_047 =
  fun e1 e2 ->
    let o = 
# 188 "lib/parser.mly"
          ( Bge )
# 1379 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1384 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_048 =
  fun c1 c2 ->
    (
# 129 "lib/parser.mly"
                                                   ( Eand (c1, c2) )
# 1392 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_049 =
  fun c1 c2 ->
    (
# 130 "lib/parser.mly"
                                                   ( Eor  (c1, c2) )
# 1400 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_050 =
  fun e1 e2 ->
    (
# 131 "lib/parser.mly"
                                                   ( Eassign (e1, e2) )
# 1408 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_051 =
  fun e ->
    (
# 132 "lib/parser.mly"
                                                   ( Eunop (Uneg, e) )
# 1416 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_052 =
  fun c ->
    (
# 133 "lib/parser.mly"
                                                   ( Eunop (Unot, c) )
# 1424 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_053 =
  fun e ->
    (
# 134 "lib/parser.mly"
                                                   ( Ederef e )
# 1432 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_054 =
  fun e mut ->
    (
# 135 "lib/parser.mly"
                                                   ( Eborrow (mut, e) )
# 1440 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_055 =
  fun _endpos_e_ _startpos__1_ e mut ->
    let _endpos = _endpos_e_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 136 "lib/parser.mly"
                                                   (
    Eborrow(NotMut,
      { edesc = Eborrow (mut, e);
        eloc = _sloc;
        etyp = None }
    )
  )
# 1457 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_056 =
  fun id ->
    (
# 143 "lib/parser.mly"
                                                   ( Evar id )
# 1465 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_057 =
  fun e id ->
    (
# 144 "lib/parser.mly"
                                                   ( Edot (e, id) )
# 1473 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_058 =
  fun () ->
    (
# 145 "lib/parser.mly"
                                                   ( Eunit )
# 1481 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_059 =
  fun fl id ->
    let _1 = 
# 49 "lib/parser.mly"
                      ( assert false )
# 1489 "lib/parser.ml"
     in
    (
# 146 "lib/parser.mly"
                                                   ( Econstr_stru (id, fl) )
# 1494 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_060 =
  fun () ->
    (
# 147 "lib/parser.mly"
                                                   ( Ebreak )
# 1502 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_061 =
  fun e ->
    (
# 148 "lib/parser.mly"
                                                   ( Ereturn (Some e) )
# 1510 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_062 =
  fun () ->
    let _1 = 
# 49 "lib/parser.mly"
                      ( assert false )
# 1518 "lib/parser.ml"
     in
    (
# 149 "lib/parser.mly"
                                                   ( Ereturn None )
# 1523 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_063 =
  fun el id ->
    (
# 150 "lib/parser.mly"
                                                   ( Ecall (id, el) )
# 1531 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_064 =
  fun e ->
    let e = 
# 124 "lib/parser.mly"
                 ( e )
# 1539 "lib/parser.ml"
     in
    (
# 151 "lib/parser.mly"
                                                   ( e.edesc )
# 1544 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_065 =
  fun c ->
    (
# 127 "lib/parser.mly"
                                                   ( Econst c )
# 1552 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_066 =
  fun e1 e2 ->
    let o = 
# 178 "lib/parser.mly"
          ( Badd )
# 1560 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1565 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_067 =
  fun e1 e2 ->
    let o = 
# 179 "lib/parser.mly"
          ( Bsub )
# 1573 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1578 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_068 =
  fun e1 e2 ->
    let o = 
# 180 "lib/parser.mly"
          ( Bmul )
# 1586 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1591 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_069 =
  fun e1 e2 ->
    let o = 
# 181 "lib/parser.mly"
          ( Bdiv )
# 1599 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1604 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_070 =
  fun e1 e2 ->
    let o = 
# 182 "lib/parser.mly"
          ( Bmod )
# 1612 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1617 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_071 =
  fun e1 e2 ->
    let o = 
# 183 "lib/parser.mly"
          ( Beqeq )
# 1625 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1630 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_072 =
  fun e1 e2 ->
    let o = 
# 184 "lib/parser.mly"
          ( Bneq )
# 1638 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1643 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_073 =
  fun e1 e2 ->
    let o = 
# 185 "lib/parser.mly"
          ( Blt )
# 1651 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1656 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_074 =
  fun e1 e2 ->
    let o = 
# 186 "lib/parser.mly"
          ( Ble )
# 1664 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1669 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_075 =
  fun e1 e2 ->
    let o = 
# 187 "lib/parser.mly"
          ( Bgt )
# 1677 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1682 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_076 =
  fun e1 e2 ->
    let o = 
# 188 "lib/parser.mly"
          ( Bge )
# 1690 "lib/parser.ml"
     in
    (
# 128 "lib/parser.mly"
                                                   ( Ebinop (o, e1, e2) )
# 1695 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_077 =
  fun c1 c2 ->
    (
# 129 "lib/parser.mly"
                                                   ( Eand (c1, c2) )
# 1703 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_078 =
  fun c1 c2 ->
    (
# 130 "lib/parser.mly"
                                                   ( Eor  (c1, c2) )
# 1711 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_079 =
  fun e1 e2 ->
    (
# 131 "lib/parser.mly"
                                                   ( Eassign (e1, e2) )
# 1719 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_080 =
  fun e ->
    (
# 132 "lib/parser.mly"
                                                   ( Eunop (Uneg, e) )
# 1727 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_081 =
  fun c ->
    (
# 133 "lib/parser.mly"
                                                   ( Eunop (Unot, c) )
# 1735 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_082 =
  fun e ->
    (
# 134 "lib/parser.mly"
                                                   ( Ederef e )
# 1743 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_083 =
  fun e mut ->
    (
# 135 "lib/parser.mly"
                                                   ( Eborrow (mut, e) )
# 1751 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_084 =
  fun _endpos_e_ _startpos__1_ e mut ->
    let _endpos = _endpos_e_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 136 "lib/parser.mly"
                                                   (
    Eborrow(NotMut,
      { edesc = Eborrow (mut, e);
        eloc = _sloc;
        etyp = None }
    )
  )
# 1768 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_085 =
  fun id ->
    (
# 143 "lib/parser.mly"
                                                   ( Evar id )
# 1776 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_086 =
  fun e id ->
    (
# 144 "lib/parser.mly"
                                                   ( Edot (e, id) )
# 1784 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_087 =
  fun () ->
    (
# 145 "lib/parser.mly"
                                                   ( Eunit )
# 1792 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_088 =
  fun fl id ->
    let _1 = 
# 48 "lib/parser.mly"
               ( () )
# 1800 "lib/parser.ml"
     in
    (
# 146 "lib/parser.mly"
                                                   ( Econstr_stru (id, fl) )
# 1805 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_089 =
  fun () ->
    (
# 147 "lib/parser.mly"
                                                   ( Ebreak )
# 1813 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_090 =
  fun e ->
    (
# 148 "lib/parser.mly"
                                                   ( Ereturn (Some e) )
# 1821 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_091 =
  fun () ->
    let _1 = 
# 48 "lib/parser.mly"
               ( () )
# 1829 "lib/parser.ml"
     in
    (
# 149 "lib/parser.mly"
                                                   ( Ereturn None )
# 1834 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_092 =
  fun el id ->
    (
# 150 "lib/parser.mly"
                                                   ( Ecall (id, el) )
# 1842 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_093 =
  fun e ->
    let e = 
# 124 "lib/parser.mly"
                 ( e )
# 1850 "lib/parser.ml"
     in
    (
# 151 "lib/parser.mly"
                                                   ( e.edesc )
# 1855 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_094 =
  fun e id ->
    let e = 
# 124 "lib/parser.mly"
                 ( e )
# 1863 "lib/parser.ml"
     in
    (
# 175 "lib/parser.mly"
                        ( id, e )
# 1868 "lib/parser.ml"
     : (Ast.ident * Ast.expr))

let _menhir_action_095 =
  fun id mut ty ->
    let ty = 
# 54 "lib/parser.mly"
                                                     ( ty )
# 1876 "lib/parser.ml"
     in
    (
# 82 "lib/parser.mly"
                                          ( (id, mut, ty) )
# 1881 "lib/parser.ml"
     : (Ast.ident * Ast.mut * Ast.full_typ))

let _menhir_action_096 =
  fun g ->
    (
# 52 "lib/parser.mly"
                                                ( g )
# 1889 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_097 =
  fun _endpos_id_ _startpos_id_ id ->
    let _endpos = _endpos_id_ in
    let _symbolstartpos = _startpos_id_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 34 "lib/parser.mly"
           ( { iloc = _sloc; id } )
# 1900 "lib/parser.ml"
     : (Ast.ident))

let _menhir_action_098 =
  fun _endpos_e_inlined1_ _startpos_e_inlined1_ b1 e e_inlined1 ->
    let b2 =
      let (_endpos_e_, _startpos_e_, e) = (_endpos_e_inlined1_, _startpos_e_inlined1_, e_inlined1) in
      let _endpos = _endpos_e_ in
      let _symbolstartpos = if _startpos_e_ != _endpos_e_ then
        _startpos_e_
      else
        _endpos in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 1916 "lib/parser.ml"
      
    in
    (
# 167 "lib/parser.mly"
    ( Eif (e, b1, b2) )
# 1922 "lib/parser.ml"
     : (Ast.expr_desc))

let _menhir_action_099 =
  fun _endpos__s_ _l _s _startpos__l_ b e id mut ty ->
    let ty = 
# 55 "lib/parser.mly"
                                         ( ty )
# 1930 "lib/parser.ml"
     in
    (
# 111 "lib/parser.mly"
   ( { edesc = Elet(id, mut, ty, e, b);
       eloc = (_startpos__l_, _endpos__s_);
       etyp = None } )
# 1937 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_100 =
  fun _endpos__4_ _startpos__1_ ->
    let _endpos = _endpos__4_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 115 "lib/parser.mly"
  ( Error.error _sloc "In MiniRust, all let-bindings must have explicit types." )
# 1948 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_101 =
  fun _endpos__4_ _startpos__1_ ->
    let _endpos = _endpos__4_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    (
# 117 "lib/parser.mly"
  ( Error.error _sloc "In MiniRust, all let-bindings must have explicit types." )
# 1959 "lib/parser.ml"
     : (Ast.expr))

let _menhir_action_102 =
  fun l ->
    (
# 201 "lib/parser.mly"
                                         ( Lnamed l )
# 1967 "lib/parser.ml"
     : (Ast.lifetime))

let _menhir_action_103 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 1975 "lib/parser.ml"
     : (Ast.decl list))

let _menhir_action_104 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 1983 "lib/parser.ml"
     : (Ast.decl list))

let _menhir_action_105 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1991 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_106 =
  fun g ->
    let x = 
# 52 "lib/parser.mly"
                                         ( g )
# 1999 "lib/parser.ml"
     in
    (
# 148 "<standard.mly>"
    ( x )
# 2004 "lib/parser.ml"
     : (Ast.lifetime list))

let _menhir_action_107 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 2012 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_action_108 =
  fun l ->
    let x = 
# 89 "lib/parser.mly"
                                                                           ( l )
# 2020 "lib/parser.ml"
     in
    (
# 148 "<standard.mly>"
    ( x )
# 2025 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_action_109 =
  fun () ->
    (
# 37 "lib/parser.mly"
      ( Mut )
# 2033 "lib/parser.ml"
     : (Ast.mut))

let _menhir_action_110 =
  fun () ->
    (
# 38 "lib/parser.mly"
  ( NotMut )
# 2041 "lib/parser.ml"
     : (Ast.mut))

let _menhir_action_111 =
  fun b ->
    (
# 102 "lib/parser.mly"
                                                          ( b )
# 2049 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_112 =
  fun s ->
    (
# 103 "lib/parser.mly"
                                                          ( [], s )
# 2057 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_113 =
  fun b e ->
    (
# 104 "lib/parser.mly"
                                                          ( e::fst b, snd b )
# 2065 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_114 =
  fun b e ->
    (
# 105 "lib/parser.mly"
                                                          ( e::fst b, snd b )
# 2073 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_115 =
  fun e ->
    let e = 
# 124 "lib/parser.mly"
                 ( e )
# 2081 "lib/parser.ml"
     in
    (
# 106 "lib/parser.mly"
                                                          ( [], e )
# 2086 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_116 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2094 "lib/parser.ml"
     : (unit option))

let _menhir_action_117 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 2102 "lib/parser.ml"
     : (unit option))

let _menhir_action_118 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 2110 "lib/parser.ml"
     : (Ast.expr option))

let _menhir_action_119 =
  fun e ->
    let x =
      let e = 
# 124 "lib/parser.mly"
                 ( e )
# 2119 "lib/parser.ml"
       in
      
# 109 "lib/parser.mly"
                                                                    (e)
# 2124 "lib/parser.ml"
      
    in
    (
# 114 "<standard.mly>"
    ( Some x )
# 2130 "lib/parser.ml"
     : (Ast.expr option))

let _menhir_action_120 =
  fun l ->
    (
# 204 "lib/parser.mly"
              ( l )
# 2138 "lib/parser.ml"
     : (Ast.decl list))

let _menhir_action_121 =
  fun ty ->
    let ty = 
# 54 "lib/parser.mly"
                                                     ( ty )
# 2146 "lib/parser.ml"
     in
    (
# 85 "lib/parser.mly"
                    ( ty )
# 2151 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_122 =
  fun () ->
    (
# 86 "lib/parser.mly"
                    ( Tunit )
# 2159 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_123 =
  fun _endpos__0_ ->
    let e =
      let e = 
# 98 "lib/parser.mly"
                         ( Eunit )
# 2168 "lib/parser.ml"
       in
      let _endpos_e_ = _endpos__0_ in
      let _endpos = _endpos_e_ in
      let _symbolstartpos = _endpos in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 92 "lib/parser.mly"
      ( { edesc = e; eloc = _sloc; etyp = None } )
# 2177 "lib/parser.ml"
      
    in
    (
# 98 "lib/parser.mly"
                                      ( [], e )
# 2183 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_124 =
  fun b ->
    (
# 99 "lib/parser.mly"
                                      ( b )
# 2191 "lib/parser.ml"
     : (Ast.block))

let _menhir_action_125 =
  fun id ty ->
    let ty = 
# 54 "lib/parser.mly"
                                                     ( ty )
# 2199 "lib/parser.ml"
     in
    (
# 79 "lib/parser.mly"
                             ( (id, ty) )
# 2204 "lib/parser.ml"
     : (Ast.ident * Ast.full_typ))

let _menhir_action_126 =
  fun id ->
    let gen = 
# 55 "lib/parser.mly"
                                 ( [] )
# 2212 "lib/parser.ml"
     in
    (
# 191 "lib/parser.mly"
                                           ( Tstruct (id, gen) )
# 2217 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_127 =
  fun () ->
    (
# 192 "lib/parser.mly"
                                           ( Ti32 )
# 2225 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_128 =
  fun () ->
    (
# 193 "lib/parser.mly"
                                           ( Tbool )
# 2233 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_129 =
  fun () ->
    (
# 194 "lib/parser.mly"
                                           ( Tunit )
# 2241 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_130 =
  fun mut ty ->
    let l = 
# 55 "lib/parser.mly"
                             ()
# 2249 "lib/parser.ml"
     in
    (
# 196 "lib/parser.mly"
                                           ( Tborrow (l, mut, ty) )
# 2254 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_131 =
  fun mut ty ->
    let nl = 
# 55 "lib/parser.mly"
                         ()
# 2262 "lib/parser.ml"
     in
    (
# 198 "lib/parser.mly"
                                           ( Tborrow (nl, NotMut, Tborrow(nl, mut, ty)) )
# 2267 "lib/parser.ml"
     : (unit Ast.typ))

let _menhir_action_132 =
  fun gen id ->
    (
# 191 "lib/parser.mly"
                                           ( Tstruct (id, gen) )
# 2275 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_133 =
  fun () ->
    (
# 192 "lib/parser.mly"
                                           ( Ti32 )
# 2283 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_134 =
  fun () ->
    (
# 193 "lib/parser.mly"
                                           ( Tbool )
# 2291 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_135 =
  fun () ->
    (
# 194 "lib/parser.mly"
                                           ( Tunit )
# 2299 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_136 =
  fun l mut ty ->
    (
# 196 "lib/parser.mly"
                                           ( Tborrow (l, mut, ty) )
# 2307 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_137 =
  fun mut ty ->
    let nl = 
# 49 "lib/parser.mly"
                      ( assert false )
# 2315 "lib/parser.ml"
     in
    (
# 198 "lib/parser.mly"
                                           ( Tborrow (nl, NotMut, Tborrow(nl, mut, ty)) )
# 2320 "lib/parser.ml"
     : (Ast.lifetime Ast.typ))

let _menhir_action_138 =
  fun l ->
    (
# 89 "lib/parser.mly"
                                                                                  ( l )
# 2328 "lib/parser.ml"
     : ((Ast.lifetime * Ast.lifetime) list))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AMP ->
        "AMP"
    | AMPAMP ->
        "AMPAMP"
    | ARROW ->
        "ARROW"
    | BARBAR ->
        "BARBAR"
    | BOOL ->
        "BOOL"
    | BREAK ->
        "BREAK"
    | COLON ->
        "COLON"
    | COMMA ->
        "COMMA"
    | CONSTANT _ ->
        "CONSTANT"
    | DERIVECOPY ->
        "DERIVECOPY"
    | DIV ->
        "DIV"
    | DOT ->
        "DOT"
    | DUMMY ->
        "DUMMY"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | EQEQ ->
        "EQEQ"
    | FN ->
        "FN"
    | GE ->
        "GE"
    | GT ->
        "GT"
    | I32 ->
        "I32"
    | IDENT _ ->
        "IDENT"
    | IF ->
        "IF"
    | LBRA ->
        "LBRA"
    | LE ->
        "LE"
    | LET ->
        "LET"
    | LIFETIME _ ->
        "LIFETIME"
    | LOOP ->
        "LOOP"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MINUS ->
        "MINUS"
    | MUT ->
        "MUT"
    | NEQ ->
        "NEQ"
    | NOT ->
        "NOT"
    | PERCENT ->
        "PERCENT"
    | PLUS ->
        "PLUS"
    | RBRA ->
        "RBRA"
    | RETURN ->
        "RETURN"
    | RPAREN ->
        "RPAREN"
    | SEMICOLON ->
        "SEMICOLON"
    | STAR ->
        "STAR"
    | STRUCT ->
        "STRUCT"
    | WHERE ->
        "WHERE"
    | WHILE ->
        "WHILE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_249 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let l = _v in
      let _v = _menhir_action_120 l in
      MenhirBox_prog _v
  
  let rec _menhir_run_252 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_decl -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let MenhirCell1_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_104 x xs in
      _menhir_goto_list_decl_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_decl_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState251 ->
          _menhir_run_252 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_249 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_FN (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState001 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_002 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_id_, _startpos_id_, id) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_097 _endpos_id_ _startpos_id_ id in
      _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_goto_ident : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState240 ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState242 ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState237 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState199 ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState145 ->
          _menhir_run_146 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState050 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState171 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState168 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState156 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState152 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState134 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState087 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState049 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState122 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState120 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState068 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState065 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState001 ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_243 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState244 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | I32 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_135 () in
          _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_typ_false__lifetime_generics_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState244 ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState038 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState017 ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState026 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState029 ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_245 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_125 id ty in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_struct_field (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState242
          | RBRA ->
              let _v_1 = _menhir_action_017 () in
              _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | _ ->
              _eRR ())
      | RBRA ->
          let x = _v in
          let _v = _menhir_action_018 x in
          _menhir_goto_comma_list_struct_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_246 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_struct_field -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_struct_field (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_019 l x in
      _menhir_goto_comma_list_struct_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list_struct_field_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState240 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState242 ->
          _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_247 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LBRA -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_LBRA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_generics (_menhir_stack, _, g) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
      let MenhirCell0_STRUCT (_menhir_stack, _startpos__2_) = _menhir_stack in
      let MenhirCell1_option_DERIVECOPY_ (_menhir_stack, _menhir_s, copy, _startpos_copy_, _endpos_copy_) = _menhir_stack in
      let (fl, _endpos__7_) = (_v, _endpos) in
      let _v = _menhir_action_020 _endpos__7_ _endpos_copy_ _startpos__2_ _startpos_copy_ copy fl g id in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | FN ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState251
      | DERIVECOPY ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState251
      | EOF ->
          let _v_0 = _menhir_action_103 () in
          _menhir_run_252 _menhir_stack _v_0
      | STRUCT ->
          let _menhir_s = MenhirState251 in
          let _v = _menhir_action_116 () in
          _menhir_goto_option_DERIVECOPY_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _endpos _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_234 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, ()) in
      let _v = _menhir_action_117 x in
      _menhir_goto_option_DERIVECOPY_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_goto_option_DERIVECOPY_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_option_DERIVECOPY_ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_STRUCT (_menhir_stack, _startpos) in
          let _menhir_s = MenhirState237 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_039 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let ty = _v in
      let _v = _menhir_action_121 ty in
      _menhir_goto_return_type _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_return_type : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_return_type (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | WHERE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LIFETIME _v_0 ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState041
          | LBRA ->
              let _v_1 = _menhir_action_002 () in
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | _ ->
              _eRR ())
      | LBRA ->
          let _v = _menhir_action_107 () in
          _menhir_goto_loption___anonymous_6_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_005 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let l = _v in
      let _v = _menhir_action_102 l in
      _menhir_goto_lifetime _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_lifetime : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState043 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState045 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState041 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState027 ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState007 ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState004 ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_044 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_lifetime as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_lifetime (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LIFETIME _v_0 ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState045
          | LBRA ->
              let _v_1 = _menhir_action_002 () in
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | _ ->
              _eRR ())
      | LBRA ->
          let MenhirCell1_lifetime (_menhir_stack, _menhir_s, l1) = _menhir_stack in
          let l2 = _v in
          let _v = _menhir_action_003 l1 l2 in
          _menhir_goto_comma_list___anonymous_5_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_046 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_cell1_lifetime -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_lifetime (_menhir_stack, _, l2) = _menhir_stack in
      let MenhirCell1_lifetime (_menhir_stack, _menhir_s, l1) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_004 l l1 l2 in
      _menhir_goto_comma_list___anonymous_5_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list___anonymous_5_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState041 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState045 ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_047 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN _menhir_cell0_return_type -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let l = _v in
      let _v = _menhir_action_108 l in
      _menhir_goto_loption___anonymous_6_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_goto_loption___anonymous_6_ : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN _menhir_cell0_return_type -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let l = _v in
      let _v = _menhir_action_138 l in
      let _menhir_stack = MenhirCell0_where_clause (_menhir_stack, _v) in
      _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
  
  and _menhir_run_049 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_LBRA (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | SEMICOLON ->
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LET ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState049
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState049
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState049
      | RBRA ->
          let _v =
            let _endpos__0_ = _endpos in
            _menhir_action_123 _endpos__0_
          in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_050 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState050 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_051 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState051 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
      let _menhir_s = MenhirState052 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_053 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState053 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_054 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState054 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_055 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | STAR ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | RPAREN ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos__2_, _startpos__1_) = (_endpos, _startpos) in
          let _v = _menhir_action_058 () in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__2_ _startpos__1_ _v _menhir_s _tok
      | RETURN ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | NOT ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | MINUS ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | LPAREN ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | LOOP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | LBRA ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | IF ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState055
      | CONSTANT _v ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState055
      | BREAK ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | AMP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState055
      | _ ->
          _eRR ()
  
  and _menhir_run_056 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState056 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_057 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | STAR ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | RETURN ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | NOT ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | MINUS ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | LPAREN ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | LOOP ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | LBRA ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | IF ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState057
      | CONSTANT _v ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState057
      | BREAK ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | AMP ->
          let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos, _endpos) in
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState057
      | BARBAR | COMMA | DIV | DOT | EQ | EQEQ | GE | GT | LE | LT | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON ->
          let (_endpos__2_, _startpos__2_) = (_endpos, _startpos) in
          let _v = _menhir_action_091 () in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__2_ _startpos__2_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_058 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState058 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_059 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState059 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_060 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | STAR ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | RPAREN ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos__2_, _startpos__1_) = (_endpos, _startpos) in
          let _v = _menhir_action_087 () in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__2_ _startpos__1_ _v _menhir_s _tok
      | RETURN ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | NOT ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | MINUS ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | LPAREN ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | LOOP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | LBRA ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | IF ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState060
      | CONSTANT _v ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState060
      | BREAK ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | AMP ->
          let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr_without_block__true__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_035 _endpos_e_ _startpos_e_ e in
      _menhir_goto_expr_without_block_true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_goto_expr_without_block_true__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState049 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_223 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr_without_block_true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _menhir_stack = MenhirCell0_SEMICOLON (_menhir_stack, _endpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | SEMICOLON ->
              _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | LET ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | IDENT _v_1 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState224
          | CONSTANT _v_2 ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState224
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState224
          | RBRA ->
              let _v_3 =
                let _endpos__0_ = _endpos_0 in
                _menhir_action_123 _endpos__0_
              in
              _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 _tok
          | _ ->
              _eRR ())
      | AMPAMP | BARBAR | DIV | DOT | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | STAR ->
          let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_027 e in
          _menhir_goto_expr__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_197 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s, _endpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | SEMICOLON ->
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | LET ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState197
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState197
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState197
      | RBRA ->
          let _v =
            let _endpos__0_ = _endpos in
            _menhir_action_123 _endpos__0_
          in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_062 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LOOP (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState062 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_198 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState198
      | IDENT _ ->
          let _v = _menhir_action_110 () in
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState198 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_109 () in
      _menhir_goto_mutornot _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_mutornot : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState211 ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState209 ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState198 ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState135 ->
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState133 ->
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState075 ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState073 ->
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState028 ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_212 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState212
      | IDENT _v_0 ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState212
      | I32 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState212
      | BOOL ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState212
      | AMPAMP ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState212
      | AMP ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState212
      | _ ->
          _eRR ()
  
  and _menhir_run_204 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_129 () in
          _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState203 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState212 ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_215 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ___anonymous_2___anonymous_3___anonymous_4_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _menhir_stack = MenhirCell0_EQ (_menhir_stack, _endpos) in
          let _menhir_s = MenhirState216 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONSTANT _v ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | SEMICOLON ->
          let _v = _menhir_action_118 () in
          _menhir_goto_option___anonymous_9_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState064 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_065 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RETURN ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos__2_, _startpos__1_) = (_endpos, _startpos) in
          let _v = _menhir_action_062 () in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__2_ _startpos__1_ _v _menhir_s _tok
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_DUMMY (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState065
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr_without_block__false__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_034 _endpos_e_ _startpos_e_ e in
      let (_endpos, _startpos) = (_endpos_e_, _startpos_e_) in
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_025 e in
      _menhir_goto_expr__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_goto_expr__false__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState050 ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState171 ->
          _menhir_run_172 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_170 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState168 ->
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_161 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_159 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState156 ->
          _menhir_run_157 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_155 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState152 ->
          _menhir_run_153 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState134 ->
          _menhir_run_147 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_144 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_195 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | PLUS ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | PERCENT ->
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | NEQ ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | MINUS ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | LT ->
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | LE ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | GT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | GE ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | EQEQ ->
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | EQ ->
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | DOT ->
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | DIV ->
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | BARBAR ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | AMPAMP ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState195
      | _ ->
          _eRR ()
  
  and _menhir_run_148 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState148 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_131 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_c_, _startpos_c_, c) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_036 c in
      _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c_ _startpos_c_ _v _menhir_s _tok
  
  and _menhir_run_132 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos__1_, _startpos__1_) = (_endpos, _startpos) in
      let _v = _menhir_action_060 () in
      _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__1_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_133 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState133
      | AMP | AMPAMP | BREAK | CONSTANT _ | DUMMY | IDENT _ | IF | LBRA | LOOP | LPAREN | MINUS | NOT | RETURN | STAR | WHILE ->
          let _v = _menhir_action_110 () in
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState133 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_134 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState134
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | CONSTANT _v_1 ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState134
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState134
      | _ ->
          _eRR ()
  
  and _menhir_run_135 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState135
      | AMP | AMPAMP | BREAK | CONSTANT _ | DUMMY | IDENT _ | IF | LBRA | LOOP | LPAREN | MINUS | NOT | RETURN | STAR | WHILE ->
          let _v = _menhir_action_110 () in
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState135 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_136 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState136
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | CONSTANT _v_1 ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState136
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState136
      | _ ->
          _eRR ()
  
  and _menhir_run_150 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PLUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState150 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_152 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PERCENT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState152 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_156 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NEQ (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState156 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_158 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState158 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_160 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState160 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_162 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState162 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_164 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_GT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState164 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_166 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_GE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState166 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_168 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_EQEQ (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState168 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_171 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_EQ (_menhir_stack, _menhir_s, _endpos) in
      let _menhir_s = MenhirState171 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_145 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DOT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState145 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_154 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DIV (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState154 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_173 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_BARBAR (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState173 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_175 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState175 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | DUMMY ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CONSTANT _v ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_194 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState194
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_053 e in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_193 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_RETURN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | LT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | LE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | GT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | GE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState193
      | LBRA ->
          let MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos__1_, _) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_061 e in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_192 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_NOT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState192
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_NOT (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_c_, c) = (_endpos, _v) in
          let _v = _menhir_action_052 c in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_191 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState191
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_051 e in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_176 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_AMPAMP as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | LT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | LE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | GT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | GE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState176
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_AMPAMP (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, c1, _startpos_c1_, _) = _menhir_stack in
          let (_endpos_c2_, c2) = (_endpos, _v) in
          let _v = _menhir_action_048 c1 c2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c2_ _startpos_c1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_174 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_BARBAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | LT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | LE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | GT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | GE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState174
      | BARBAR | EQ | LBRA ->
          let MenhirCell1_BARBAR (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, c1, _startpos_c1_, _) = _menhir_stack in
          let (_endpos_c2_, c2) = (_endpos, _v) in
          let _v = _menhir_action_049 c1 c2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c2_ _startpos_c1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_172 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | LT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | LE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | GT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | GE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState172
      | LBRA ->
          let MenhirCell1_EQ (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_050 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_170 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | PLUS ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | PERCENT ->
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | NEQ ->
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | MINUS ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | LT ->
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | LE ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | GT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | GE ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | EQEQ ->
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | EQ ->
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | DOT ->
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | DIV ->
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | BARBAR ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | AMPAMP ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState170
      | _ ->
          _eRR ()
  
  and _menhir_run_169 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_EQEQ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState169
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_EQEQ (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_042 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_167 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GE as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState167
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_GE (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_047 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_165 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_GT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState165
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_GT (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_046 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_163 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LE as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState163
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_LE (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_045 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_161 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_LT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState161
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_LT (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_044 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_159 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState159
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState159
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState159
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState159
      | AMPAMP | BARBAR | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PLUS ->
          let MenhirCell1_MINUS (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_038 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_157 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_NEQ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState157
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_NEQ (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_043 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_155 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_DIV as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState155
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_DIV (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_040 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_153 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PERCENT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState153
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_PERCENT (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_041 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_151 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_PLUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState151
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState151
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState151
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState151
      | AMPAMP | BARBAR | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PLUS ->
          let MenhirCell1_PLUS (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_037 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_149 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState149
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_STAR (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_039 e1 e2 in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_147 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_156 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | LT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | LE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | GT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | GE ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_154 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState147
      | AMPAMP | BARBAR | EQ | LBRA ->
          let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
          let MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_055 _endpos_e_ _startpos__1_ e mut in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_144 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState144
      | AMPAMP | BARBAR | DIV | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
          let MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_054 e mut in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_071 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_c_, _startpos_c_, c) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_065 c in
      _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c_ _startpos_c_ _v _menhir_s _tok
  
  and _menhir_run_072 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos__1_, _startpos__1_) = (_endpos, _startpos) in
      let _v = _menhir_action_089 () in
      _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__1_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_073 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState073
      | AMP | AMPAMP | BREAK | CONSTANT _ | IDENT _ | IF | LBRA | LOOP | LPAREN | MINUS | NOT | RETURN | STAR | WHILE ->
          let _v = _menhir_action_110 () in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState073 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_074 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState074
      | CONSTANT _v_1 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState074
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState074
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState075
      | AMP | AMPAMP | BREAK | CONSTANT _ | IDENT _ | IF | LBRA | LOOP | LPAREN | MINUS | NOT | RETURN | STAR | WHILE ->
          let _v = _menhir_action_110 () in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState075 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_076 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState076
      | CONSTANT _v_1 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState076
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState076
      | _ ->
          _eRR ()
  
  and _menhir_goto_option___anonymous_9_ : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _menhir_stack = MenhirCell0_option___anonymous_9_ (_menhir_stack, _v) in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell0_SEMICOLON (_menhir_stack, _endpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | SEMICOLON ->
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | LET ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState219
      | CONSTANT _v_1 ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState219
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState219
      | RBRA ->
          let _v_2 =
            let _endpos__0_ = _endpos in
            _menhir_action_123 _endpos__0_
          in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_220 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_cell0_option___anonymous_9_ _menhir_cell0_SEMICOLON -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_SEMICOLON (_menhir_stack, _endpos__s_) = _menhir_stack in
      let MenhirCell0_option___anonymous_9_ (_menhir_stack, e) = _menhir_stack in
      let MenhirCell1_typ___anonymous_2___anonymous_3___anonymous_4_ (_menhir_stack, _, ty) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
      let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
      let MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos__l_) = _menhir_stack in
      let (b, _s, _l) = (_v, (), ()) in
      let _v = _menhir_action_099 _endpos__s_ _l _s _startpos__l_ b e id mut ty in
      _menhir_goto_let_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_let_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let s = _v in
      let _v = _menhir_action_112 s in
      _menhir_goto_nonempty_stmts _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_nonempty_stmts : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState226 ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState049 ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_227 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr_with_block -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, e, _, _) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_114 b e in
      _menhir_goto_nonempty_stmts _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_221 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let b = _v in
      let _v = _menhir_action_124 b in
      _menhir_goto_stmts_or_unit _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_stmts_or_unit : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState049 ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState197 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState224 ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState219 ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_230 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LBRA -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRA ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRA (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos__3_, sl) = (_endpos, _v) in
          let _v = _menhir_action_001 _endpos__3_ _startpos__1_ sl in
          _menhir_goto_block_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_block_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState048 ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState195 ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState178 ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState170 ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState049 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState171 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState134 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState168 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState156 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState152 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState062 ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_232 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN, _menhir_box_prog) _menhir_cell1_comma_list_formal_ _menhir_cell0_RPAREN _menhir_cell0_return_type _menhir_cell0_where_clause -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell0_where_clause (_menhir_stack, o) = _menhir_stack in
      let MenhirCell0_return_type (_menhir_stack, r) = _menhir_stack in
      let MenhirCell0_RPAREN (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_comma_list_formal_ (_menhir_stack, _, fl) = _menhir_stack in
      let MenhirCell0_LPAREN (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_generics (_menhir_stack, _, g) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _, f, _, _) = _menhir_stack in
      let MenhirCell1_FN (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_021 _endpos_b_ _startpos__1_ b f fl g o r in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_run_196 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_WHILE, _menhir_box_prog) _menhir_cell1_expr__false__ -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_expr__false__ (_menhir_stack, _, e, _, _) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_032 b e in
      _menhir_goto_expr_with_block_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_goto_expr_with_block_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_029 _endpos_e_ _startpos_e_ e in
      _menhir_goto_expr_with_block _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_goto_expr_with_block : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState049 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState171 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState168 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState156 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState152 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState134 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_226 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | STAR ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_197 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | RETURN ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | NOT ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | LOOP ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | LET ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | LBRA ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | IF ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState226
      | CONSTANT _v_1 ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState226
      | BREAK ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | AMP ->
          let _menhir_stack = MenhirCell1_expr_with_block (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState226
      | BARBAR | DIV | DOT | EQ | EQEQ | GE | GT | LE | LT | NEQ | PERCENT | PLUS | RBRA ->
          let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_028 e in
          _menhir_goto_expr__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr__true__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState049 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_184 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_105 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_228 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRA ->
          let e = _v in
          let _v = _menhir_action_115 e in
          _menhir_goto_nonempty_stmts _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_085 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_STAR (_menhir_stack, _startpos) in
      let _menhir_s = MenhirState085 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_090 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState090 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_092 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState092 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_096 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState096 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_098 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_MINUS (_menhir_stack, _startpos) in
      let _menhir_s = MenhirState098 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_100 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState100 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_102 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState102 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_104 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState104 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_106 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState106 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_108 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState108 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_110 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell0_EQ (_menhir_stack, _endpos) in
      let _menhir_s = MenhirState110 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_087 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState087 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_094 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState094 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_112 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState112 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_114 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell0_AMPAMP (_menhir_stack, _startpos) in
      let _menhir_s = MenhirState114 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RETURN ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NOT ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LOOP ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRA ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CONSTANT _v ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BREAK ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMPAMP ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_217 : type  ttv_stack. (((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_cell0_EQ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let MenhirCell0_EQ (_menhir_stack, _) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_119 e in
          _menhir_goto_option___anonymous_9_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_189 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (e, _endpos__3_) = (_v, _endpos_0) in
          let _v = _menhir_action_064 e in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _startpos__1_ _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_187 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_082 e in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_186 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_RETURN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos__1_, _) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_090 e in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_185 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_NOT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_NOT (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_c_, c) = (_endpos, _v) in
          let _v = _menhir_action_081 c in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_184 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_080 e in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_182 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (e, _endpos__3_) = (_v, _endpos_0) in
          let _v = _menhir_action_093 e in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _startpos__1_ _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_128 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ident as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRA ->
          let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _, _) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_094 e id in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_field (_menhir_stack, _menhir_s, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v_0 ->
                  _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState122
              | RBRA ->
                  let _v_1 = _menhir_action_008 () in
                  _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
              | _ ->
                  _eRR ())
          | RBRA ->
              let x = _v in
              let _v = _menhir_action_009 x in
              _menhir_goto_comma_list_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_123 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_field -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_field (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_010 l x in
      _menhir_goto_comma_list_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list_field_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState068 ->
          _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState120 ->
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState122 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_129 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_DUMMY, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LBRA -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_LBRA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
      let MenhirCell1_DUMMY (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos__5_, fl) = (_endpos, _v) in
      let _v = _menhir_action_059 fl id in
      _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__5_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_124 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LBRA -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_LBRA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _startpos_id_, _) = _menhir_stack in
      let (_endpos__5_, fl) = (_endpos, _v) in
      let _v = _menhir_action_088 fl id in
      _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__5_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_run_127 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
          let MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_084 _endpos_e_ _startpos__1_ e mut in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_126 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
          let MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e_, e) = (_endpos, _v) in
          let _v = _menhir_action_083 e mut in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_115 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_AMPAMP as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell0_AMPAMP (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, c1, _startpos_c1_, _) = _menhir_stack in
          let (_endpos_c2_, c2) = (_endpos, _v) in
          let _v = _menhir_action_077 c1 c2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c2_ _startpos_c1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_113 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, c1, _startpos_c1_, _) = _menhir_stack in
          let (_endpos_c2_, c2) = (_endpos, _v) in
          let _v = _menhir_action_078 c1 c2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c2_ _startpos_c1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_111 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_EQ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell0_EQ (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_079 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_109 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_071 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_107 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_076 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_105 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_075 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_103 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_074 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_101 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_073 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_099 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PLUS | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell0_MINUS (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_067 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_097 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_072 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_095 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_069 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_093 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_070 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_091 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PLUS | RBRA | RPAREN | SEMICOLON ->
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_066 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_086 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ _menhir_cell0_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP | BARBAR | COMMA | DIV | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let MenhirCell0_STAR (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_068 e1 e2 in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_084 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_098 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_106 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQEQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | IDENT _v_0 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState116
          | CONSTANT _v_1 ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState116
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
          | RPAREN ->
              let _v_2 = _menhir_action_005 () in
              _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2
          | _ ->
              _eRR ())
      | BARBAR ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AMPAMP ->
          let _menhir_stack = MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let e = _v in
          let _v = _menhir_action_006 e in
          _menhir_goto_comma_list_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_117 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e, _, _) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_007 e l in
      _menhir_goto_comma_list_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState138 ->
          _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState079 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState116 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_139 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LPAREN -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_LPAREN (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _startpos_id_, _) = _menhir_stack in
      let (_endpos__4_, el) = (_endpos, _v) in
      let _v = _menhir_action_063 el id in
      _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__4_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_run_118 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_ident _menhir_cell0_LPAREN -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_LPAREN (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _startpos_id_, _) = _menhir_stack in
      let (_endpos__4_, el) = (_endpos, _v) in
      let _v = _menhir_action_092 el id in
      _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__4_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_run_143 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_026 e in
      _menhir_goto_expr__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_083 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_028 e in
      _menhir_goto_expr__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_180 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_block_expr _menhir_cell0_ELSE -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell0_ELSE (_menhir_stack, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_022 b in
      _menhir_goto_else_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _tok
  
  and _menhir_goto_else_expr : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_block_expr -> _ -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _tok ->
      let MenhirCell1_block_expr (_menhir_stack, _, b1, _, _) = _menhir_stack in
      let MenhirCell1_expr__false__ (_menhir_stack, _, e, _, _) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_e_inlined1_, _startpos_e_inlined1_, e_inlined1) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_098 _endpos_e_inlined1_ _startpos_e_inlined1_ b1 e e_inlined1 in
      _menhir_goto_if_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_inlined1_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_goto_if_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState178 ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState049 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState197 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState052 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState060 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState171 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState064 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState168 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState166 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState158 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState156 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState152 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState134 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState138 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState070 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState116 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState112 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState110 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState108 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState106 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState104 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState098 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState094 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState092 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState085 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState079 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_179 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_block_expr _menhir_cell0_ELSE -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell0_ELSE (_menhir_stack, _startpos__1_) = _menhir_stack in
      let (_endpos_e_, e) = (_endpos, _v) in
      let _v = _menhir_action_023 e in
      _menhir_goto_else_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _tok
  
  and _menhir_run_077 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_033 e in
      _menhir_goto_expr_with_block_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_177 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr__false__ as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_block_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_ELSE (_menhir_stack, _startpos) in
          let _menhir_s = MenhirState178 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AMP | AMPAMP | BARBAR | BREAK | COMMA | CONSTANT _ | DIV | DOT | EQ | EQEQ | GE | GT | IDENT _ | IF | LBRA | LE | LET | LOOP | LPAREN | LT | MINUS | NEQ | NOT | PERCENT | PLUS | RBRA | RETURN | RPAREN | SEMICOLON | STAR | WHILE ->
          let _v = _menhir_action_024 () in
          _menhir_goto_else_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _endpos _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_089 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_030 e in
      _menhir_goto_expr_with_block_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_063 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LOOP -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_LOOP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_e_, e) = (_endpos, _v) in
      let _v = _menhir_action_031 e in
      _menhir_goto_expr_with_block_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_229 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SEMICOLON -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_111 b in
      _menhir_goto_nonempty_stmts _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_225 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr_without_block_true__ _menhir_cell0_SEMICOLON -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_SEMICOLON (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_expr_without_block_true__ (_menhir_stack, _menhir_s, e, _, _) = _menhir_stack in
      let b = _v in
      let _v = _menhir_action_113 b e in
      _menhir_goto_nonempty_stmts _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_214 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP, _menhir_box_prog) _menhir_cell1_mutornot -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
      let MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_131 mut ty in
      _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_213 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_mutornot -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
      let MenhirCell1_AMP (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_130 mut ty in
      _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_206 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let id = _v in
      let _v = _menhir_action_126 id in
      _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_207 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_127 () in
      _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_208 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_128 () in
      _menhir_goto_typ___anonymous_2___anonymous_3___anonymous_4_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_209 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState209
      | AMP | AMPAMP | BOOL | I32 | IDENT _ | LPAREN ->
          let _v = _menhir_action_110 () in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState209 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_210 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState210
      | IDENT _v_0 ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState210
      | I32 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState210
      | BOOL ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState210
      | AMPAMP ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState210
      | AMP ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState210
      | _ ->
          _eRR ()
  
  and _menhir_run_211 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState211
      | AMP | AMPAMP | BOOL | I32 | IDENT _ | LPAREN ->
          let _v = _menhir_action_110 () in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState211 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_199 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LET as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState199
      | _ ->
          _eRR ()
  
  and _menhir_run_029 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_lifetime as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState029
      | IDENT _v_0 ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState029
      | I32 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState029
      | BOOL ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState029
      | AMPAMP ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState029
      | AMP ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState029
      | _ ->
          _eRR ()
  
  and _menhir_run_020 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      let _menhir_s = MenhirState020 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | COMMA | LBRA | RBRA | RPAREN | WHERE ->
          let _v = _menhir_action_105 () in
          _menhir_goto_loption___anonymous_1_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LIFETIME _v ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState004
      | GT ->
          let _v = _menhir_action_014 () in
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_009 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LT (_menhir_stack, _menhir_s) = _menhir_stack in
      let g = _v in
      let _v = _menhir_action_106 g in
      _menhir_goto_loption___anonymous_1_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_loption___anonymous_1_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let g = _v in
      let _v = _menhir_action_096 g in
      _menhir_goto_generics _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_generics : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState238 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState020 ->
          _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState003 ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_239 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT, _menhir_box_prog) _menhir_cell1_ident as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_generics (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRA ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LBRA (_menhir_stack, _startpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState240
          | RBRA ->
              let _v_1 = _menhir_action_017 () in
              _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_021 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id, _, _) = _menhir_stack in
      let gen = _v in
      let _v = _menhir_action_132 gen id in
      _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_012 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_generics (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LPAREN (_menhir_stack, _startpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState013
          | RPAREN ->
              let _v_0 = _menhir_action_011 () in
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState013
          | IDENT _ ->
              let _v_1 = _menhir_action_110 () in
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState013 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_036 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FN, _menhir_box_prog) _menhir_cell1_ident, _menhir_box_prog) _menhir_cell1_generics _menhir_cell0_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_comma_list_formal_ (_menhir_stack, _menhir_s, _v) in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell0_RPAREN (_menhir_stack, _endpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState038 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | I32 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LBRA | WHERE ->
          let _v = _menhir_action_122 () in
          _menhir_goto_return_type _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_133 () in
      _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_023 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_134 () in
      _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | DUMMY ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_DUMMY (_menhir_stack, _startpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState025
          | AMP | AMPAMP | BOOL | I32 | IDENT _ | LPAREN ->
              let _v = _menhir_action_110 () in
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState025 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_026 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP _menhir_cell0_DUMMY as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | IDENT _v_0 ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState026
      | I32 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | BOOL ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | AMPAMP ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | AMP ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState026
      | _ ->
          _eRR ()
  
  and _menhir_run_027 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState027 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LIFETIME _v ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_mutornot (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState015
      | _ ->
          _eRR ()
  
  and _menhir_run_081 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_e_, _startpos_e_, e) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_027 e in
      _menhir_goto_expr__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_042 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lifetime (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState043 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LIFETIME _v ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_028 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lifetime (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | MUT ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState028
      | AMP | AMPAMP | BOOL | I32 | IDENT _ | LPAREN ->
          let _v_0 = _menhir_action_110 () in
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState028 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_006 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_lifetime (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LIFETIME _v_0 ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState007
          | GT ->
              let _v_1 = _menhir_action_014 () in
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | _ ->
              _eRR ())
      | GT ->
          let x = _v in
          let _v = _menhir_action_015 x in
          _menhir_goto_comma_list_lifetime_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_008 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_lifetime -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_lifetime (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_016 l x in
      _menhir_goto_comma_list_lifetime_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list_lifetime_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState004 ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState007 ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_032 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_mutornot, _menhir_box_prog) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
      let MenhirCell1_mutornot (_menhir_stack, _menhir_s, mut) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_095 id mut ty in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_formal (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUT ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState034
          | RPAREN ->
              let _v_0 = _menhir_action_011 () in
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
          | IDENT _ ->
              let _v_1 = _menhir_action_110 () in
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState034 _tok
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_012 x in
          _menhir_goto_comma_list_formal_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_035 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_formal -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_formal (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_013 l x in
      _menhir_goto_comma_list_formal_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_comma_list_formal_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState013 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState034 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_031 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_AMPAMP _menhir_cell0_DUMMY, _menhir_box_prog) _menhir_cell1_mutornot -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
      let MenhirCell0_DUMMY (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_AMPAMP (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_137 mut ty in
      _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_030 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_AMP, _menhir_box_prog) _menhir_cell1_lifetime, _menhir_box_prog) _menhir_cell1_mutornot -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_mutornot (_menhir_stack, _, mut) = _menhir_stack in
      let MenhirCell1_lifetime (_menhir_stack, _, l) = _menhir_stack in
      let MenhirCell1_AMP (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_136 l mut ty in
      _menhir_goto_typ_false__lifetime_generics_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_238 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_option_DERIVECOPY_ _menhir_cell0_STRUCT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | LT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState238
      | LBRA ->
          let _menhir_s = MenhirState238 in
          let _v = _menhir_action_105 () in
          _menhir_goto_loption___anonymous_1_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_200 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_mutornot (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let _endpos__4_ = _endpos_0 in
          let _v = _menhir_action_101 _endpos__4_ _startpos__1_ in
          _menhir_goto_let_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | EQ ->
          let _endpos_1 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_mutornot (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let _endpos__4_ = _endpos_1 in
          let _v = _menhir_action_100 _endpos__4_ _startpos__1_ in
          _menhir_goto_let_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | COLON ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _menhir_s = MenhirState203 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | I32 ->
              _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL ->
              _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_146 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr__false__, _menhir_box_prog) _menhir_cell1_DOT -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_DOT (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_expr__false__ (_menhir_stack, _menhir_s, e, _startpos_e_, _) = _menhir_stack in
      let (_endpos_id_, id) = (_endpos, _v) in
      let _v = _menhir_action_057 e id in
      _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_137 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LPAREN (_menhir_stack, _startpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | IDENT _v_1 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState138
          | CONSTANT _v_2 ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState138
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState138
          | RPAREN ->
              let _v_3 = _menhir_action_005 () in
              _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
          | _ ->
              _eRR ())
      | AMPAMP | BARBAR | DIV | DOT | EQ | EQEQ | GE | GT | LBRA | LE | LT | MINUS | NEQ | PERCENT | PLUS | STAR ->
          let (_endpos_id_, _startpos_id_, id) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_056 id in
          _menhir_goto_expr_without_block__false__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_id_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_088 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr__true__ -> _ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_expr__true__ (_menhir_stack, _menhir_s, e, _startpos_e_, _) = _menhir_stack in
      let (_endpos_id_, id) = (_endpos, _v) in
      let _v = _menhir_action_086 e id in
      _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_078 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LPAREN (_menhir_stack, _startpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | IDENT _v_1 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState079
          | CONSTANT _v_2 ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState079
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
          | RPAREN ->
              let _v_3 = _menhir_action_005 () in
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
          | _ ->
              _eRR ())
      | LBRA ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _startpos_4 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LBRA (_menhir_stack, _startpos_4) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_5 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState120
          | RBRA ->
              let _v_6 = _menhir_action_008 () in
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _v_6
          | _ ->
              _eRR ())
      | AMPAMP | BARBAR | COMMA | DIV | DOT | EQ | EQEQ | GE | GT | LE | LT | MINUS | NEQ | PERCENT | PLUS | RBRA | RPAREN | SEMICOLON | STAR ->
          let (_endpos_id_, _startpos_id_, id) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_085 id in
          _menhir_goto_expr_without_block__true__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_id_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_069 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState070 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WHILE ->
              _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RETURN ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NOT ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LOOP ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRA ->
              _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CONSTANT _v ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BREAK ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_067 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_DUMMY as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | LBRA ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LBRA (_menhir_stack, _startpos_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_1 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState068
          | RBRA ->
              let _v_2 = _menhir_action_008 () in
              _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_016 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_mutornot as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState017 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | I32 ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMPAMP ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_003 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | LT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState003
      | LPAREN ->
          let _menhir_s = MenhirState003 in
          let _v = _menhir_action_105 () in
          _menhir_goto_loption___anonymous_1_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | FN ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | DERIVECOPY ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | EOF ->
          let _v = _menhir_action_103 () in
          _menhir_run_249 _menhir_stack _v
      | STRUCT ->
          let _menhir_s = MenhirState000 in
          let _v = _menhir_action_116 () in
          _menhir_goto_option_DERIVECOPY_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _endpos _v _menhir_s _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
