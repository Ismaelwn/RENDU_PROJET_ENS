
%{
  open Ast
%}

%token <Ast.constant> CONSTANT
%token <string> IDENT LIFETIME
%token STRUCT I32 BOOL FN RETURN BREAK EOF
%token IF ELSE WHILE LOOP LET MUT DERIVECOPY WHERE
%token LPAREN RPAREN LBRA RBRA
%token COMMA COLON SEMICOLON DOT ARROW
%token PLUS MINUS STAR DIV PERCENT AMP AMPAMP BARBAR NOT
%token EQ EQEQ NEQ LT LE GT GE
%token DUMMY /* Not used in the lexer */

%nonassoc RETURN block_as_expr
%right EQ
%left BARBAR
%left AMPAMP
%nonassoc EQEQ NEQ LT LE GT GE
%left MINUS PLUS
%left STAR DIV PERCENT
%nonassoc NOT uminus ustar AMP
%nonassoc DOT

%start prog

%type <Ast.decl list> prog


%%

ident:
  id=IDENT { { iloc = $sloc; id } }

mutornot:
| MUT { Mut }
| { NotMut }

comma_list(X):
|                             { [] }
| x=X                         { [x] }
| x=X COMMA l=comma_list(X)   { x::l }

paren_comma_list(X):
| xs=loption(LPAREN xs=comma_list(X) RPAREN { xs }) { xs }

%inline true_: { () }
%inline false_: DUMMY { assert false } /* never reduced */

generics:
| g=loption(LT g=comma_list(lifetime) GT { g }) { g }

%inline decl_typ: ty=typ(false_, lifetime, generics) { ty }
%inline body_typ: ty=typ({}, {}, { [] }) { ty }

decl:
| copy=DERIVECOPY? STRUCT id=ident g=generics LBRA fl=comma_list(struct_field) RBRA
   { Dstruct {
      sname = id;
      slfts = g;
      sfields = fl;
      scopy = copy = Some ();
      sloc = $sloc }
    }
| FN f=ident g=generics LPAREN fl=comma_list(formal) RPAREN r=return_type
  o=where_clause b=block_expr
   { Dfundef {
      fname = f;
      flfts = g;
      fformals = fl;
      freturn = r;
      foutlives = o;
      fbody = b;
      floc = $sloc }
    }

struct_field:
| id=ident COLON ty=decl_typ { (id, ty) }

formal:
| mut=mutornot id=ident COLON ty=decl_typ { (id, mut, ty) }

return_type:
| ARROW ty=decl_typ { ty }
|                   { Tunit }

where_clause:
| l=loption(WHERE l=comma_list(l1=lifetime COLON l2=lifetime { (l1, l2) }) { l }) { l }

%inline loc_expr(e):
| e=e { { edesc = e; eloc = $sloc; etyp = None } }

block_expr:
| e=loc_expr(LBRA sl=stmts_or_unit RBRA { Eblock sl }) { e }

stmts_or_unit:
| e=loc_expr(/* empty */ { Eunit })   { [], e }
| b=nonempty_stmts                    { b }

nonempty_stmts:
| SEMICOLON b=stmts_or_unit                               { b }
| s=let_stmt                                              { [], s }
| e=expr_without_block(true_) SEMICOLON b=stmts_or_unit   { e::fst b, snd b }
| e=expr_with_block b=nonempty_stmts                      { e::fst b, snd b }
| e=expr                                                  { [], e }

let_stmt:
| _l=LET mut=mutornot id=ident COLON ty=body_typ e=option(EQ e=expr {e}) _s=SEMICOLON
  b=stmts_or_unit
   { { edesc = Elet(id, mut, ty, e, b);
       eloc = ($startpos(_l), $endpos(_s));
       etyp = None } }
| LET mutornot ident EQ
  { Error.error $sloc "In MiniRust, all let-bindings must have explicit types." }
| LET mutornot ident SEMICOLON
  { Error.error $sloc "In MiniRust, all let-bindings must have explicit types." }

expr_(in_cond):
| e=expr_without_block(in_cond)          { e }
| e=expr_with_block  %prec block_as_expr { e }

%inline expr:
| e=expr_(true_) { e }

expr_without_block_(in_cond):
| c=CONSTANT                                       { Econst c }
| e1=expr_(in_cond) o=binop e2=expr_(in_cond)      { Ebinop (o, e1, e2) }
| c1=expr_(in_cond) AMPAMP c2=expr_(in_cond)       { Eand (c1, c2) }
| c1=expr_(in_cond) BARBAR  c2=expr_(in_cond)      { Eor  (c1, c2) }
| e1=expr_(in_cond) EQ e2=expr_(in_cond)           { Eassign (e1, e2) }
| MINUS e=expr_(in_cond) %prec uminus              { Eunop (Uneg, e) }
| NOT c=expr_(in_cond)                             { Eunop (Unot, c) }
| STAR e=expr_(in_cond) %prec ustar                { Ederef e }
| AMP mut=mutornot e=expr_(in_cond)                { Eborrow (mut, e) }
| AMPAMP mut=mutornot e=expr_(in_cond)             {
    Eborrow(NotMut,
      { edesc = Eborrow (mut, e);
        eloc = $sloc;
        etyp = None }
    )
  }
| id=ident                                         { Evar id }
| e=expr_(in_cond) DOT id=ident                    { Edot (e, id) }
| LPAREN RPAREN                                    { Eunit }
| in_cond id=ident LBRA fl=comma_list(field) RBRA  { Econstr_stru (id, fl) }
| BREAK                                            { Ebreak }
| RETURN e=expr_(in_cond)                          { Ereturn (Some e) }
| in_cond RETURN                                   { Ereturn None }
| id=ident LPAREN el=comma_list(expr) RPAREN       { Ecall (id, el) }
| LPAREN e=expr RPAREN                             { e.edesc }

expr_without_block(in_cond):
| e=loc_expr(expr_without_block_(in_cond)) { e }

expr_with_block_:
| e=block_expr                              { e.edesc }
| LOOP e=block_expr                         { Eloop e }
| WHILE e=expr_(false_) b=block_expr        { Ewhile (e, b) }
| e=if_expr                                 { e }

expr_with_block:
| e=loc_expr(expr_with_block_) { e }

if_expr:
| IF e=expr_(false_) b1=block_expr b2=loc_expr(else_expr)
    { Eif (e, b1, b2) }

else_expr:
| ELSE b=block_expr { b.edesc }
| ELSE e=if_expr    { e }
|                   { Eunit }

field:
| id=ident COLON e=expr { id, e }

%inline binop:
| PLUS    { Badd }
| MINUS   { Bsub }
| STAR    { Bmul }
| DIV     { Bdiv }
| PERCENT { Bmod }
| EQEQ    { Beqeq }
| NEQ     { Bneq }
| LT      { Blt }
| LE      { Ble }
| GT      { Bgt }
| GE      { Bge }

typ(nolft, lft, gen):
| id=IDENT gen=gen                         { Tstruct (id, gen) }
| I32                                      { Ti32 }
| BOOL                                     { Tbool }
| LPAREN RPAREN                            { Tunit }
| AMP l=lft mut=mutornot ty=typ(nolft, lft, gen)
                                           { Tborrow (l, mut, ty) }
| AMPAMP nl=nolft mut=mutornot ty=typ(nolft, lft, gen)
                                           { Tborrow (nl, NotMut, Tborrow(nl, mut, ty)) }

lifetime:
| l = LIFETIME                           { Lnamed l }

prog:
| l=decl* EOF { l }
