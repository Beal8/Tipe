%{
    open Ast
%}

%token <string> VAR
%token LPAREN
%token RPAREN
%token RARROW
%token DOT 
%token DOUBLEDOT
%token LAM
%token HOLE
%token WEDGE
%token CONJ
%token RMWEDGE0
%token RMWEDGE1
%token EOF

%start <Ast.expr> prog

%%

prog:
  | e = expr; EOF { e }
    ;

expr:
  | LPAREN; LAM; x = VAR; DOT; e = expr; RPAREN { Lam(x,e) }
  | LPAREN; e1 = expr; DOUBLEDOT ; t = set; RPAREN { Ann(e1,t) }
  | x = VAR { Var x }
  | LPAREN; e1 = expr; e2 = expr; RPAREN { App(e1,e2) }
  | HOLE { Hole (-1) }
  | LPAREN; HOLE; RPAREN{ Hole (-1) }
  | LPAREN; e1 = expr; WEDGE; e2 = expr; RPAREN { Wedge(e1,e2) }
  | LPAREN; RMWEDGE0; e = expr; RPAREN { Rm_wedge0 e}
  | LPAREN; RMWEDGE1; e = expr; RPAREN { Rm_wedge1 e}
;

set:
  | LPAREN; t1 = set; RARROW; t2 = set; RPAREN { Arrow(t1,t2) }
  | LPAREN; t1 = set; CONJ; t2 = set; RPAREN {Conj(t1,t2)}
  | t = VAR { Set t }
  ;
