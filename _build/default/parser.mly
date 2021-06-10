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
%token DJINTRO0
%token DJINTRO1
%token DJELIM
%token DISJ
%token RMBOTTOM
%token BOTTOM
%token NEG
%token EOF

%start <Ast.expr> prog

%start <Ast.set> set_only

%%

prog:
  | e = expr; EOF { e }
;

set_only:
  | t = set; EOF { t }
;

expr:
  | LPAREN; LAM; x = VAR; DOT; e = expr; RPAREN { Lam(x,e) }
  | LPAREN; e1 = expr; DOUBLEDOT ; t = set; RPAREN { Ann(e1,t) }
  | x = VAR { Var x }
  | LPAREN; DJELIM; e1 = expr; e2 = expr; e3 = expr; RPAREN { Dj_elim (e1,e2,e3) }
  | LPAREN; e1 = expr; e2 = expr; RPAREN { App(e1,e2) }
  | HOLE { Hole (-1) }
  | LPAREN; HOLE; RPAREN{ Hole (-1) }
  | LPAREN; e1 = expr; WEDGE; e2 = expr; RPAREN { Wedge(e1,e2) }
  | LPAREN; RMWEDGE0; e = expr; RPAREN { Rm_wedge0 e}
  | LPAREN; RMWEDGE1; e = expr; RPAREN { Rm_wedge1 e}
  | LPAREN; DJINTRO0; e = expr; RPAREN { Dj_intro0 e }
  | LPAREN; DJINTRO1; e = expr; RPAREN { Dj_intro1 e }
  | LPAREN; RMBOTTOM; e = expr; RPAREN { Bot_elim e }
;

set:
  | LPAREN; t1 = set; RARROW; t2 = set; RPAREN { Arrow(t1,t2) }
  | LPAREN; t1 = set; CONJ; t2 = set; RPAREN { Conj(t1,t2) }
  | t = VAR { Set t }
  | LPAREN; t1 = set; DISJ; t2 = set; RPAREN { Disj(t1,t2) }
  | BOTTOM { Bottom }
  | LPAREN; NEG; t = set; RPAREN { Arrow(t,Bottom) }
  ;
