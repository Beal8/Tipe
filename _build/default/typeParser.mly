%{
    open Ast
%}

%token <string>VAR
%token LPAREN
%token RPAREN
%token RARROW
%token CONJ
%token DISJ
%token EOF

%start <Ast.set> prog

%%

prog:
    | t = set; EOF { t }
    ;

set:
  | LPAREN; t1 = set; RARROW; t2 = set; RPAREN { Arrow(t1,t2) }
  | t = VAR { Set t }
  | LPAREN; t1 = set; CONJ; t2 = set; RPAREN { Conj(t1,t2) }
  | LPAREN; t1 = set; DISJ; t2 = set; RPAREN { Disj(t1,t2) }
;
