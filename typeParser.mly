%{
    open Ast
%}

%token <string>VAR
%token LPAREN
%token RPAREN
%token RARROW
%token CONJ
%token EOF

%start <Ast.set> prog

%%

prog:
    | e = set; EOF { e }
    ;

set:
  | LPAREN; t1 = set; RARROW; t2 = set; RPAREN { Arrow(t1,t2) }
  | t = VAR { Set t }
  | LPAREN; t1 = set; CONJ; t2 = set; RPAREN {Conj(t1,t2)}
;
