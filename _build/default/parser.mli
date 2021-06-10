
(* The type of tokens. *)

type token = 
  | WEDGE
  | VAR of (string)
  | RPAREN
  | RMWEDGE1
  | RMWEDGE0
  | RMBOTTOM
  | RARROW
  | NEG
  | LPAREN
  | LAM
  | HOLE
  | EOF
  | DOUBLEDOT
  | DOT
  | DJINTRO1
  | DJINTRO0
  | DJELIM
  | DISJ
  | CONJ
  | BOTTOM

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val set_only: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.set)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
