
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | RPAREN
  | RARROW
  | LPAREN
  | EOF
  | DISJ
  | CONJ

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.set)
