type expr =
  |Var of string
  |Lam of string * expr
  |App of expr * expr
  |Ann of expr * set
  |Hole of int
  |Wedge of expr * expr
  |Rm_wedge0 of expr
  |Rm_wedge1 of expr
  |Dj_intro0 of expr
  |Dj_intro1 of expr
  |Dj_elim of expr * expr * expr
  |Bot_elim of expr

and set =
  |Arrow of set * set
  |Set of string
  |Conj of set * set
  |Disj of set * set
  |Bottom;;
