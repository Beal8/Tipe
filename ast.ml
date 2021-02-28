type expr =
  |Var of string
  |Lam of string * expr
  |App of expr * expr
  |Ann of expr * set
  |Hole of int
  |Wedge of expr * expr
  |Rm_wedge0 of expr
  |Rm_wedge1 of expr

and set =
  |Arrow of set * set
  |Set of string
  |Conj of set * set;;
