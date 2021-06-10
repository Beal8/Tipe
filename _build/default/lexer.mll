{
    open Parser
}

let white = [' ']+
let letter = ['a'-'z' 'A'-'Z' '0'-'9']
let id = letter+

rule read =
    parse
    | white { read lexbuf}
    | "?" { HOLE }
    | "λ" { LAM }
    | "." {DOT}
    | ":" {DOUBLEDOT}
    | "->" {RARROW}
    | "("   { LPAREN }
    | ")"   { RPAREN }
    | id { VAR (Lexing.lexeme lexbuf) }
    | "∧-intro" { WEDGE }
    | "∧" { CONJ }
    | "∧-elim0" { RMWEDGE0 }
    | "∧-elim1" { RMWEDGE1 }
    | "∨-intro0" { DJINTRO0 }
    | "∨-intro1" { DJINTRO1 }
    | "∨-elim" { DJELIM }
    | "∨" { DISJ }
    | "⊥" { BOTTOM }
    | "⊥-elim" { RMBOTTOM }
    | "¬" { NEG }
    | eof { EOF }
