{
    open Parser
}

let white = [' ']+
let letter = ['a'-'z' 'A'-'Z']
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
    | "Λ-intro" { WEDGE }
    | "Λ" { CONJ }
    | "Λ-elim0" { RMWEDGE0 }
    | "Λ-elim1" { RMWEDGE1 }
    | eof { EOF }
