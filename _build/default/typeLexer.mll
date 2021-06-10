{
    open TypeParser
}

let white = [' ']+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read =
    parse
    | white { read lexbuf}
    | "->" {RARROW}
    | "("   { LPAREN }
    | ")"   { RPAREN }
    | id { VAR (Lexing.lexeme lexbuf) }
    | "∧" { CONJ }
    | "∨" { DISJ }
    | eof { EOF }
