{
  open Parser

  let error = Core.Error.error_str_lexbuf
}

let digit = ['0'-'9']
let alpha = ['A'-'Z'] | ['a'-'z'] | '_'
let id = digit | alpha | ''' | '.'
let ident = alpha id*

let blank_line = [' ' '\t' '\r']* ("--" [^'\n']*)? '\n'

rule lexer = parse
  | [' ' '\t' '\r'] { lexer lexbuf }
  | blank_line { Lexing.new_line lexbuf; lexer lexbuf }
  | "fun" { FUN }
  | ident as s { IDENT s }
  | '(' { LPAR }
  | ')' { RPAR }
  | "->" { ARROW }
  | "=>" { DARROW }
  | ':' { DCOL }
  | '*' { TYPE }
  | ";;" { END }
  | '@' { AT }
  | '?' { HOLE }
  | _ as c { error lexbuf (Printf.sprintf "Unknown character : %c" c) }
