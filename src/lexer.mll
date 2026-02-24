{
  open Parser

  let ident_tbl = Hashtbl.create 63

  let _ = List.iter (fun (k, v) -> Hashtbl.add ident_tbl k v)
    ["handle", HANDLE; "do", DO; "with", WITH; "return", RETURN;
     "effect", EFFECT; "fun", FUN; "data", DATA; "if", IF; "then", THEN;
     "else", ELSE; "forall", FORALL; "case", CASE; "of", OF; "_", WILDCARD]
}

let digit = ['0'-'9']
let id = ['a'-'z'] | ['A'-'Z'] | '_'
let ident = id (digit | id)*

let blank_line = [' ' '\t' '\r']* ("//" [^'\n']*)? '\n'

rule lexer = parse
  | eof { EOF }
  | [' ' '\t' '\r'] { lexer lexbuf }
  | blank_line { Lexing.new_line lexbuf; lexer lexbuf }
  | ident as s
    { match Hashtbl.find_opt ident_tbl s with
      | None -> IDENT s | Some t -> t }
  | '<' { LANGLE }
  | '>' { RANGLE }
  | '[' { LSQUARE }
  | ']' { RSQUARE }
  | '{' { LCURLY }
  | '}' { RCURLY }
  | '(' { LPAR }
  | ')' { RPAR }
  | '@' { AT }
  | ',' { COMMA }
  | '|' { PIPE }
  | "->" { ARROW }
  | "=>" { DARROW }
  | '.' { DOT }
  | ':' { DCOL }
  | '=' { EQU }
  | '@' { AT }
  | '1' { ONE }
{
}
