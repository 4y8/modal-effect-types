{
  open Parser

  let ident_tbl = Hashtbl.create 63

  let error = Error.error_str_lexbuf

  let _ = List.iter (fun (k, v) -> Hashtbl.add ident_tbl k v)
    ["handle", HANDLE; "do", DO; "with", WITH; "return", RETURN;
     "eff", EFFECT; "fun", FUN; "type", TYPE; "if", IF; "then", THEN;
     "else", ELSE; "forall", FORALL; "match", MATCH; "_", WILDCARD; "of", OF;
     "mask", MASK; "let", LET; "in", IN; "end", END; "val", VAL]
}

let digit = ['0'-'9']
let lower = ['a'-'z'] | '_'
let cap = ['A'-'Z']
let id = digit | lower | cap | ''' | '.'
let ident = lower id*
let mident = cap id*

let blank_line = [' ' '\t' '\r']* ("--" [^'\n']*)? '\n'

rule lexer = parse
  | eof { EOF }
  | [' ' '\t' '\r'] { lexer lexbuf }
  | blank_line { Lexing.new_line lexbuf; lexer lexbuf }
  | ident as s
    { match Hashtbl.find_opt ident_tbl s with
      | None -> IDENT s | Some t -> t }
  | mident as s { MIDENT s }
  | ('-'? ('0' | ['1'-'9'] digit*)) as s { INT (int_of_string s) }
  | '<' { LANGLE }
  | '>' { RANGLE }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }
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
  | ';' { SCOL }
  | '=' { EQU }
  | '@' { AT }
  | '^' { CARET }
  | ('"' [^ '"' '\\']* '"') as s { STRING s }
  | "&&" { AND }
  | "()" { UNIT }
  | _ as c { error lexbuf (Printf.sprintf "Unknown character : %c" c) }
{
  let lexer x =
  (*
  print_endline "ee";
  *)
  lexer x
}
