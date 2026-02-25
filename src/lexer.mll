{
  open Parser

  let ident_tbl = Hashtbl.create 63

  let error = Error.error_str_lexbuf

  let _ = List.iter (fun (k, v) -> Hashtbl.add ident_tbl k v)
    ["handle", HANDLE; "do", DO; "with", WITH; "return", RETURN;
     "eff", EFFECT; "fun", FUN; "type", TYPE; "if", IF; "then", THEN;
     "else", ELSE; "forall", FORALL; "match", MATCH; "_", WILDCARD;
     "mask", MASK; "let", LET; "in", IN; "inl", INL; "inr", INR; "end", END;
     "val", VAL]
}

let digit = ['0'-'9']
let id = ['a'-'z'] | ['A'-'Z'] | '_'
let ident = id (digit | id | ''')*

let blank_line = [' ' '\t' '\r']* ("//" [^'\n']*)? '\n'

rule lexer = parse
  | eof { EOF }
  | [' ' '\t' '\r'] { lexer lexbuf }
  | blank_line { Lexing.new_line lexbuf; lexer lexbuf }
  | ident as s
    { match Hashtbl.find_opt ident_tbl s with
      | None -> IDENT s | Some t -> t }
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
  | '=' { EQU }
  | '@' { AT }
  | "()" { UNIT }
  | _ as c { error lexbuf (Printf.sprintf "Unknown character : %c" c) }
{
  let lexer x =
  (*
  print_endline "ee";
  *)
  lexer x
}
