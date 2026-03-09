open Core

let _ =
  let rec loop () =
    print_string "> ";
    flush stdout;
    let lb = Lexing.from_channel stdin in
    let a, b =
      try
        Parser.subtype Lexer.lexer lb
      with
        _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
    let a, b = Type.(check_type init_ctx a, check_type init_ctx b) in
    let m = Subtype.check a b Type.init_ctx.gamma in
    Format.printf "%a@." Pprint.expr m;
    loop ()
  in loop ()
