open Core

let _ =
  let rec loop ctx =
    print_string "> ";
    flush stdout;
    try
      let lb = Lexing.from_channel stdin in
      let prompt =
        try
          Parser.subtype Lexer.lexer lb
        with
          _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
      match prompt with
      | Either.Right d ->
        let _, ctx = Type.check_decl ([], ctx) d in
        loop ctx
      | Either.Left (a, b) ->
        let a, b = Type.(fst @@ check_type a ctx, fst @@ check_type b ctx) in
        let m = Subtype.check a b ctx.gamma in
        Format.printf "%a@." Pprint.expr m;
        loop ctx
    with
      Error.Exit ->
      flush stderr;
      loop ctx
  in loop Type.init_ctx
