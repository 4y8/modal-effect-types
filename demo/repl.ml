let repl_from_file f =
  let ic = open_in f in
  let lb = Lexing.from_channel ic in
  let p =
      try
        Core.Parser.file Core.Lexer.lexer lb
      with
        _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
  close_in ic;
  let p, tctx = Core.Type.(check_prog init_ctx p) in
  let ectx = ref (Core.Eval.build_stdlib_map tctx) in
  Core.Eval.eval_prog ectx p;
  let infer =
    match Core.Eval.VMap.find (List.assoc "infer_top_level" tctx.id) !ectx with
    | VClo f -> f
    | _ -> failwith "internal error" in
  let rec loop () =
    print_string "> ";
    flush stdout;
    let lb = Lexing.from_channel stdin in
    let p =
      try
        Parser.prog Lexer.lexer lb
      with
        _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in

    begin
      try Format.printf "%a@." Core.Eval.pp_value (infer p)
      with
        Core.Eval.Fail -> ()
    end;
    loop ()
  in loop ()

let _ =
  Arg.parse [] repl_from_file ""
