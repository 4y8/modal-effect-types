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
  let ectx = ref Core.Eval.stdlib in
  let p, _ = Core.Type.(check_prog init_ctx p) in
  let p = List.rev p in
  let p = Core.TT.erase_types_prog p in 
  Core.Eval.eval_prog ectx p;
  let infer =
    match Core.Eval.SMap.find "infer_top_level" !ectx with
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
