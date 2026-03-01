open Core.Syntax
open Core.Type

let show_ast = ref false

let read_file f =
  let ic = open_in f in
  let lb = Lexing.from_channel ic in
  let p =
      try
        Core.Parser.file Core.Lexer.lexer lb
      with
        _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
  if !show_ast then
    List.iter (fun ((_, d), _) -> print_endline @@ show_surface_decl d) p;
  ignore (Core.Eval.eval_prog (check_prog p));
  close_in ic

let () =
  let spec_list = [("--show-ast", Arg.Set show_ast, "Print AST of the program")] in
  Arg.parse spec_list read_file ""
