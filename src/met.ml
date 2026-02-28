open Syntax
open Type


let show_ast = ref false
let repl = ref true

let read_file f =
  repl := false;
  let ic = open_in f in
  let lb = Lexing.from_channel ic in
  let p =
      try
        Parser.file Lexer.lexer lb
      with
        _ ->
          Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
  if !show_ast then
    List.iter (fun ((_, d), _) -> print_endline @@ show_surface_decl d) p;
  ignore (Eval.eval_prog (check_prog p));
  close_in ic

let () =
  let rec loop s =
    print_string "> ";
    let s = s ^ (read_line ()) in
    let lb = Lexing.from_string s in
    let p =
      try
        Parser.file Lexer.lexer lb
      with
        _ ->
          Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb))
    in
    if !show_ast then
      List.iter (fun ((_, d), _) -> print_endline @@ show_surface_decl d) p;
    ignore (check_prog p);
    loop s
  in
  let spec_list = [("--show-ast", Arg.Set show_ast, "Print AST of the program")] in
  Arg.parse spec_list read_file "";
  if !repl then
    ignore (loop "")
