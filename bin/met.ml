open Core.Syntax
open Core.Type

let show_ast = ref false
let eval = ref false
let launch_repl = ref true

let repl () =
  let lb = Lexing.from_channel stdin in
  let eval_ctx = ref Core.Eval.stdlib in
  let rec loop ctx =
    try
      print_string "# ";
      flush stdout;
      let tl =
        try
          Core.Parser.top_level Core.Lexer.lexer lb
        with
          _ ->
          Core.Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb))
      in
      match tl with
      | TLExpr m ->
        let _, a = infer ctx m ([], None) in
        let v = Core.Eval.eval eval_ctx [] m in
        Format.printf "- : %a = %a@." Core.Pprint.ty a Core.Eval.pp_value v;
        loop ctx
      | TLDecl d ->
        let ctx = match d with
          | x, SDFun m ->
            let a, ctx =
              match List.assoc_opt x ctx.id with
              | Some v ->
                let _, a, _ = Core.Context.(get_type_context ctx.gamma v) in
                a, ctx
              | None ->
                let _, a = infer ctx m ([], None) in
                let ctx, _ = Core.Context.fresh_var ctx x a in
                a, ctx
            in
            let v = Core.Eval.eval eval_ctx [] m in
            eval_ctx := Core.Eval.(SMap.add x v !eval_ctx);
            Format.printf "val %s : %a = %a@." x Core.Pprint.ty a
              Core.Eval.pp_value v;
            ctx
          | _ -> fst (check_decl (ctx, []) (d, None))
        in
        loop ctx
    with
    | Core.Error.Exit ->
      let fd = Unix.descr_of_in_channel stdin in
      let buf = Bytes.create 4096 in
      let rec discard_all () =
        let ready, _, _ = Unix.select [fd] [] [] 0.0 in
        match ready with
        | [] -> ()
        | _ ->
          let n = Unix.read fd buf 0 4096 in
          if n = 0 then ()
          else discard_all ()
      in
      discard_all ();
      loop ctx
  in
  loop init_ctx

let read_file f =
  try
    launch_repl := false;
    let ic = open_in f in
    let lb = Lexing.from_channel ic in
    Lexing.set_filename lb f;
    let p =
      try
        Core.Parser.file Core.Lexer.lexer lb
      with
        _ ->
        Core.Error.error_str_lexbuf lb
          (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
    if !show_ast then
      List.iter (fun ((_, d), _) -> print_endline @@ show_surface_decl d) p;
    let p = check_prog p in
    if !eval then (
      ignore (Core.Eval.eval_prog p)
    );
    close_in ic
  with
  | Core.Error.Exit -> exit 1

let () =
  let spec_list = [("--show-ast", Arg.Set show_ast, "Print AST of the program");
                   ("--eval", Arg.Set eval, "Evaluate the program (needs a main function)")] in
  Arg.parse spec_list read_file "";
  if !launch_repl then
    repl ()
