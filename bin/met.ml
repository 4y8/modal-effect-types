open Core.Syntax
open Core.Type

let eval = ref false
let launch_repl = ref true
let verbose = ref false

let open_file f tctx ectx =
  let open Core.Context in
  let check_decl (p, ctx) = function
    | (x, SDFun m), _ ->
      begin match List.assoc_opt x ctx.id with
        | Some v ->
          let (_, a, _), _ = get_type_context v ctx in
          let (_, m), _ =
            try
              Core.Frost.finfer (Check a) m ctx
            with
            | Core.Frost.UnifyError (a, b) -> Core.Errors.cannot_unify None a b
          in
          (v, m) :: p, ctx
        | None ->
          let (a, m), ctx' = Core.Frost.finfer (Infer Ghost) m ctx in
          let a = Core.Frost.subst_suffix ctx'.gamma a in
          if !verbose then
            Format.printf "%s : %a@." x Core.Pprint.ty a;
          let v, ctx = fresh_var x a ctx in
          (v, m) :: p, ctx
      end
    | d -> check_decl (p, ctx) d
  in
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
    let p, tctx = List.fold_left check_decl ([], tctx) p in
    if !eval || !launch_repl then
      Core.Eval.eval_prog ectx p;
    close_in ic;
    tctx
  with
  | Core.Error.Exit -> exit 1

let repl () =
  let lb = Lexing.from_channel stdin in
  let ectx = ref (Core.Eval.build_stdlib_map init_ctx) in
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
        let (a, m), ctx' =
            Core.Frost.finfer (Infer Ghost) m ctx
        in
        let a = Core.Frost.subst_suffix ctx'.gamma a in
        let v = Core.Eval.eval ectx m in
        Format.printf "- : %a = %a@." Core.Pprint.ty a Core.Eval.pp_value v;
        loop ctx
      | TLOpen f -> loop (open_file f ctx ectx)
      | TLDecl d ->
        let ctx = match d with
          | x, SDFun m ->
            let a, v, m, ctx =
              match List.assoc_opt x ctx.id with
              | Some v ->
                let (_, a, _), _ = Core.Context.get_type_context v ctx in
                let (_, m), _ = Core.Frost.finfer (Check a) m ctx in
                a, v, m, ctx
              | None ->
                let (a, m), ctx' = Core.Frost.finfer (Infer Ghost) m ctx in
                let a = Core.Frost.subst_suffix ctx'.gamma a in
                let v, ctx = Core.Context.fresh_var x a ctx in
                a, v, m, ctx
            in
            let vf = Core.Eval.eval ectx m in
            ectx := Core.Eval.(VMap.add v vf !ectx);
            Format.printf "val %s : %a = %a@." x Core.Pprint.ty a
              Core.Eval.pp_value vf;
            ctx
          | _ -> snd (check_decl ([], ctx) (d, None))
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
  let ectx = ref (Core.Eval.build_stdlib_map init_ctx) in
  let tctx = open_file f init_ctx ectx in
  if !eval then
    match Core.Eval.VMap.find Core.Context.(List.assoc "main" tctx.id)
            !ectx with
    | VClo f -> ignore (f (VCon ("Unit", [])))
    | _ -> failwith "main should be a function"

let () =
  let spec_list =
    [ ("--eval", Arg.Set eval, "Evaluate the program (needs a main function)")
    ; ("--verbose", Arg.Set verbose, "")]
  in
  Format.set_margin 80;
  Arg.parse spec_list read_file "";
  if !launch_repl then
    ignore (repl ())
