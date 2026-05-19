open Js_of_ocaml

let unsafe_getById id f =
  let _ = (Dom_html.document##getElementById (Js.string id)) in
  Js.coerce_opt (Dom_html.document##getElementById (Js.string id))
    f (fun _ ->  assert false)

let read_string s =
  let open Core.Syntax in
  let open Core.Type in
  let open Core.Context in
  let check_decl (p, ctx) = function
    | (x, SDFun m), _ ->
      begin match List.assoc_opt x ctx.id with
        | Some v ->
          let (_, a, _), _ = get_type_context v ctx in
          let (_, m), _ =
            try
              Core.Frost.finfer (Check a) m [] ctx
            with
            | Core.Frost.UnifyError (a, b, theta) ->
              Core.Errors.cannot_unify None (Core.Frost.subst_suffix theta a)
                (Core.Frost.subst_suffix theta b)
          in
          (v, m) :: p, ctx
        | None ->
          let (a, m), ctx' = try
              Core.Frost.finfer Infer m [] ctx
            with
            | Core.Frost.UnifyError (a, b, theta) ->
              Core.Errors.cannot_unify None (Core.Frost.subst_suffix theta a)
                (Core.Frost.subst_suffix theta b)
          in
          let a = Core.Frost.subst_suffix ctx'.gamma a in
          let v, ctx = fresh_var x a ctx in
          (v, m) :: p, ctx
      end
    | d -> check_decl (p, ctx) d
  in
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  Core.Error.err_fmt := fmt;
  try
    let lb = Lexing.from_string s in
    let p =
      try
        Core.Parser.file Core.Lexer.lexer lb
      with
        _ ->
        Core.Error.error_str_lexbuf lb
          (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
    let p, tctx = List.fold_left check_decl ([], init_ctx) p in
    let p = List.rev p in
    let ectx = ref (Core.Eval.build_stdlib_map init_ctx) in
    Core.Eval.fmt_out := fmt;
    Core.Eval.eval_prog ectx p;
    List.iter (fun (x, _) ->
      let v = Core.Eval.VMap.find x !ectx in
      let t = Core.Context.get_type_context_ tctx.gamma x |> fun (_, t, _) -> t in
      Format.fprintf fmt "%s : %a = %a@." (Bindlib.name_of x) Core.Pprint.ty t Core.Eval.pp_value v) p;
    Buffer.contents buf
  with
  | Core.Error.Exit -> Buffer.contents buf

let unsafe_to_string s =
  Js.Opt.get s (fun _ -> assert false)
  |> Js.to_string

let () =
  let out = unsafe_getById "out" Dom_html.CoerceTo.pre in
  let run = unsafe_getById "run" Dom_html.CoerceTo.button in
  let code = unsafe_getById "code" Dom_html.CoerceTo.textarea in
  let onclick () = 
    let code = Js.to_string code##.value in
    print_endline code;
    let answer = read_string code in
    out##.textContent := 
    Js.some (Js.string (unsafe_to_string out##.textContent ^ answer ^ "\n"))
  in
  run##.onclick := Dom_html.handler (fun _ ->
    onclick ();
    Js._true);