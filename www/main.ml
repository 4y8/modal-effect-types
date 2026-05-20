open Js_of_ocaml
open Core

let unsafe_getById id f =
  let _ = (Dom_html.document##getElementById (Js.string id)) in
  Js.coerce_opt (Dom_html.document##getElementById (Js.string id))
    f (fun _ ->  assert false)

let read_string s =
  let open Syntax in
  let open Type in
  let open Context in
  let check_decl (p, ctx) = function
    | (x, SDFun m), _ ->
      begin match List.assoc_opt x ctx.id with
        | Some v ->
          let (_, a, _), _ = get_type_context v ctx in
          let (_, m), _ =
            try
              Frost.finfer (Check a) m [] ctx
            with
            | Frost.UnifyError (a, b, theta) ->
              Errors.cannot_unify None (Frost.subst_suffix theta a)
                (Frost.subst_suffix theta b)
          in
          (v, m) :: p, ctx
        | None ->
          let (a, m), ctx' = try
              Frost.finfer Infer m [] ctx
            with
            | Frost.UnifyError (a, b, theta) ->
              Errors.cannot_unify None (Frost.subst_suffix theta a)
                (Frost.subst_suffix theta b)
          in
          let a = Frost.subst_suffix ctx'.gamma a in
          let v, ctx = fresh_var x a ctx in
          (v, m) :: p, ctx
      end
    | d -> check_decl (p, ctx) d
  in
  let buf = Buffer.create 4096 in
  let fmt = Format.formatter_of_buffer buf in
  Error.red := (fun s -> s);
  Error.err_fmt := fmt;
  try
    let lb = Lexing.from_string s in
    let p =
      try
        Parser.file Lexer.lexer lb
      with
        Parser.Error ->
        Error.error_str_lexbuf lb
          (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
    let p, tctx = List.fold_left check_decl ([], init_ctx) p in
    let p = List.rev p in
    let ectx = ref (Eval.build_stdlib_map init_ctx) in
    Eval.fmt_out := fmt;
    Eval.eval_prog ectx p;
    List.iter (fun (x, _) ->
      let v = Eval.VMap.find x !ectx in
      let t = get_type_context_ tctx.gamma x |> fun (_, t, _) -> t in
      Format.fprintf fmt "%s : %a = %a@." (Bindlib.name_of x) Pprint.ty t Eval.pp_value v) p;
    Buffer.contents buf
  with
  | Error.Exit -> Buffer.contents buf

let unsafe_to_string s =
  Js.Opt.get s (fun _ -> assert false)
  |> Js.to_string

let () =
  Core.Eval.multicont := false;
  let out = unsafe_getById "out" Dom_html.CoerceTo.pre in
  let run = unsafe_getById "run" Dom_html.CoerceTo.button in
  let clear = unsafe_getById "clear" Dom_html.CoerceTo.button in
  let code = unsafe_getById "code" Dom_html.CoerceTo.textarea in
  let onclick () = 
    let code = Js.to_string code##.value in
    let answer = read_string code in
    out##.textContent := 
    Js.some (Js.string (unsafe_to_string out##.textContent ^ answer ^ "\n"))
  in
  run##.onclick := Dom_html.handler (fun _ ->
    onclick ();
    Js._true);
  clear##.onclick := Dom_html.handler (fun _ ->
    out##.textContent := Js.some (Js.string "");
    Js._true)
