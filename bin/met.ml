open Core
open Syntax
open Type

let eval = ref false
let launch_repl = ref true
let elab = ref false

let open_file f tctx ectx =
  try
    launch_repl := false;
    let ic = open_in f in
    let lb = Lexing.from_channel ic in
    Lexing.set_filename lb f;
    let p =
      try
        Parser.file Lexer.lexer lb
      with
        _ ->
        Error.error_str_lexbuf lb
          (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb)) in
    let p, tctx = check_prog tctx p in
    let p = TT.erase_types_prog p in
    Eval.eval_prog ectx p;
    close_in ic;
    tctx
  with
  | Error.Exit -> exit 1

let repl () =
  let lb = Lexing.from_channel stdin in
  let ectx = ref Eval.stdlib in
  let rec loop ctx =
    try
      print_string "# ";
      flush stdout;
      let tl =
        try
          Parser.top_level Lexer.lexer lb
        with
          _ ->
          Error.error_str_lexbuf lb
            (Printf.sprintf "Unexpected token: \"%s\"" (Lexing.lexeme lb))
      in
      match tl with
      | TLExpr m ->
        let (melab, a), _ = infer m ([], None) ctx in
        let m = TT.(erase_types VMap.empty melab) in
        let v = Eval.eval ectx m in
        if !elab then
          Format.printf "%a@." TT.pp_expr melab;
        Format.printf "- : %a = %a@." Pprint.ty a Eval.pp_value v;
        loop ctx
      | TLOpen f -> loop (open_file f ctx ectx)
      | TLDecl d ->
        let ctx = match d with
          | x, SDFun m ->
            let a, melab, ctx =
              match List.assoc_opt x ctx.id with
              | Some v ->
                let (_, a, _), _ = Context.get_type_context v ctx in
                let m, _ = check m a ([], None) ctx in
                a, m, ctx
              | None ->
                let (m, a), _ = infer m ([], None) ctx in
                let _, ctx = TT.fresh_var x a ctx in
                a, m, ctx
            in
            let m = TT.(erase_types VMap.empty melab) in
            let vf = Eval.eval ectx m in
            ectx := Eval.(SMap.add x vf !ectx);
            if !elab then
              Format.printf "%a@." TT.pp_expr melab;
            Format.printf "val %s : %a = %a@." x Pprint.ty a
              Eval.pp_value vf;
            ctx
          | _ -> snd (check_decl ([], ctx) (d, None))
        in
        loop ctx
    with
    | Error.Exit ->
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
  let ectx = ref Eval.stdlib in
  let _ = open_file f init_ctx ectx in
  if !eval then
    match Eval.SMap.find "main" !ectx with
    | VClo f -> ignore (f (VCon ("Unit", [])))
    | _ -> failwith "main should be a function"

let () =
  let spec_list =
    [("--eval", Arg.Set eval, "Evaluate the program (needs a main function)")
    ; ("--elab", Arg.Set elab, "Prints elaboration results")]
  in
  Format.set_margin 80;
  Arg.parse spec_list read_file "";
  if !launch_repl then
    ignore (repl ())
