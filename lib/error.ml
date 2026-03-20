open Lexing
open Format

exception Exit

let err msg =
  Format.eprintf "@[<hov>\027[31;1mError\027[0m: ";
  msg err_formatter;
  Format.eprintf "@].";
  raise Exit

let error loc msg =
  match loc with
  | None -> err msg
  | Some (bg, _) when bg.pos_fname = "" ->
    err msg
  | Some (bg, nd) ->
  let ic = open_in bg.pos_fname in
  let rec get_line n =
    if n = 1 then
      input_line ic
    else begin
      ignore (input_line ic);
      get_line (n - 1)
    end
  in
  let b = bg.pos_cnum - bg.pos_bol in
  let l = get_line bg.pos_lnum in
  let e = if nd.pos_lnum = bg.pos_lnum then nd.pos_cnum - nd.pos_bol else String.(length l) in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n"
    bg.pos_fname bg.pos_lnum b e;
  let pref = Printf.sprintf "%d |" bg.pos_lnum in
  Format.eprintf "%s%s\n" pref l;
  let length = e - b in
  Format.eprintf "%s\027[31;1m%s\027[0m" (String.make (b + String.length pref) ' ')
    (String.make length '^');
  err msg

let error_str loc s =
  error loc (fun fmt -> fprintf fmt "%s" s)

let error_str_lexbuf lexbuf s =
  error (Some (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf))
    (fun fmt -> fprintf fmt "%s" s)
