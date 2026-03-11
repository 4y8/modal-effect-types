open Syntax
open Format

let kind fmt = function
  | Any -> fprintf fmt "Any"
  | Abs -> fprintf fmt "Abs"
  | Effect -> fprintf fmt "Effect"

let rec ty_fora ctx fmt = function
  | TForA (k, a) ->
    let v, a, ctx = Bindlib.unbind_in ctx a in
    fprintf fmt "∀ %s : %a .@ @[<2>%a@]" (Bindlib.name_of v) kind k
      (ty_fora ctx) a
  | a -> ty_arrow ctx fmt a
and ty_arrow ctx fmt = function
  | TArr (a, b) ->
    fprintf fmt "%a →@ %a" (ty_atom ctx) a (ty_arrow ctx) b
  | a -> ty_atom ctx fmt a
and ty_atom ctx fmt = function
  | TFlex v
  | TVar v ->
    fprintf fmt "%s" (Bindlib.name_of v)
  | TCon (c, [||]) ->
    fprintf fmt "%s" c
  | TCon (c, arr) ->
    fprintf fmt "%s %a" c (pp_print_array (ty_atom ctx)) arr
  | TMod (mu, a) ->
    fprintf fmt "%a %a" (modality ctx) mu (ty_atom ctx) a
  | a -> fprintf fmt "(@[%a@])" (ty_fora ctx) a

and eff ctx fmt {eff_name; eff_type = (a, b)} =
  fprintf fmt "%s: %a ⇒@ %a" eff_name (ty_fora ctx) a (ty_fora ctx) b
and eff_ctx ctx =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") (eff ctx)

and modality ctx fmt = function
  | MAbs e -> fprintf fmt "[@[%a@]]" (eff_ctx ctx) e
  | MRel (l, r) ->
    fprintf fmt "<@[%a|%a@]>"
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ")
         (fun fmt -> fprintf fmt "%s"))
      l (eff_ctx ctx) r

let ty fmt a = ty_fora (Bindlib.free_vars (box_type a)) fmt a
