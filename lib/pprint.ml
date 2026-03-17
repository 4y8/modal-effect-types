open Syntax
open Format

let kind fmt = function
  | Any -> fprintf fmt "Any"
  | Abs -> fprintf fmt "Abs"
  | Effect -> fprintf fmt "Effect"

let mask =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ")
    (fun fmt -> fprintf fmt "%s")

let rec ty_fora ctx fmt = function
  | TForA (k, a) ->
    let v, a, ctx = Bindlib.unbind_in ctx a in
    fprintf fmt "∀ %s : %a . %a" (Bindlib.name_of v) kind k
      (ty_fora ctx) a
  | a -> ty_arrow ctx fmt a
and ty_arrow ctx fmt = function
  | TArr (a, b) ->
    fprintf fmt "%a → %a" (ty_atom ctx) a (ty_arrow ctx) b
  | a -> ty_app ctx fmt a

and ty_app ctx fmt = function
  | TCon (c, arr) when Array.length arr > 0 ->
    fprintf fmt "%s %a" c (pp_print_array (ty_atom ctx)) arr
  | a -> ty_atom ctx fmt a
and ty_atom ctx fmt = function
  | TVar v ->
    fprintf fmt "%s" (Bindlib.name_of v)
  | TCon (c, [||]) ->
    fprintf fmt "%s" c
  | TMod (mu, a) ->
    fprintf fmt "%a %a" (modality ctx) mu (ty_atom ctx) a
  | ECtx e -> fprintf fmt "[%a]" (eff_ctx ctx) e
  | a -> fprintf fmt "(%a)" (ty_fora ctx) a

and eff ctx fmt {eff_name; eff_args} =
  fprintf fmt "%s %a" eff_name (pp_print_array (ty_atom ctx)) eff_args
and eff_ext ctx =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") (eff ctx)
and eff_ctx ctx fmt (d, eps) =
  match eps with
  | None -> eff_ext ctx fmt d
  | Some eps when d = [] ->
    eff_var ctx fmt eps
  | Some eps ->
    fprintf fmt "%a, %a" (eff_ext ctx) d (eff_var ctx) eps
and eff_var ctx fmt (a, l) =
  if l = [] then
    ty_atom ctx fmt a
  else
    fprintf fmt "%a \\ %a" (ty_atom ctx) a mask l

and modality ctx fmt = function
  | MAbs e -> fprintf fmt "[%a]" (eff_ctx ctx) e
  | MRel (l, r) -> fprintf fmt "<%a|%a>" mask l (eff_ext ctx) r

let ty fmt a = ty_fora (Bindlib.free_vars (box_type a)) fmt a

let mu fmt mu = modality (Bindlib.free_vars (box_mod mu)) fmt mu

let ectx fmt ectx = eff_ctx (Bindlib.free_vars (box_effect_ctx ectx)) fmt ectx
