open Syntax
open TT
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

let rec expr_let ctx fmt = function
  | LetMod (mu, nu, m, n) ->
    let v, n, ctx' = Bindlib.unbind_in ctx n in
    fprintf fmt "let%a mod%a %s =@ @[<2>%a@] in@ %a"
      (modality ctx) mu (modality ctx) nu (Bindlib.name_of v) (expr_let ctx) m
      (expr_let ctx') n
  | Mod (mu, m) ->
    fprintf fmt "mod%a@[<2>@ %a@]" (modality ctx) mu (expr_atom ctx) m
  | Lam (a, m) ->
    let v, m, ctx' = Bindlib.unbind_in ctx m in
    fprintf fmt "@[<2>λ%s : %a .@ %a@]" (Bindlib.name_of v) (ty_arrow ctx) a
      (expr_let ctx') m
  | TLam (k, m) ->
    let v, m, ctx = Bindlib.unbind_in ctx m in
    fprintf fmt "@[<2>Λ%s : %a.@ %a@]" (Bindlib.name_of v) kind k
      (expr_let ctx) m
  | m -> expr_app ctx fmt m
and expr_app ctx fmt = function
  | TApp (m, a) ->
    fprintf fmt "@[<2>%a@ %a@]" (expr_app ctx) m (ty_atom ctx) a
  | App (m, n) ->
    fprintf fmt "@[<2>%a@ %a@]" (expr_app ctx) m (expr_atom ctx) n
  | m -> expr_atom ctx fmt m
and expr_atom ctx fmt = function
  | Var v -> fprintf fmt "%s" (Bindlib.name_of v)
  | m -> fprintf fmt "(@[%a@])" (expr_let ctx) m

let expr fmt m = expr_let (Bindlib.free_vars (box_expr m)) fmt m
