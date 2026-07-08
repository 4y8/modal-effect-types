type ty = Syntax.pure_type

type modality = Syntax.pure_mod

type pat = Syntax.pat

type ectx = Syntax.effect_ctx

type kind = Syntax.kind

type expr
  = Var of var
  | Lam of ty * (expr, expr) Bindlib.binder
  | App of expr * expr
  | TLam of kind * (ty, expr) Bindlib.binder
  | TApp of expr * ty
  | Mod of modality * expr
  | LetMod of modality * modality * expr * (expr, expr) Bindlib.binder
  | Do of string * expr
  | Con of string * expr list
  | Hand of expr * ectx * (expr, expr) Bindlib.binder *
            (string * (expr, (expr, expr) Bindlib.binder) Bindlib.binder) list

  | Match of expr * (pat * (expr, expr) Bindlib.mbinder) list
and var = expr Bindlib.var

let var_ = Bindlib.box_var

let lam_ = Bindlib.box_apply2 (fun a m -> Lam (a, m))

let app_ = Bindlib.box_apply2 (fun m n -> App (m, n))

let tlam_ k = Bindlib.box_apply (fun m -> TLam (k, m))

let tapp_ = Bindlib.box_apply2 (fun m a -> TApp (m, a))

let mod_ = Bindlib.box_apply2 (fun mu m -> Mod (mu, m))

let letmod_ = Bindlib.box_apply4 (fun mu nu m n -> LetMod (mu, nu, m, n))

let do_ e = Bindlib.box_apply (fun m -> Do (e, m))

let con_ c l = Bindlib.box_apply (fun l -> Con (c, l)) (Bindlib.box_list l)

let hand_ m d ret h =
  let h = List.map (fun (e, b) -> Bindlib.box_apply (fun b -> (e, b)) b) h
       |> Bindlib.box_list in
  Bindlib.box_apply3 (fun m ret h -> Hand (m, d, ret, h)) m ret h

let match_ m l =
  Bindlib.box_apply2 (fun m l -> Match (m, l)) m (Bindlib.box_list l)

let rec box_expr = function
  | Var v -> var_ v
  | Lam (a, m) -> lam_ (Syntax.box_type a) (Bindlib.box_binder box_expr m)
  | App (m, n) -> app_ (box_expr m) (box_expr n)
  | TLam (k, m) -> tlam_ k (Bindlib.box_binder box_expr m)
  | TApp (m, a) -> tapp_ (box_expr m) (Syntax.box_type a)
  | Mod (mu, m) -> mod_ (Syntax.box_mod mu) (box_expr m)
  | LetMod (mu, nu, m, n) ->
    letmod_ (Syntax.box_mod mu) (Syntax.box_mod nu) (box_expr m)
      (Bindlib.box_binder box_expr n)
  | Do (e, m) -> do_ e (box_expr m)
  | Con (c, l) -> con_ c (List.map box_expr l)
  | Hand (m, d, ret, h) ->
    hand_ (box_expr m) d (Bindlib.box_binder box_expr ret)
      (List.map (fun (e, b) ->
           e, Bindlib.(box_binder (box_binder box_expr) b)) h)
  | Match (m, c) ->
    match_ (box_expr m)
      (List.map (fun (p, c) ->
           Bindlib.(box_pair (Syntax.box_pat p) (box_mbinder box_expr c))) c)
