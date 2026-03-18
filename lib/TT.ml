open Context

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

let rec is_val = function
  | Mod (_, _) -> true
  | Var _ -> true
  | Lam (_, _) -> true
  | TLam (_, m) ->
    let _, m = Bindlib.unbind m in
    is_val m
  | TApp (m, _) -> is_val m
  | LetMod (_, _, m, n) ->
    let _, n = Bindlib.unbind n in is_val m && is_val n
  | Con (_, l) -> List.for_all is_val l
  | _ -> false

let split_var = function
  | Syntax.TMod (mu, a) -> mu, a
  | _ -> failwith "internal error"

type shape = Hole | Check of Syntax.pure_type

let shape_map f = function
  | Hole -> Hole
  | Check a -> Check (f a)

let shape_iter f = function
  | Hole -> ()
  | Check a -> f a

let expected_mod _ _ =
  Error.error_str None "Didn't get expected modality"

let check_mod mu = function
  | Syntax.TMod (nu, a) when Effects.eq_mod mu nu -> a
  | a -> expected_mod a mu

let rec check ctx m s e = match m, s with
  (* T-Var *)
  | Var v, Hole ->
    let _, a, gamma' = get_type_context ctx.gamma v in
    let mu, a = split_var a in
    let nu, f = locks e gamma' in
    if not (Effects.sub_mod mu nu f) && not (is_abs ctx a) then
      Errors.no_access None (Bindlib.name_of v) v ctx e;
    a

  (* T-Mod *)
  | Mod (mu, v), s ->
    if not (is_val v) then
      Errors.expected_val None v;
    check (ctx <: Lock (mu, e)) m (shape_map (check_mod mu) s)
      (Effects.apply_mod mu e)

  (* T-Letmod *)
  | LetMod (mu, nu, v, m), s ->
    if not (is_val v) then
      Errors.expected_val None v;
    let a = check_mod mu (check (ctx <: Lock (nu, e)) v Hole
                            (Effects.apply_mod nu e)) in
    let x, m = Bindlib.unbind m in
    check (ctx <: BVar (x, TMod (Effects.compose nu mu, a))) m s e

  (* T-App *)
  | App (m, n), Hole ->
    let a, b = Type.split_arr None (check ctx m Hole e) in
    let _ = check ctx n (Check a) e in
    b

  (* T-Abs *)
  | Lam (a, m), Check (TArr (a', b)) when Effects.eq_ty a a' ->
    let x, m = Bindlib.unbind m in
    let _ = check (ctx <: BVar (x, a)) m (Check b) e in
    TArr (a, b)
  | Lam (a, m), Hole ->
    let x, m = Bindlib.unbind m in
    TArr (a, check (ctx <: BVar (x, a)) m Hole e)

  (* T-TApp *)
  | TApp (m, b), Hole ->
    let a = check ctx m Hole e in
    let k, a = Type.split_forall None a in
    if k = Abs && not (is_abs ctx b) then
      Errors.kind_mismatch None b ~expected:Syntax.Abs ~got:Syntax.Any;
    Bindlib.subst a b

  (* Switch *)
  | _, Check a ->
    let a' = check ctx m Hole e in
    if not Effects.(eq_ty a' a) then
      Errors.type_mismatch None ~got:a' ~expected:a;
    a

  | _, _ -> failwith "todo"
