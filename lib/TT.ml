open Context

type ty = Syntax.pure_type

type modality = Syntax.pure_mod

type pat = Syntax.pat

type eext = Syntax.effect_ext

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
  | Hand of expr * eext * (expr, expr) Bindlib.binder *
            (string * (expr, (expr, expr) Bindlib.binder) Bindlib.binder) list

  | Match of modality * expr * (pat * (expr, expr) Bindlib.mbinder) list
  | Mask of string list * expr
  | Lit of Syntax.lit
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

let match_ mu m l =
  Bindlib.box_apply3 (fun mu m l -> Match (mu, m, l)) mu m (Bindlib.box_list l)

let mask_ l =
  Bindlib.box_apply (fun m -> Mask (l, m))

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
  | Match (mu, m, c) ->
    match_ (Syntax.box_mod mu) (box_expr m)
      (List.map (fun (p, c) ->
           Bindlib.(box_pair (Syntax.box_pat p) (box_mbinder box_expr c))) c)
  | Mask (l, m) ->
     mask_ l (box_expr m)
  | Lit _ as m -> Bindlib.box m

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

let split_arr loc = function
  | Syntax.TArr (a, b) -> a, b
  | a ->
    Errors.expected_arr loc a

let split_forall loc = function
  | Syntax.TForA (k, a) -> k, a
  | a -> Errors.expected_forall loc a

let split_foralls a =
  let rec aux l = function
    | Syntax.TForA (k, b) ->
      let v, a = Bindlib.unbind b in
      aux ((v, k) :: l) a
    | a -> a, l
  in Pair.map_snd List.rev @@ aux [] a

let split_cons loc = function
  | Syntax.TCon (c, l) -> c, l
  | a -> Errors.expected_cons loc a

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
    let (_, a, gamma'), ctx = get_type_context v ctx in
    let mu, a = split_var a in
    let nu, f = locks e gamma' in
    if not (Effects.sub_mod mu nu f) && not (fst @@ is_abs a ctx) then
      Errors.no_access None (Bindlib.name_of v) v e ctx;
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
    let a, b = split_arr None (check ctx m Hole e) in
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
    let k, a = split_forall None a in
    if k = Abs && not (fst @@ is_abs b ctx) then
      Errors.kind_mismatch None b ~expected:Syntax.Abs ~got:Syntax.Any;
    Bindlib.subst a b

  (* Switch *)
  | _, Check a ->
    let a' = check ctx m Hole e in
    if not Effects.(eq_ty a' a) then
      Errors.type_mismatch None ~got:a' ~expected:a;
    a

  | _, _ -> failwith "todo"

let fresh_var x a ({ gamma; id; _ } as ctx) =
  let v = Bindlib.new_var (fun v -> Var v) x in
  v, { ctx with gamma = BVar (v, a) :: gamma; id = (x, v) :: id }

let fresh_vars args ctx =
  let vars, ctx =
    List.fold_right (fun (x, t) (vars, ctx) ->
        Pair.map_fst (fun v -> v :: vars) @@ fresh_var x t ctx)
      args ([], ctx) in
  let mvar = Array.of_list vars in
  mvar, ctx

module VMap = Map.Make(struct
    type t = var
    let compare = Bindlib.compare_vars
  end)

let svar_of_var v =
  Bindlib.new_var (fun v -> Syntax.Var v) (Bindlib.name_of v)

let rec erase_types env = function
  | Lit l -> Syntax.Lit l
  | App (m, n) -> Syntax.App (erase_types env m, erase_types env n)
  | Do (op, m) -> Syntax.Do (op, erase_types env m)
  | TLam (_, m) ->
    let _, m = Bindlib.unbind m in
    erase_types env m
  | TApp (m, _) -> erase_types env m
  | Mod (_, m) -> erase_types env m
  | Con (c, l) -> Syntax.Con (c, List.map (erase_types env) l)
  | Mask (l, m) -> Syntax.Mask (l, erase_types env m)
  | Lam (_, b) ->
    Syntax.Lam (erase_types_binder env b)
  | LetMod (_, _, m, n) ->
    Syntax.Let (erase_types env m, erase_types_binder env n)
  | Hand (m, _, ret, h) ->
    let h = List.map (fun (op, b) ->
        let v, b = Bindlib.unbind b in
        let v' = svar_of_var v in
        let b = erase_types_binder (VMap.add v v' env) b in
        op, Bindlib.(box_binder Syntax.box_expr b |> bind_var v' |> unbox)
      ) h in
    Syntax.Hand (erase_types env m, erase_types_binder env ret, h)
  | Match (_, m, l) ->
    let l = List.map (fun (p, b) ->
        let v, m = Bindlib.unmbind b in
        let v' = Array.map svar_of_var v in
        let env = Array.fold_left (fun env (v, v') -> VMap.add v v' env) env
            (Array.combine v v') in
        p, Bindlib.(erase_types env m |> Syntax.box_expr
                    |> bind_mvar v' |> unbox)
      ) l in
    Syntax.Match (erase_types env m, l)
  | Var v ->
    match VMap.find_opt v env with
    | Some v -> Syntax.Var v
    | None -> Syntax.FVar (Bindlib.name_of v)

and erase_types_binder env b =
    let v, m = Bindlib.unbind b in
    let v' = svar_of_var v in
    Bindlib.(erase_types (VMap.add v v' env) m |> Syntax.box_expr
             |> bind_var v' |> unbox)

let erase_types_prog p =
  List.map (fun (v, m) -> Bindlib.name_of v, erase_types VMap.empty m) p

open Pprint
open Format

let rec simpl = function
  | Match (mu, m, [((Syntax.PVar _ | Syntax.PWild), b)]) ->
    let v, n = Bindlib.unmbind b in
    let b = Bindlib.(box_expr n |> bind_var v.(0) |> unbox) in
    simpl (LetMod (Effects.id, mu, m, b))
  | LetMod (mu, nu, m, b) ->
    let m = simpl m in
    let v, n = Bindlib.unbind b in
    let n = simpl n in
    let b = Bindlib.(box_expr n |> bind_var v |> unbox) in
    LetMod (mu, nu, m, b)
  | Lit _ | Var _ as m -> m
  | m -> m

let rec expr_let ctx fmt = function
  | LetMod (mu, nu, m, n) ->
    let v, n, ctx' = Bindlib.unbind_in ctx n in
    fprintf fmt "let%a mod%a %s = @[<2>%a@] in@ %a"
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
  | Mask (l, m) ->
    fprintf fmt "mask<%a> %a" (pp_print_list pp_print_string) l
      (expr_atom ctx) m
  | Match (mu, m, l) ->
    let pp_clause fmt (p, b) =
      let rec pp_pat l = function
        | Syntax.PWild -> fprintf fmt "_"; l
        | Syntax.PVar _ ->
          fprintf fmt "%s" (Bindlib.name_of (List.hd l));
          List.tl l
        | Syntax.PCon (c, p) ->
          fprintf fmt "%s(" c;
          let l = List.fold_left (fun l p ->
              let l = pp_pat l p in
              fprintf fmt ",@ ";
              l
            ) l p
          in
          fprintf fmt ")";
          l
      in
      let v, n, ctx = Bindlib.unmbind_in ctx b in
      let l = Array.to_list v in
      fprintf fmt "| ";
      ignore (pp_pat l p);
      fprintf fmt " -> @[<2> %a@]" (expr_let ctx) n
    in
    fprintf fmt "match%a %a with@.%a" (modality ctx) mu (expr_let ctx) m
      (pp_print_list ~pp_sep:pp_force_newline pp_clause) l
  | m -> expr_app ctx fmt m
and expr_app ctx fmt = function
  | TApp (m, a) ->
    fprintf fmt "@[<2>%a@ %a@]" (expr_app ctx) m (ty_atom ctx) a
  | App (m, n) ->
    fprintf fmt "@[<2>%a@ %a@]" (expr_app ctx) m (expr_atom ctx) n
  | m -> expr_atom ctx fmt m
and expr_atom ctx fmt = function
  | Var v -> fprintf fmt "%s" (Bindlib.name_of v)
  | Lit (Str s) -> fprintf fmt "\"%s\"" s
  | Lit (Int n) -> fprintf fmt "%d" n
  | m -> fprintf fmt "(@[%a@])" (expr_let ctx) m

let pp_expr fmt m =
  let m = simpl m in
  expr_let (Bindlib.free_vars (box_expr m)) fmt m
