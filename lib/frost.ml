open Syntax
open Context

exception UnifyError of pure_type * pure_type
exception Occurs of tvar * pure_type

type mode
  = Infer of pure_type
  | Check of pure_type
  | Fun of pure_type * mode

let rec is_guarded a theta = match a with
  | UGhost _ | Ghost | TForA _ | TMod _ -> false
  | TVar _ | TCon _ | MFlex _ | TArr _ -> true
  | PFlex v -> is_guarded (get_pflex_def_ v theta) theta
  | ECtx _ -> failwith "is_guarded: internal error"

let is_flex_var = function
  | MFlex _ | PFlex _ -> true
  | _ -> false

let subst_var a b v =
  Bindlib.(subst (bind_var v (box_type a) |> unbox) b)

let subst_suffix xi s =
  List.fold_left (fun t b -> match b with
      | BPFlex (a, p, _) -> subst_var t p a
      | BMFlex (a, Some tau, _) -> subst_var t tau a
      | _ -> t) s xi

let guess_mono =
  let rec aux l = function
    | MFlex v -> l, MFlex v
    | PFlex v -> l, PFlex v
    | TVar v -> l, TVar v
    | ECtx (d, eps) ->
      let l, d = aux_eff_ext l d in
      l, ECtx (d, eps)
    | TCon (s, a) ->
      let l, a = aux_array l a in
      l, TCon (s, a)
    | UGhost p -> aux l p
    | TForA (k, a) ->
      let v, a = Bindlib.unbind a in
      let l, a = aux l a in
      l, Bindlib.(box_type a |> bind_var v |> tfora_ k |> unbox)
    | Ghost ->
      incr counter;
      let v = Bindlib.new_var (fun v -> MFlex v)
          (Printf.sprintf "x%d" !counter) in
      (BMFlex (v, None, Any)) :: l, MFlex v
    | TArr (a, b) ->
      let l, a = aux l a in
      let l, b = aux l b in
      l, TArr (a, b)
    | TMod (MAbs (d, eps), a) ->
      let l, d = aux_eff_ext l d in
      let l, a = aux l a in
      l, TMod (MAbs (d, eps), a)
    | TMod (MRel (mask, d), a) ->
      let l, d = aux_eff_ext l d in
      let l, a = aux l a in
      l, TMod (MRel (mask, d), a)
  and aux_array l = Array.fold_left_map aux l
  and aux_eff_ext l =
    List.fold_left_map (fun l { eff_name ; eff_args } ->
        let l, eff_args = aux_array l eff_args in
        l, { eff_name ; eff_args }) l
  in
  aux

let rec join_sk s p theta = match s, p with
  (* U-GhostL *)
  | Ghost, p -> p, theta

  (* U-GhostR *)
  | s, Ghost -> s, theta

  (* U-Unit (generalised) *)
  | TCon (c, a), TCon (c', a') when c = c' ->
    let a, theta = Array.fold_right (fun (s, p) (a, theta) ->
        let s', theta = join_sk s p theta in
        (s' :: a), theta) (Array.combine a a') ([], theta) in
    TCon (c, Array.of_list a), theta

  (* U-Rigid *)
  | TVar x, TVar y when Bindlib.eq_vars x y ->
    TVar x, theta

  (* U-Flex *)
  | (PFlex _ | MFlex _) as alpha, MFlex beta ->
    alpha, join_var alpha beta theta

  (* U-FlexR *)
  | s, (MFlex _ as alpha) ->
    alpha, assign alpha s [] theta

  (* U-FlexL *)
  | (PFlex _ | MFlex _) as alpha, p ->
    alpha, assign alpha p [] theta

  (* U-Arrow *)
  | TArr (s1, s2), TArr (p1, p2) ->
    let s1', theta = join_sk s1 p1 theta in
    let s2', theta = join_sk s2 p2 theta in
    TArr (s1', s2'), theta

  (* U-Forall *)
  | TForA (k, s), TForA (k', p) when k = k' ->
    let alpha, s, p = Bindlib.unbind2 s p in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* U-UnivGhost *)
  | UGhost s, UGhost p ->
    let s', theta = join_sk s p theta in
    UGhost s', theta

  (* U-Forall-UnivGhost *)
  | TForA (k, s), (UGhost _ as p) ->
    let alpha, s = Bindlib.unbind s in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* U-UnivGhost-Forall *)
  | (UGhost _ as s), TForA (k, p) ->
    let alpha, p = Bindlib.unbind p in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* U-Guarded-UnivGhost *)
  | s, UGhost p when is_guarded s theta && not (is_flex_var s) ->
    join_sk s p theta

  (* U-UnivGhost-Guarded *)
  | UGhost s, p when is_guarded s theta && not (is_flex_var s) ->
    join_sk s p theta

  | _ -> raise (UnifyError (s, p))

and join_var alpha beta theta = match alpha, theta with
  (* U-Flex-Flex-Id *)
  | MFlex alpha, theta when Bindlib.eq_vars alpha beta -> theta

  (* U-Flex-Flex-L *)
  | MFlex alpha, BMFlex (a', None, k) :: theta when Bindlib.eq_vars alpha a' ->
    BMFlex (a', Some (MFlex beta), k) :: theta

  (* U-Flex-Flex-R *)
  | MFlex alpha, BMFlex (b', None, k) :: theta when Bindlib.eq_vars beta b' ->
    BMFlex (beta, Some (MFlex alpha), k) :: theta

  (* U-Flex-Flex-AssignMono *)
  | alpha, (BMFlex (gamma, Some tau, _) as hd) :: theta ->
    let _, theta = join_sk (subst_var alpha tau gamma)
        (subst_var (MFlex beta) tau gamma) theta in
    hd :: theta

  (* U-Flex-Flex-AssignPoly *)
  | PFlex a, BPFlex (a', p, k) :: theta when Bindlib.eq_vars a a' ->
    let q, theta = join_sk p (MFlex beta) theta in
    BPFlex (a, q, k) :: theta

  (* U-Flex-Flex-SkipPoly *)
  | _, (BPFlex _ as hd) :: theta

  (* U-Flex-Flex-SkipMono *)
  | _, (BMFlex _ as hd) :: theta

  (* U-Flex-Flex-Skip *)
  | _, ((BVar _ | Marker | BType _ | Lock _) as hd) :: theta ->
    let theta = join_var alpha beta theta in
    hd :: theta

  | _, [] -> raise (UnifyError (alpha, MFlex beta))

and assign alpha s xi theta = match alpha, theta with
  (* U-Assign-SolveM *)
  | MFlex a, BMFlex (a', None, k) :: theta when Bindlib.eq_vars a a' ->
    if Bindlib.occur a (box_type s) then
      raise (Occurs (a, s));
    let beta, tau = guess_mono (xi @ theta) s in
    BMFlex (a', Some tau, k) :: beta

  (* U-Assign-SolveP *)
  | PFlex a, BPFlex (a', q, k) :: theta when Bindlib.eq_vars a a' ->
    let p', theta = join_sk q s (xi @ theta) in
    BPFlex (a', p', k) :: theta

  (* U-Assign-AssignMono *)
  | MFlex _, (BMFlex (b, Some tau, _) as hd) :: theta ->
    let _, theta = join_sk (subst_var s tau b) (subst_var alpha tau b) theta in
    hd :: theta

  (* U-Assign-AssignMono' *)
  | PFlex _, (BMFlex (b, Some tau, _) as hd) :: theta ->
    let _, theta = join_sk alpha (subst_var s tau b) theta in
    hd :: theta

  (* U-Assign-AssignPoly *)
  | MFlex _, BPFlex (b, p, k) :: theta when Bindlib.occur b (box_type s) ->
    let xi, tau = guess_mono xi p in
    let theta = assign alpha (subst_var s tau b) xi theta in
    BPFlex (b, tau, k) :: theta

  (* U-Assign-SkipPoly *)
  | (MFlex a | PFlex a), (BPFlex (b, _, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s) || eq_vars b a) ->
    hd :: (assign alpha s xi theta)

  (* U-Assign-DependMono *)
  | (MFlex a | PFlex a), (BMFlex (b, None, _) as hd) :: theta when
      Bindlib.(occur b (box_type s) && not (eq_vars a b)) ->
    assign alpha s (hd :: xi) theta

  (* U-Assign-SkipMono *)
  | (MFlex a | PFlex a), (BMFlex (b, _, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s) || eq_vars b a) ->
    hd :: assign alpha s xi theta

  (* U-Assign-SkipRigid *)
  | alpha, (BType (b, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s)) ->
    hd :: assign alpha s xi theta

  (* U-Assign-SkipOthers *)
  | _, ((BVar _ | Marker | Lock _) as hd) :: theta ->
    hd :: assign alpha s xi theta

  | _ -> raise (UnifyError (alpha, s))

let rec sk_of_mode = function
  | Infer p | Check p -> p
  | Fun (p, m) -> TArr (p, sk_of_mode m)

type sup
  = Ty | Sk

let (=~) s p ({ gamma; _ } as ctx) =
  let s, gamma = join_sk s p gamma in
  s, { ctx with gamma }

let guess_mono p = fun ({ gamma; _ } as ctx) ->
  let gamma, p = guess_mono gamma p in
  p, { ctx with gamma }

(* eta expand to avoid value restriction *)
let guess_mono_suffix l =
  M.List.map (function
  | BPFlex (a, p, k) ->
    let* p = guess_mono p in
    return @@ BPFlex (a, p, k)
  | BMFlex (_, None, _) as b ->
    add_binding b >> return b
  | b -> return b) l

let rec prejoin p q = match p, q with
  | Ghost, q -> q
  | p, Ghost -> p
  | TCon (s, a), TCon (s', a') when s = s' -> TCon (s, Array.map2 prejoin a a')
  | TVar _ as a, _ -> a
  | MFlex _ as a, _ -> a
  | p, MFlex _ -> p
  | TForA (k, p), TForA (k', q) when k = k' ->
    let a, p, q = Bindlib.unbind2 p q in
    let p' = prejoin p q in
    Bindlib.(box_type p' |> bind_var a |> tfora_ k |> unbox)
  | UGhost p, TForA (k, q) ->
    let a, q = Bindlib.unbind q in
    let p' = prejoin p q in
    Bindlib.(box_type p' |> bind_var a |> tfora_ k |> unbox)
  (* q is a skeleton so does not have polymoprphic flexible variables *)
  | UGhost p, q when is_guarded q [] ->
    prejoin p q
  | TForA (k, p), UGhost q ->
    let a, p = Bindlib.unbind p in
    let p' = prejoin p q in
    Bindlib.(box_type p' |> bind_var a |> tfora_ k |> unbox)
  | UGhost p, UGhost q ->
    UGhost (prejoin p q)
  | p, UGhost q when is_guarded p [] ->
    prejoin p q
  | TArr (p1, p2), TArr (q1, q2) ->
    TArr (prejoin p1 q1, prejoin p2 q2)
  | p, q -> raise (UnifyError (p, q))

let rec presub m p q = match p, q, m with
  | Ghost, q, _ when is_guarded q [] ->
    q
  | p, q, (Check _ | Infer _) when is_guarded p [] && is_guarded q [] ->
    prejoin p q
  | MFlex _ as p, q, Fun _ when is_guarded q [] ->
    p
  | TForA (_, p), q, m ->
    let _, p = Bindlib.unbind p in
    presub m p q
  | p, TForA (_, q), m ->
    let _, q = Bindlib.unbind q in
    presub m p q
  | UGhost p, q, m
  | p, UGhost q, m ->
    presub m p q
  | TArr (p1, p2), TArr (q1, q2), Fun (_, m) ->
    TArr (prejoin p1 q1, presub m p2 q2)
  | p, q, _ -> raise (UnifyError (p, q))

let is_guarded p ({ gamma; _ } as ctx) =
  is_guarded p gamma, ctx

let rec broom loc m n s = match m, n, s with
  (* SI-Infer *)
  | Infer Ghost, _, s ->
    return s

  (* SI-ForallR *)
  | Check (TForA (k, b) as a), Ty, t ->
    let v, b = Bindlib.unbind b in
    with_binding (BType (v, k)) @@
    let* _ = broom loc (Check b) Ty t in
    return a

  (* SI-Arg *)
  | Fun (p, m), n, TArr (s1, s2) ->
    let* s1' = s1 =~ p in
    let* s2' = broom loc m n s2 in
    return (TArr (s1', s2'))

  (* SI-ForallL *)
  | (Fun _ | Check _), n, TForA (k, s) ->
    let a' = Bindlib.new_var (fun v -> PFlex v) "alpha" in
    add_binding (BPFlex (a', Ghost, k)) >>
    broom loc m n (Bindlib.subst s (PFlex a'))

  (* SI-UnivGhostL *)
  | (Fun _ | Check _), Sk, UGhost s ->
    broom loc m Sk s

  (* SI-Ghost *)
  | (Fun _ | Check _), Sk, Ghost ->
    return @@ sk_of_mode m

  (* SI-FlexMono *)
  | Fun _, _, (MFlex _ as alpha) ->
    alpha =~ sk_of_mode m

  (* SI-FlexPoly *)
  | Fun _, Ty, PFlex a ->
    flex_poly loc m a

  (* SI-FlexPoly' *)
  | Fun _, Sk, PFlex a ->
    flex_poly' loc m a

  (* SI-Check *)
  | Check a, Ty, t ->
    let* ga = is_guarded a in
    if ga then
      unless (is_guarded t)
        (fun () -> failwith "broom: SI-Check") >>
      let* _ = t =~ a in
      return a
    (* SI-FlexPoly *)
    else begin match t with
      | PFlex a -> flex_poly loc m a
      | _ -> failwith "broom: SI-Check"
    end

  (* SI-UnivGhostR *)
  | Check Ghost, Sk, s ->
    let* gs = is_guarded s in
    if gs then
      return @@ UGhost s
    (* SI-FlexPoly' *)
    else begin match s with
      | PFlex a -> flex_poly' loc m a
      | _ -> failwith "broom: SI-UnivGhostR"
    end

  | _ -> failwith "broom: todo"

and flex_poly loc m alpha =
  let* theta, (q, k), theta' = get_pflex_split alpha in
  let p = sk_of_mode m in
  let q' = presub m q p in
  replace_bindings theta' >>
  let* a = guess_mono q' in
  let* t = broom loc m Ty a in
  add_binding (BPFlex (alpha, q, k)) >>
  add_bindings theta >>
    return t

and flex_poly' loc m alpha =
  let* theta, (q, k), theta' = get_pflex_split alpha in
  let p = sk_of_mode m in
  let q' = presub m q p in
  replace_bindings theta' >>
  let* p' = broom loc m Sk q' in
  add_binding (BPFlex (alpha, q, k)) >>
  add_bindings theta >>
    return p'

let sub loc m n p =
  let* s, xi = get_suffix @@
      broom loc m n p in
  let* xi' = match n with
    | Ty -> guess_mono_suffix xi
    | Sk -> return xi
  in
  return @@ subst_suffix xi' s

let split_fun loc = function
  | Ghost -> return (Ghost, Ghost)
  | TArr (p, q) -> return (p, q)
  | MFlex a ->
    let* b = fresh_mflex Any in
    let* c = fresh_mflex Any in
    let* _ = MFlex a =~ TArr (MFlex b, MFlex c) in
    return (MFlex b, MFlex c)
  | a -> Errors.function_non_arr loc a

let unfun_mode m p = match m with
  | Fun (_, m) -> m
  | Check _ -> Check p
  | Infer _ -> Infer p

let rec sk_infer m { sexpr; loc } = match m, sexpr with
  (* PI-Unit *)
  | m, SCons ("Unit", []) ->
    sub loc m Sk (TCon ("unit", [||]))

  (* PI-Var *)
  | m, SVar x ->
    let* id = lookup_id x in
    begin match id with
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, q, _ = get_type_context v in
        sub loc m Sk q
    end

  (* PI-Anno *)
  | m, SAnn (_, a) ->
    let* a = Type.check_type a in
    sub loc m Sk a

  (* PI-Freeze *)
  | Check Ghost, SFreeze m ->
    sk_infer (Infer Ghost) m

  (* PI-AbsCheck *)
  | Check Ghost, SLam (x, None, m) ->
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x Ghost in
        get_suffix @@
        sk_infer (Check Ghost) m
      end in
    add_bindings xi >>
    return @@ UGhost (TArr (Ghost, q))

  (* PI-Abs *)
  | (Fun _ | Infer _) as mode, SLam (x, None, m) ->
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x p in
        get_suffix @@
        sk_infer (unfun_mode mode q) m
      end in
    add_bindings xi >>
    return @@ TArr (p, q')

  (* PI-AbsAnnoCheck *)
  | Check Ghost, SLam (x, Some a, m) ->
    let* a = Type.check_type a in
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (Check Ghost) m
      end in
    add_bindings xi >>
    return @@ UGhost (TArr (a, q))

  (* PI-Abs *)
  | (Fun _ | Infer _) as mode, SLam (x, Some a, m) ->
    let* a = Type.check_type a in
    let* _, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (unfun_mode mode q) m
      end in
    add_bindings xi >>
    return @@ TArr (a, q')

  (* PI-App *)
  | mode, SApp (m, n) ->
    let* p = sk_infer (Check Ghost) n in
    sk_infer (Fun (p, mode)) m @> split_fun None $> snd

  | _, _ -> Errors.cannot_infer_expr loc


let rec finfer m { sexpr; loc } = match m, sexpr with
  (* I-Unit *)
  | m, SCons ("Unit", []) ->
    let* a = sub loc m Ty (TCon ("unit", [||])) in
    return (a, Con ("Unit", []))

  | m, SInt n ->
    let* a = sub loc m Ty (TCon ("int", [||])) in
    return (a, Lit (Int n))


  | m, SStr s ->
    let* a = sub loc m Ty (TCon ("string", [||])) in
    return (a, Lit (Str s))

  (* I-Var *)
  | m, SVar x ->
    let* id = lookup_id x in
    begin match id with
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, a, _ = get_type_context v in
        let* b = sub loc m Ty a in
        return (b , Var v)
    end

  (* I-Anno *)
  | mode, SAnn (m, a) ->
    let* a = Type.check_type a in
    let* _, m = finfer (Check a) m in
    let* b = sub loc mode Ty a in
    return (b, m)

  (* I-Freeze *)
  | Check a, SFreeze m ->
    let* b, m = finfer (Infer Ghost) m in
    let* _ = b =~ a in
    return (a, m)

  (* I-AbsCheck and I-AbsAnnoCheck *)
  | Check t, SLam (x, a, m) ->
    let a', alphas = Type.split_foralls t in
    let a', b = match a' with
      | TArr (a, b) -> a, b
      | a' -> Errors.function_non_arr loc a'
    in let* a = match a with
    (* I-AbsCheck *)
    | None -> return a'
    (* I-AbsAnnoCheck *)
    | Some a ->
      let* a = Type.check_type a in
      a' =~ a
    in
    protect_context begin
      add_bindings (List.map (fun (x, k) -> BType (x, k)) alphas) >>
      let* v = fresh_var x a in
      let* _, m = finfer (Check b) m in
      return (t, Bindlib.(box_expr m |> bind_var v |> lam_ |> unbox))
    end

  (* I-Abs and I-AbsAnno *)
  | (Infer _ | Fun _) as mode, SLam (x, a', m) ->
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* a = match a' with
      | None -> guess_mono p
      | Some a ->
        let* a = Type.check_type a in
        p =~ a
    in let* p, xi =
      protect_context begin
        let* v = fresh_var x a in
        get_suffix @@
        let* b, m = finfer (unfun_mode mode q) m in
        return (TArr (a, b),
                Bindlib.(box_expr m |> bind_var v |> lam_ |> unbox))
      end in
    add_bindings xi >>
    return p

  (* I-App *)
  | mode, SApp (m, n) ->
    let* p = sk_infer (Check Ghost) n in
    let* t, m = finfer (Fun (p, mode)) m in
    let* a, b = split_fun None t in
    let* _, n = finfer (Check a) n in
    return (b, App (m, n))

  | _ ->
    Errors.cannot_infer_expr loc
