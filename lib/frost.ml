open Syntax
open Context

exception UnifyError of pure_type * pure_type
exception Occurs of tvar * pure_type

type mode
  = Infer of pure_type
  | Check of pure_type
  | Fun of pure_type * mode

let infer_ = Bindlib.box_apply (fun a -> Infer a)
let check_ = Bindlib.box_apply (fun a -> Check a)
let fun_ = Bindlib.box_apply2 (fun a m -> Fun (a, m))

let rec box_mode = function
  | Infer a -> infer_ (box_type a)
  | Check a -> check_ (box_type a)
  | Fun (a, m) -> fun_ (box_type a) (box_mode m)

let rec is_guarded a theta = match a with
  | UGhost _ | Ghost | TForA _ | TMod _ -> false
  | TVar _ | TCon _ | MFlex _ | TArr _ -> true
  | PFlex v -> is_guarded (get_pflex_def_ v theta) theta
  | ECtx _ -> failwith "is_guarded: internal error"

let is_flex_var = function
  | MFlex _ | PFlex _ -> true
  | _ -> false

let rec is_mono = function
  | TVar _
  | MFlex _ -> true
  | TCon (_, a) -> Array.for_all is_mono a
  | TForA _
  | TMod _
  | UGhost _ -> false
  | TArr (a, b) -> is_mono a && is_mono b
  | _ -> false

let is_ghost = function
  | Ghost -> true
  | _ -> false

let subst_var a b v =
  Bindlib.(subst (bind_var v (box_type a) |> unbox) b)

let subst_var_sk m a v =
  Bindlib.(subst (bind_var v (box_mode m) |> unbox) a)

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

let level = ref 0
let debug = ref false
let rule s =
  incr level;
  if !debug then
    Format.printf "%s %s@." (String.make !level '-') s
let end_rule () =
  decr level

let rec join_sk s p theta =
  match s, p with
  (* U-GhostL *)
  | Ghost, p ->
    rule "U-GhostL"; end_rule ();
    p, theta

  (* U-GhostR *)
  | s, Ghost ->
    rule "U-GhostR"; end_rule ();
    s, theta

  (* U-Unit (generalised) *)
  | TCon (c, a), TCon (c', a') when c = c' ->
    rule "U-Con";
    let a, theta = join_sk_array a a' theta in
    end_rule ();
    TCon (c, a), theta

  (* U-Rigid *)
  | TVar x, TVar y when Bindlib.eq_vars x y ->
    rule "U-Rigid"; end_rule ();
    TVar x, theta

  (* U-Flex *)
  | (PFlex _ | MFlex _) as alpha, MFlex beta ->
    rule "U-Flex";
    let theta = join_var alpha beta theta in
    end_rule ();
    alpha, theta

  (* U-FlexR *)
  | s, (MFlex _ as alpha) ->
    rule "U-FlexR";
    let theta = assign alpha s [] theta in
    end_rule ();
    alpha, theta

  (* U-FlexL *)
  | (PFlex _ | MFlex _) as alpha, p ->
    rule "U-FlexL";
    let theta = assign alpha p [] theta in
    end_rule ();
    alpha, theta

  (* U-Arrow *)
  | TArr (s1, s2), TArr (p1, p2) ->
    rule "U-Arrow";
    let s1', theta = join_sk s1 p1 theta in
    let s2', theta = join_sk s2 p2 theta in
    end_rule ();
    TArr (s1', s2'), theta

  (* U-Forall *)
  | TForA (k, s), TForA (k', p) when k = k' ->
    rule "U-Forall";
    let alpha, s, p = Bindlib.unbind2 s p in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    end_rule ();
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* U-UnivGhost *)
  | UGhost s, UGhost p ->
    rule "U-UnivGhost";
    let s', theta = join_sk s p theta in
    end_rule ();
    UGhost s', theta

  (* U-Forall-UnivGhost *)
  | TForA (k, s), (UGhost _ as p) ->
    rule "U-Forall-UnivGhost";
    let alpha, s = Bindlib.unbind s in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    end_rule ();
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* U-UnivGhost-Forall *)
  | (UGhost _ as s), TForA (k, p) ->
    rule "U-UnivGhost-Forall";
    let alpha, p = Bindlib.unbind p in
    let s', theta = join_sk s p (BType (alpha, k) :: theta) in
    end_rule ();
    Bindlib.(bind_var alpha (box_type s') |> tfora_ k |> unbox), theta

  (* NEW *)
  (* U-Mod *)
  | TMod (mu, s), TMod (nu, p) ->
    rule "U-Mod";
    let mu', theta = match join_sk_mod mu nu theta with
    | None -> raise (UnifyError (TMod (mu, s), TMod (nu, p)))
    | Some x -> x
    in
    let s', theta = join_sk s p theta in
    end_rule ();
    TMod (mu', s'), theta

  (* U-Mod-UnivGhost *)
  | TMod (mu, s), (UGhost _ as p) ->
    rule "U-Mod-UnivGhost";
    let s', theta = join_sk s p theta in
    end_rule ();
    TMod (mu, s'), theta
    
  (* U-UnivGhost-Mod *)
  | (UGhost _ as s), TMod (mu, p) -> 
    rule "U-UnivGhost-Mod";
    let s', theta = join_sk s p theta in
    end_rule ();
    TMod (mu, s'), theta
  (* END NEW *) 

  (* U-Guarded-UnivGhost *)
  | s, UGhost p when is_guarded s theta && not (is_flex_var s) ->
    rule "U-Guarded-UnivGhost";
    let theta = join_sk s p theta in
    end_rule ();
    theta

  (* U-UnivGhost-Guarded *)
  | UGhost s, p when is_guarded s theta && not (is_flex_var s) ->
    rule "U-UnivGhost-Guarded";let theta = join_sk s p theta in
    end_rule ();
    theta

  | _ ->
    raise (UnifyError (s, p))

and join_sk_array a a' theta =
  let l, theta = Array.fold_right (fun (s, p) (a, theta) ->
      let s', theta = join_sk s p theta in
      (s' :: a), theta) (Array.combine a a') ([], theta)
  in Array.of_list l, theta

(* NEW *)
and join_sk_mod mu nu theta =
  let join_sk_eff_ext d d' theta =
    Option.bind 
    (List.fold_right (fun { eff_name; eff_args } o -> match o with
          | None -> None
          | Some (d, d', theta) ->
            match Effects.find_label_eff eff_name d' with
            | None -> None
            | Some ({ eff_args = eff_args'; _ }, d') ->
              let eff_args, theta = join_sk_array eff_args eff_args' theta in
              Some ({ eff_name; eff_args } :: d, d', theta))
       d (Some ([], d', theta)))
    (fun (d, d', theta) ->
       if d' = [] then
         Some (d, theta)
       else None)
  in
  let join_sk_eff_ctx (d, eps) (d', eps') theta =
    match join_sk_eff_ext d d' theta with
    | None -> None
    | Some (d, theta) ->
      match eps, eps' with
      | None, None -> Some ((d, None), theta)
      | Some eps, Some eps' when Effects.eq_eff_var eps eps' ->
        Some ((d, Some eps), theta)
      | _, _ -> None
  in
  match mu, nu with
  | MRel (l, d), MRel (l', d') when Effects.eq_mask l l' ->
    Option.map (fun (d, theta) -> MRel (l, d), theta) (join_sk_eff_ext d d' theta)
  | MAbs e, MAbs e' ->
    Option.map (fun (e, theta) -> MAbs e, theta) (join_sk_eff_ctx e e' theta)
  | _, _ -> None
(* END NEW *)

and join_var alpha beta theta = match alpha, theta with
  (* U-Flex-Flex-Id *)
  | MFlex alpha, theta when Bindlib.eq_vars alpha beta ->
    rule "U-Flex-Flex-Id"; end_rule ();
    theta

  (* U-Flex-Flex-L *)
  | MFlex alpha, BMFlex (a', None, k) :: theta when Bindlib.eq_vars alpha a' ->
    rule "U-Flex-Flex-L"; end_rule ();
    BMFlex (a', Some (MFlex beta), k) :: theta

  (* U-Flex-Flex-R *)
  | MFlex alpha, BMFlex (b', None, k) :: theta when Bindlib.eq_vars beta b' ->
    rule "U-Flex-Flex-R"; end_rule ();
    BMFlex (beta, Some (MFlex alpha), k) :: theta

  (* U-Flex-Flex-AssignMono *)
  | alpha, (BMFlex (gamma, Some tau, _) as hd) :: theta ->
    rule "U-Flex-Flex-AssignMono";
    let _, theta = join_sk (subst_var alpha tau gamma)
        (subst_var (MFlex beta) tau gamma) theta in
    end_rule ();
    hd :: theta

  (* U-Flex-Flex-AssignPoly *)
  | PFlex a, BPFlex (a', p, k) :: theta when Bindlib.eq_vars a a' ->
    rule "U-Flex-Flex-AssignPoly";
    let q, theta = join_sk p (MFlex beta) theta in
    end_rule ();
    BPFlex (a, q, k) :: theta

  (* U-Flex-Flex-SkipPoly *)
  | _, (BPFlex _ as hd) :: theta ->
    rule "U-Flex-Flex-SkipPoly";
    let theta = join_var alpha beta theta in
    end_rule ();
    hd :: theta

  (* U-Flex-Flex-SkipMono *)
  | _, (BMFlex _ as hd) :: theta ->
    rule "U-Flex-Flex-SkipMono";
    let theta = join_var alpha beta theta in
    end_rule ();
    hd :: theta

  (* U-Flex-Flex-Skip *)
  | _, ((BVar _ | Marker | BType _ | Lock _) as hd) :: theta ->
    rule "U-Flex-Flex-Skip";
    let theta = join_var alpha beta theta in
    end_rule ();
    hd :: theta

  | _, [] ->
    raise (UnifyError (alpha, MFlex beta))

and assign alpha s xi theta = match alpha, theta with
  (* U-Assign-SolveM *)
  | MFlex a, BMFlex (a', None, k) :: theta when Bindlib.eq_vars a a' ->
    rule "U-Assign-SolveM";
    if Bindlib.occur a (box_type s) then
      raise (Occurs (a, s));
    let beta, tau = guess_mono (xi @ theta) s in
    if not (is_mono tau) then
      raise (UnifyError (MFlex a, tau));
    end_rule ();
    BMFlex (a', Some tau, k) :: beta

  (* U-Assign-SolveP *)
  | PFlex a, BPFlex (a', q, k) :: theta when Bindlib.eq_vars a a' ->
    rule "U-Assign-SolveP";
    let p', theta = join_sk q s (xi @ theta) in
    end_rule ();
    BPFlex (a', p', k) :: theta

  (* U-Assign-AssignMono *)
  | MFlex _, (BMFlex (b, Some tau, _) as hd) :: theta ->
    rule "U-Assign-AssignMono";
    let _, theta = join_sk (subst_var s tau b) (subst_var alpha tau b) theta in
    end_rule ();
    hd :: theta

  (* U-Assign-AssignMono' *)
  | PFlex _, (BMFlex (b, Some tau, _) as hd) :: theta ->
    rule "U-Assign-AssignMono'";
    let _, theta = join_sk alpha (subst_var s tau b) theta in
    end_rule ();
    hd :: theta

  (* U-Assign-AssignPoly *)
  | MFlex _, BPFlex (b, p, k) :: theta when Bindlib.occur b (box_type s) ->
    rule "U-Assign-AssignPoly";
    let xi', tau = guess_mono [] p in
    let xi = xi @ xi' in
    let theta = assign alpha (subst_var s tau b) xi theta in
    end_rule ();
    BPFlex (b, tau, k) :: theta

  (* U-Assign-SkipPoly *)
  | (MFlex a | PFlex a), (BPFlex (b, _, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s) || eq_vars b a) ->
    rule "U-Assign-SkipPoly";
    let theta = assign alpha s xi theta in
    end_rule ();
    hd :: theta

  (* U-Assign-DependMono *)
  | (MFlex a | PFlex a), (BMFlex (b, None, _) as hd) :: theta when
      Bindlib.(occur b (box_type s) && not (eq_vars a b)) ->
    rule "U-Assign-DependMono";
    let theta = assign alpha s (xi @ [hd]) theta in
    end_rule ();
    theta

  (* U-Assign-SkipMono *)
  | (MFlex a | PFlex a), (BMFlex (b, _, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s) || eq_vars b a) ->
    rule "U-Assign-SkipMono";
    let theta = assign alpha s xi theta in
    end_rule ();
    hd :: theta

  (* U-Assign-SkipRigid *)
  | alpha, (BType (b, _) as hd) :: theta when
      not Bindlib.(occur b (box_type s)) ->
    rule "U-Assign-SkipRigid";
    let theta = assign alpha s xi theta in
    end_rule ();
    hd :: theta

  (* U-Assign-SkipOthers *)
  | _, ((BVar _ | Marker | Lock _) as hd) :: theta ->
    rule "U-Assign-SkipOthers";
    let theta = assign alpha s xi theta in
    end_rule ();
    hd :: theta

  | _ ->
    raise (UnifyError (alpha, s))

let rec sk_of_mode = function
  | Infer p | Check p -> p
  | Fun (p, m) -> TArr (p, sk_of_mode m)

type sup
  = Ty | Sk

let (=~) s p ({ gamma; _ } as ctx) =
  let s, gamma = join_sk s p gamma in
  s, { ctx with gamma }

let rec split_guards = function
  | TForA (k, p) ->
    let alpha, p = Bindlib.unbind p in
    let mu, v, ughost, p = split_guards p in
    mu, (k, alpha) :: v, ughost, p
  | TMod (mu, p) ->
    let nu, v, ughost, p = split_guards p in
    Effects.compose mu nu, v, ughost, p
  | UGhost p ->
    Effects.id, [], true, p
  | p ->
    Effects.id, [], false, p

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
  | UGhost _ as p, TForA (k, q) ->
    let a, q = Bindlib.unbind q in
    let p' = prejoin p q in
    Bindlib.(box_type p' |> bind_var a |> tfora_ k |> unbox)
  (* q is a skeleton so does not have polymoprphic flexible variables *)
  | UGhost p, q when is_guarded q [] ->
    prejoin p q
  | TForA (k, p), (UGhost _ as q) ->
    let a, p = Bindlib.unbind p in
    let p' = prejoin p q in
    Bindlib.(box_type p' |> bind_var a |> tfora_ k |> unbox)
  | UGhost p, UGhost q ->
    UGhost (prejoin p q)
  | p, UGhost q when is_guarded p [] ->
    prejoin p q

  (* NEW *)
  | UGhost _ as p, TMod (mu, q)
  | TMod (mu, p), (UGhost _ as q) ->
    TMod (mu, prejoin p q)
  | TMod (mu, p), TMod (nu, q) ->
    let mu = match prejoin_mod mu nu with
      | Some mu -> mu
      | _ -> raise (UnifyError (TMod (mu, p), TMod (nu, q)))
    in
    TMod (mu, prejoin p q)
  (* END NEW *)

  | TArr (p1, p2), TArr (q1, q2) ->
    TArr (prejoin p1 q1, prejoin p2 q2)
  | p, q ->
    raise (UnifyError (p, q))

and prejoin_mod mu nu =
  let rec prejoin_eff_ext d d' = match d with
    | [] ->
      if d' = [] then Some [] else None
    | { eff_name; eff_args } :: d ->
      match Effects.find_label_eff eff_name d' with
      | None -> None
      | Some ({ eff_args = eff_args'; _ }, d') ->
        let eff_args = Array.map2 prejoin eff_args eff_args' in
        Option.map (List.cons { eff_name; eff_args }) (prejoin_eff_ext d d')
  in
  let prejoin_eff_ctx (d, eps) (d', eps') =
    match prejoin_eff_ext d d' with
    | None -> None
    | Some d ->
      match eps, eps' with
      | None, None -> Some (d, None)
      | Some eps, Some eps' when Effects.eq_eff_var eps eps' ->
        Some (d, Some eps)
      | _, _ -> None
  in
  match mu, nu with
  | MRel (l, d), MRel (l', d') when Effects.eq_mask l l' ->
    Option.map (fun d -> MRel (l, d)) (prejoin_eff_ext d d')
  | MAbs e, MAbs e' -> Option.map (fun e -> MAbs e) (prejoin_eff_ctx e e')
  | _, _ -> None

let rec presub m p q = match p, q, m with
  | Ghost, q, _ when is_guarded q [] ->
    q
  | p, Ghost, _ when is_guarded p [] ->
    p
  | p, q, (Check _ | Infer _) when is_guarded p [] && is_guarded q [] ->
    prejoin p q
  | MFlex _ as p, q, Fun _ when is_guarded q [] ->
    p
  | TForA (k, p), q, m ->
    let v, p = Bindlib.unbind p in
    Bindlib.(presub m p q |> box_type |> bind_var v |> tfora_ k |> unbox)
  | p, TForA (_, q), m ->
    let _, q = Bindlib.unbind q in
    presub m p q

  (* NEW *)
  | TMod (mu, p), q, m ->
    TMod (mu, presub m p q)
  | p, TMod (_, q), m ->
    presub m p q
  (* END NEW *)
 
  | UGhost p, q, m
  | p, UGhost q, m ->
    presub m p q
  | TArr (p1, p2), TArr (q1, q2), Fun (_, m) ->
    TArr (prejoin p1 q1, presub m p2 q2)
  | p, q, _ ->
    raise (UnifyError (p, q))

let guess_mono_ = guess_mono

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

let is_guarded p ({ gamma; _ } as ctx) =
  is_guarded p gamma, ctx

let is_pflex = function
  | PFlex _ -> true
  | _ -> false

let rule s = fun ctx ->
  (rule s, ctx)

let end_rule x = fun ctx ->
  end_rule ();
  (x, ctx)

let rec broom loc m n s =
  let* gp = is_guarded (sk_of_mode m) in
  let* gs = is_guarded s in
  match m, n, s with
  (* SI-Infer *)
  | Infer Ghost, _, s ->
    rule "SI-Infer" >>
    end_rule () >>
    return s

  (* SI-ForallR *)
  | Check (TForA (k, b) as a), Ty, t when not (is_pflex t) ->
    rule "SI-ForallR" >>
    let v, b = Bindlib.unbind b in
    with_binding (BType (v, k)) @@
    let* _ = broom loc (Check b) Ty t in
    end_rule () >>
    return a

  (* SI-Arg *)
  | Fun (p, m), n, TArr (s1, s2) ->
    rule "SI-Arg" >>
    let* s1' = s1 =~ p in
    let* s2' = broom loc m n s2 in
    end_rule () >>
    return (TArr (s1', s2'))

  (* SI-ForallL *)
  | (Fun _ | Check _), n, TForA (k, s) ->
    incr counter;
    rule "SI-ForallL" >>
    let a' = Bindlib.new_var (fun v -> PFlex v)
        (Printf.sprintf "x%d" !counter) in
    add_binding (BPFlex (a', Ghost, k)) >>
    let* s' = broom loc m n (Bindlib.subst s (PFlex a')) in
    end_rule () >>
    return s'

  (* SI-UnivGhostL *)
  | (Fun _ | Check _), Sk, UGhost s ->
    rule "SI-UnivGhostL" >>
    let* s' = broom loc m Sk s in
    end_rule () >>
    return s'

  (* SI-Ghost *)
  | (Fun _ | Check _), Sk, Ghost ->
    rule "SI-Ghost" >>
    end_rule () >>
    return @@ sk_of_mode m

  (* SI-FlexMono *)
  | Fun _, _, (MFlex _ as alpha) ->
    rule "SI-FlexMono" >>
    let* tau = alpha =~ sk_of_mode m in
    end_rule () >>
    return tau

  (* SI-FlexPoly *)
  | Fun _, n, PFlex a ->
    rule "SI-FlexPoly" >>
    let* s = broom_flex_poly loc [] m n a in
    end_rule () >>
    return s

  (* SI-FlexPoly *)
  | Check _, n, PFlex a when not gs ->
    rule "SI-FlexPoly" >>
    let* s = broom_flex_poly loc [] m n a in
    end_rule () >>
    return s

  (* SI-Check *)
  | Check a, Ty, t when gs && gp ->
    rule "SI-Check" >>
    let* _ = t =~ a in
    end_rule () >>
    return a

  (* SI-UnivGhostR *)
  | Check Ghost, Sk, s when gs && not (is_flex_var s) ->
    rule "SI-UnivGhostR" >>
    end_rule () >>
    return @@ UGhost s

  | _ -> failwith "broom: todo"

and broom_flex_poly loc xi m n alpha =
  let* b = pop_binding () in
  match b with
  (* SI-FlexPoly-Solve-Ty and SI-FlexPoly-Solve-Sk *)
  | BPFlex (a', q, k) when Bindlib.eq_vars a' alpha ->
    rule "SI-FlexPoly-Solve" >>
    let q' = presub m q (sk_of_mode m) in
    add_bindings xi >>
    let* a = match n with
      (* SI-FlexPoly-Solve-Ty *)
      | Ty -> guess_mono q'
      (* SI-FlexPoly-Solve-Sk *)
      | Sk -> return q' in
    let* t = broom loc m n a in
    add_binding (BPFlex (a', a, k)) >>
    end_rule () >>
    return t

  (* SI-FlexPoly-AssignMono *)
  | BMFlex (b, Some tau, _) as bind->
    rule "SI-FlexPoly-AssignMono" >>
    let* s = broom_flex_poly loc xi (subst_var_sk m tau b) n alpha in
    add_binding bind >>
    end_rule () >>
    return s

  (* SIFlexPoly-DependMono *)
  | BMFlex (b, None, _) as bind when Bindlib.occur b (box_mode m) ->
    rule "SI-FlexPoly-DependMono" >>
    let* s = broom_flex_poly loc (xi @ [bind]) m n alpha in
    end_rule () >>
    return s

  (* SI-FlexPoly-SkipMono *)
  | BMFlex (_, None, _) as bind ->
    rule "SI-FlexPoly-SkipMono" >>
    let* s = broom_flex_poly loc xi m n alpha in
    add_binding bind >>
    end_rule () >>
    return s

  (* SI-FlexPoly-SkipPoly *)
  | (BPFlex _ as bind) ->
    rule "SI-FlexPoly-SkipPoly" >>
    let* s = broom_flex_poly loc xi m n alpha in
    add_binding bind >>
    end_rule () >>
    return s

  (* SI-FlexPoly-SkipRigid *)
  | BType (b, _) as bind when not Bindlib.(occur b (box_mode m)) ->
    rule "SI-FlexPoly-SkipRigid" >>
    let* s = broom_flex_poly loc xi m n alpha in
    add_binding bind >>
    end_rule () >>
    return s

  | Marker | Lock _ -> failwith "broom_flex_poly: should not happen"

  | _ ->
    raise (UnifyError (PFlex alpha, sk_of_mode m))

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
    rule "PI-Unit" >>
    let* q = sub loc m Sk (TCon ("unit", [||])) in
    end_rule () >>
    return q

  | m, SInt _ ->
    rule "PI-Int" >>
    let* q = sub loc m Sk (TCon ("int", [||])) in
    end_rule q

  (* PI-Var *)
  | m, SVar x ->
    rule "PI-Var" >>
    let* id = lookup_id x in
    begin match id with
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, q, _ = get_type_context v in
        sub loc m Sk q @> end_rule
    end

  (* PI-Anno *)
  | m, SAnn (_, a) ->
    rule "PI-Anno" >>
    let* a = Type.check_type a in
    sub loc m Sk a @> end_rule

  (* PI-Freeze *)
  | Check Ghost, SFreeze m ->
    rule "PI-Freeze" >>
    sk_infer (Infer Ghost) m @>
    end_rule

  (* PI-AbsCheck *)
  | Check Ghost, SLam (x, None, m) ->
    rule "PI-AbsCheck" >>
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x Ghost in
        get_suffix @@
        sk_infer (Check Ghost) m
      end in
    add_bindings xi >>
    end_rule @@ UGhost (TArr (Ghost, q))

  (* PI-Abs *)
  | (Fun _ | Infer _) as mode, SLam (x, None, m) ->
    rule "PI-Abs" >>
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x p in
        get_suffix @@
        sk_infer (unfun_mode mode q) m
      end in
    add_bindings xi >>
    end_rule @@ TArr (p, q')

  (* PI-AbsAnnoCheck *)
  | Check Ghost, SLam (x, Some a, m) ->
    rule "PI-AbsAnnoCheck" >>
    let* a = Type.check_type a in
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (Check Ghost) m
      end in
    add_bindings xi >>
    end_rule @@ UGhost (TArr (a, q))

  (* PI-Abs *)
  | (Fun _ | Infer _) as mode, SLam (x, Some a, m) ->
    rule "PI-Abs" >>
    let* a = Type.check_type a in
    let* _, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (unfun_mode mode q) m
      end in
    add_bindings xi >>
    end_rule @@ TArr (a, q')

  (* PI-App *)
  | mode, SApp (m, n) ->
    rule "PI-App" >>
    let* p = sk_infer (Check Ghost) n in
    let* q' = sk_infer (Fun (p, mode)) m @> split_fun None $> snd in
    end_rule q'

  | _, _ -> Errors.cannot_infer_expr loc

let rec finfer m { sexpr; loc } = match m, sexpr with
  (* I-Unit *)
  | m, SCons ("Unit", []) ->
    rule "I-Unit" >>
    let* a = sub loc m Ty (TCon ("unit", [||])) in
    end_rule (a, Con ("Unit", []))

  | m, SInt n ->
    rule "I-Int" >>
    let* a = sub loc m Ty (TCon ("int", [||])) in
    end_rule (a, Lit (Int n))

  | m, SStr s ->
    rule "I-Str" >>
    let* a = sub loc m Ty (TCon ("string", [||])) in
    return (a, Lit (Str s))

  (* I-Var *)
  | m, SVar x ->
    rule "I-Var" >>
    let* id = lookup_id x in
    begin match id with
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, a, _ = get_type_context v in
        let* b = sub loc m Ty a in
        end_rule (b , Var v)
    end

  (* I-Anno *)
  | mode, SAnn (m, a) ->
    rule "I-Anno" >>
    let* a = Type.check_type a in
    let* _, m = finfer (Check a) m in
    let* b = sub loc mode Ty a in
    end_rule (b, m)

  (* I-Freeze *)
  | Check a, SFreeze m ->
    rule "I-Freeze" >>
    let* b, m = finfer (Infer Ghost) m in
    let* _ = b =~ a in
    end_rule (a, m)

  (* I-AbsCheck and I-AbsAnnoCheck *)
  | Check t, SLam (x, a, m) ->
    rule "I-AbsCheck" >>
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
    in protect_context begin
      add_bindings (List.map (fun (x, k) -> BType (x, k)) alphas) >>
      let* v = fresh_var x a in
      let* _, m = finfer (Check b) m in
      end_rule (t, Bindlib.(box_expr m |> bind_var v |> lam_ |> unbox))
    end

  (* I-Abs and I-AbsAnno *)
  | (Infer _ | Fun _) as mode, SLam (x, a', m) ->
    rule "I-Abs" >>
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* a = match a' with
      (* I-Abs *)
      | None -> guess_mono p
      (* I-AbsAnno  *)
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
    end_rule p

  (* I-App *)
  | mode, SApp (m, n) ->
    rule "I-App" >>
    let* p = sk_infer (Check Ghost) n in
    let* t, m = finfer (Fun (p, mode)) m in
    let* a, b = split_fun None t in
    let* _, n = finfer (Check a) n in
    end_rule (b, App (m, n))

  | _ ->
    Errors.cannot_infer_expr loc
