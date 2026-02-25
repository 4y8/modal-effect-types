open Syntax
open Context

let unknown_var loc x = Error.error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = Error.error_str loc ("Unknown effect " ^ x)

let type_mismatch loc _ _ = Error.error_str loc "Type mismatch todo"

let expected_arr loc _ = Error.error_str loc "Expected function type todo"
let expected_prod loc _ = Error.error_str loc "Expected product type todo"
let expected_sum loc _ = Error.error_str loc "Expected sum type todo"
let expected_val loc _ = Error.error_str loc "Expected a value todo"

let mod_mismatch loc _ _ _ = Error.error_str loc "Modality mismatch todo"

let kind_mismatch loc _ _ _ = Error.error_str loc "Kind mismatch todo"

let no_access loc _ _ _ = Error.error_str loc "Cannot access variable todo"

let ill_formed_cons loc x c _ = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Ill-typed for constructor %s of %s todo" c x)

let no_unboxing loc _ _ =
  Error.error_str loc "Cannot unbox function in application todo"

let missing_declaration loc x =
  Error.error_str loc ("Missing declaration for function " ^ x)

let eff_arg_mismatch loc e a b = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e (List.length a) (List.length b))

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SInl m
  | SInr m
  | SAnn (m, _) 
  | SAppT (m, _) -> is_val m.sexpr
  | SPair (m, n) -> is_val m.sexpr && is_val n.sexpr
  | _ -> false

let is_mod = function
  | TMod (_, _) -> true
  | _ -> false

let rec check_type ?(s=[]) ctx t = match t.stype with
  | STMod (m, t) -> TMod (check_mod ctx m, check_type ~s ctx t)
  | STArr (t, t') -> TArr (check_type ~s ctx t, check_type ctx t' ~s)
  | STSum (t, t') -> TSum (check_type ~s ctx t, check_type ~s ctx t')
  | STProd (t, t') -> TProd (check_type ~s ctx t, check_type ~s ctx t')
  | STVar x ->
    match List.assoc_opt x s with
    | Some t -> t
    | None ->
      match get_kind ctx.gamma x with
      | None -> unknown_var t.tloc x
      | Some k ->
        if k = Effect then
          kind_mismatch t.tloc t k Any;
        TVar (x, k)
    
and check_mod ctx m = match m.smod with
  | SMAbs e -> MAbs (check_effect_ctx ctx e)
  | SMRel (l, d) ->
    MRel (check_mask ctx l, check_effect_ctx ctx d)

and check_effect_ctx ctx l =
  List.map (fun {seff_name; seff_args; eloc} ->
      match List.assoc_opt seff_name ctx.effects with
      | None -> unknown_eff eloc seff_name
      | Some (args, t) ->
        if List.length args <> List.length seff_args then
          eff_arg_mismatch eloc seff_name args seff_args;
        let s = List.combine args (List.map (check_type ctx) seff_args) in
        List.map (fun { eff_type = (a, b); eff_name } ->
            let a = Subst.pure_type s a in
            let b = Subst.pure_type s b in
            if not (is_abs a) then kind_mismatch eloc a Abs Any;
            if not (is_abs b) then kind_mismatch eloc b Abs Any;
            { eff_name ; eff_type = a, b }) t
    ) l |> List.flatten
      
and check_mask ctx = function
  | [] -> []
  | (e, loc) :: tl->
    if List.mem_assoc e ctx.effects then 
      e :: check_mask ctx tl
    else
      unknown_eff loc e

let split_arr loc = function
  | TArr (a, b) -> a, b
  | a -> expected_arr loc a

let split_prod loc = function
  | TProd (a, b) -> a, b
  | a -> expected_prod loc a

let split_sum loc = function
  | TSum (a, b) -> a, b
  | a -> expected_sum loc a

let join_type loc t t' f =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g = g' then
    type_mismatch loc g g';
  if is_abs g then
    g
  else match Effect.join_mod mu nu f with
    | None -> mod_mismatch loc mu nu g
    | Some lam -> TMod (lam, g)

let rec check ctx ({loc; sexpr} as m) a e = match sexpr with
  (* B-Mod *)
  | v when is_val v && is_mod a ->
    begin match a with
      | TMod (mu, a) ->
        check (ctx <: Lock (mu, e)) m a (Effect.apply_mod mu e)
      | _ -> failwith "impossible"
    end
  (* B-Abs *)
  | SLam (x, m) ->
    let (a, b) = split_arr loc a in
    check (ctx <: BVar (x, a)) m b e
  (* B-HandlerCheck *)
  | SHand (m, d, (l, (PVar x, n))) ->
    let b = a in (* stay consistent with the paper *)
    let d = check_effect_ctx ctx d in
    let a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    check (ctx <: BVar (x, TMod (MRel ([], d), a))) n b e;
    let check_clause (li, loc, PVar pi, ri, ni) =
      match Effect.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx = ctx <: BVar (pi, ai) <: BVar (ri, TArr (bi, b)) in
        check ctx ni b e
    in
    List.iter check_clause l
  (* B-Pair *)
  | SPair (m, n) ->
    let a, b = split_prod loc a in
    check ctx m a e;
    check ctx n b e
  (* B-Inl *)
  | SInl m ->
    let a, _ = split_sum loc a in
    check ctx m a e
  (* B-Inr *)
  | SInr m ->
    let _, b = split_sum loc a in
    check ctx m b e
  (* B-CrispPairCheck *)
  | SLetP (x, y, v, m) ->
    let a' = a in
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let mu, g = get_guarded (infer ctx v e) in
    let a, b = split_prod v.loc g in
    let ctx = ctx <: BVar (x, TMod (mu, a)) <: BVar (y, TMod (mu, b)) in
    check ctx m a' e
  (* B-CrispSumCheck *)
  | SMatch (v, x, m1, y, m2) -> 
    let a' = a in
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let mu, g = get_guarded (infer ctx v e) in
    let a, b = split_sum v.loc g in
    check (ctx <: BVar (x, TMod (mu, a))) m1 a' e;
    check (ctx <: BVar (y, TMod (mu, b))) m2 a' e
  (* B-Switch *)
  | _ ->
    let mu, g = get_guarded (infer ctx m e) in
    let nu, g' = get_guarded a in
    if g <> g' then type_mismatch loc g g'
    else
      if not (Effect.sub_mod mu nu e) && not (is_abs g) then
        mod_mismatch loc mu nu g
    
and infer ctx {loc; sexpr} e = match sexpr with
  (* B-Var *)
  | SVar x ->
    begin match get_type_context ctx.gamma x with
      | None -> unknown_var loc x
      | Some (a, gamma') ->
        let nu, f = locks e gamma' in
        match across a nu f with
        | None -> no_access loc x ctx e
        | Some t -> t
    end
  (* B-Annotation *)
  | SAnn (m, a) ->
    let a = check_type ctx a in
    check ctx m a e;
    a
  (* B-App *)
  | SApp (m, n) ->
    let mu, g = get_guarded (infer ctx m e) in
    let a, b = split_arr loc g in
    if not Effect.(sub_mod mu id e) then
      no_unboxing loc mu e;
    check ctx n a e;
    b
  (* B-Do *)
  | SDo (l, m) ->
    let (a, b) = match Effect.get_eff l e with
      | None -> unknown_eff loc l 
      | Some p -> p
    in
    check ctx m a e;
    b
  (* B-HandlerInfer *)
  | SHand (m, d, (l, (PVar x, n))) ->
    let d = check_effect_ctx ctx d in
    let a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    let b' = infer (ctx <: BVar (x, TMod (MRel ([], d), a))) n e in
    let infer_clause (li, loc, PVar pi, ri, ni) =
      match Effect.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx = ctx <: BVar (pi, ai) <: BVar (ri, TArr (bi, b')) in
        infer ctx ni e
    in
    let bi = List.map infer_clause l in
    List.fold_left (fun t t' -> join_type loc t t' e) b' bi
  | SUnit -> TVar ("unit", Abs)
  | SInt _ -> TVar ("int", Abs)
  (* B-CrispPairInfer *)
  | SLetP (x, y, v, m) ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let mu, g = get_guarded (infer ctx v e) in
    let a, b = split_prod v.loc g in
    let ctx = ctx <: BVar (x, TMod (mu, a)) <: BVar (y, TMod (mu, b)) in
    infer ctx m e
  (* B-CrispSumInfer *) 
  | SMatch (v, x, m1, y, m2) -> 
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let mu, g = get_guarded (infer ctx v e) in
    let a, b = split_sum v.loc g in
    let a1 = infer (ctx <: BVar (x, TMod (mu, a))) m1 e in
    let a2 = infer (ctx <: BVar (y, TMod (mu, b))) m2 e in
    join_type loc a1 a2 e
  | SPair (m, n) ->
    let a = infer ctx m e in
    let b = infer ctx n e in
    TProd (a, b)
  | _ -> failwith "todo"

type shape = Hole | Type of pure_type

let rec infer ctx ({loc; sexpr}) s e = match sexpr, s with
  (* B-Abs *)
  | SLam (x, m), Type a ->
    let (a, b) = split_arr loc a in
    infer (ctx <: BVar (x, a)) m (Type b) e
  (* B-CrispPairInfer *)
  | SLetP (x, y, v, m), s ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let mu, g = get_guarded (infer ctx v Hole e) in
    let a, b = split_prod v.loc g in
    let ctx = ctx <: BVar (x, TMod (mu, a)) <: BVar (y, TMod (mu, b)) in
    infer ctx m s e
  | SSeq (m, n), s ->
    let _ = infer ctx m (Type (TVar ("unit", Abs))) e in
    infer ctx n s e
  | _, _ -> failwith "todo"

let check_decl ctx d = match d with
  | (x, SDSig t), _ ->
    let t = check_type ctx t in
    ctx <: BVar (x, t)
  | (x, SDFun e), loc ->
    let t = match get_type_context ctx.gamma x with
      | None -> missing_declaration loc x
      | Some (t, _) -> t
    in
    check ctx e t []; ctx
  | (x, SDEff (args, l)), _ ->
    let ctx' = List.fold_left (fun ctx x -> ctx <: BType (x, Abs)) ctx args in
    let l =
      List.map (fun (x, (a, b)) ->
        { eff_name = x; eff_type = check_type ctx' a, check_type ctx' b })
         l in
    { ctx with effects = (x, (args, l)) :: ctx.effects }
  | (x, SDADT ([], l)), loc ->
    let rec check_shape c = function
      | TVar (y, _) when y = x -> ()
      | TArr (_, t) -> check_shape c t
      | t -> ill_formed_cons loc x c t
    in
    let l = List.map (fun (c, t) ->
        let t = check_type (ctx <: (BType (x, Abs))) t in
        check_shape c t;
        c, t) l
    in
    { ctx with data = (x, [], l) :: ctx.data }
  |  _ -> failwith "todo"

let check_prog =
  let init_ctx = { gamma = [BType ("int", Abs); BType ("unit", Abs)]
                 ; effects = [] ; data = [] } in
  List.fold_left check_decl init_ctx
