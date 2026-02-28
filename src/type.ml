open Syntax
open Context

let unknown_var loc x = Error.error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = Error.error_str loc ("Unknown effect " ^ x)
let unknown_cons loc c t = Error.error loc (fun fmt -> Format.fprintf fmt
        "Unknown constructor %s of type %s" c t)

let type_mismatch loc _ _ =
  Error.error_str loc "Type mismatch todo"

let expected_arr loc _ = Error.error_str loc "Expected function type todo"
let expected_prod loc _ = Error.error_str loc "Expected product type todo"
let expected_cons loc _ =
  Error.error_str loc "Expected algebraic data type todo"
let expected_forall loc _ =
  Error.error_str loc "Expected forall type for type application todo"
let expected_val loc _ = Error.error_str loc "Expected a value todo"

let mod_mismatch loc _ _ _ = Error.error_str loc "Modality mismatch todo"

let kind_mismatch loc _ _ _ = Error.error_str loc "Kind mismatch todo"

let no_access loc _ _ _ = Error.error_str loc "Cannot access variable todo"

let no_unboxing loc _ _ =
  Error.error_str loc "Cannot unbox function in application todo"

let missing_declaration loc x =
  Error.error_str loc ("Missing declaration for function " ^ x)

let not_cons loc c _ = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Constructor %s is not of the good type" c)

let nb_arg_mismatch loc e a b = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e (List.length a) (List.length b))

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SAnn (m, _)
  | SAppT (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let rec check_type ?(s=[]) ctx t = match t.stype with
  | STMod (m, t) -> TMod (check_mod ctx m, check_type ~s ctx t)
  | STArr (t, t') -> TArr (check_type ~s ctx t, check_type ctx t' ~s)
  | STForA (x, k, t) ->
    TForA (x, k, check_type ~s:(List.remove_assoc x s) (ctx <: BType (x, k)) t)
  | STCons (c, l) ->
    begin match List.assoc_opt c ctx.data with
      | None -> unknown_var t.tloc c
      | Some (args, _) ->
        if List.length args <> List.length l then
          nb_arg_mismatch t.tloc c args l;
        TCons (c, List.map (check_type ~s ctx) l)
    end
  | STVar x ->
    match List.assoc_opt x s with
    | Some t -> t
    | None ->
      match get_kind ctx.gamma x with
      | Some k ->
        if k = Effect then
          kind_mismatch t.tloc t k Any;
        TVar (x, k)
      | None ->
        match List.assoc_opt x ctx.data with
        | None -> unknown_var t.tloc x
        | Some _ -> TCons (x, [])

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
          nb_arg_mismatch eloc seff_name args seff_args;
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
  | a ->
    expected_arr loc a

let split_forall loc = function
  | TForA (x, k, t) -> x, k, t
  | a -> expected_forall loc a

let split_cons loc = function
  | TCons (c, l) -> c, l
  | a -> expected_cons loc a

let rec split_pat ctx mu t { spat; ploc } =
  let nu, g = get_guarded t in
  let mu = Effect.compose mu nu in
  match spat with
  | SPWild -> ctx
  | SPVar x -> ctx <: BVar (x, TMod (mu, g))
  | SPCons (c, l) ->
    let tc, tl = split_cons ploc g in
    let args, cons = List.assoc tc ctx.data in
    let tcons = match List.assoc_opt c cons with
      | None -> not_cons ploc c g
      | Some tcons ->
        let s = List.combine args tl in
        List.map (Subst.pure_type s) tcons
    in
    List.fold_right (fun (a, p) ctx ->
        split_pat ctx mu a p) (List.combine tcons l) ctx

let join_type loc f t t' =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g = g' then
    type_mismatch loc g g';
  if is_abs g then
    g
  else match Effect.join_mod mu nu f with
    | None -> mod_mismatch loc mu nu g
    | Some lam -> TMod (lam, g)

let rec check ctx ({loc; sexpr} as m) a e =
  match sexpr with
  (* B-Mod *)
  | v when is_val v && is_mod a ->
    begin match a with
      | TMod (mu, a) ->
        check (ctx <: Lock (mu, e)) m a (Effect.apply_mod mu e)
      | _ -> failwith "impossible"
    end
  (* B-Forall *)
  | v when is_val v && is_forall a ->
    let x, k, a = split_forall loc a in
    check (ctx <: BType (x, k)) m a e
  (* B-Abs *)
  | SLam (x, m) ->
    let (a, b) = split_arr loc a in
    check (ctx <: BVar (x, a)) m b e
  (* B-HandlerCheck *)
  | SHand (m, d, (l, (x, n))) ->
    let b = a in (* stay consistent with the paper *)
    let d = check_effect_ctx ctx d in
    let a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    check (ctx <: BVar (x, TMod (MRel ([], d), a))) n b e;
    let check_clause (li, loc, pi, ri, ni) =
      match Effect.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx = ctx <: BVar (pi, ai) <: BVar (ri, TArr (bi, b)) in
        check ctx ni b e
    in
    List.iter check_clause l
  (* B-CrispSumCheck and B-CrispPairCheck *)
  | SMatch (v, l) ->
    (*if not (is_val v.sexpr) then
       expected_val v.loc v;*)
    let t = infer ctx v e in
    List.iter (fun (p, n) ->
        let ctx = split_pat ctx Effect.id t p in
        check ctx n a e) l
  | SSeq (m, n) ->
    let _ = check ctx m (TCons ("unit", [])) e in
    check ctx n a e
  | SCons (c, l) ->
    let tc, tl = split_cons loc a in
    let tcargs, constructors = List.assoc tc ctx.data in
    begin
      match List.assoc_opt c constructors with
      | None -> unknown_cons loc c tc
      | Some cargs ->
        let cargs = List.map (Subst.pure_type (List.combine tcargs tl)) cargs in
        if List.length cargs <> List.length l then
          nb_arg_mismatch loc c cargs l;
        List.iter2 (fun n b -> check ctx n b e) l cargs
  end
  | SLet (x, m, n) ->
    let t = infer ctx m e in
    check (ctx <: BVar (x, t)) n a e
  (* B-Switch *)
  | _ ->
    let mu, g = get_guarded (infer ctx m e) in
    let nu, g' = get_guarded a in
    if g <> g' then type_mismatch loc g g'
    else
      if not (Effect.sub_mod mu nu e) && not (is_abs g) then
        mod_mismatch loc mu nu g

and infer ctx {loc; sexpr} e =
  match sexpr with
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
  (* B-AppT *)
  | SAppT (m, ({tloc; _} as t)) ->
    let t = check_type ctx t in
    let mu, g = get_guarded (infer ctx m e) in
    if not Effect.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let x, k, b = split_forall loc g in
    if k = Abs && not (is_abs t) then
      kind_mismatch tloc t Abs Any;
    Subst.pure_type [x, t] b
  (* B-Do *)
  | SDo (l, m) ->
    let (a, b) = match Effect.get_eff l e with
      | None -> unknown_eff loc l
      | Some p -> p
    in
    check ctx m a e;
    b
  (* B-HandlerInfer *)
  | SHand (m, d, (l, (x, n))) ->
    let d = check_effect_ctx ctx d in
    let a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    let b' = infer (ctx <: BVar (x, TMod (MRel ([], d), a))) n e in
    let infer_clause (li, loc, pi, ri, ni) =
      match Effect.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx = ctx <: BVar (pi, ai) <: BVar (ri, TArr (bi, b')) in
        infer ctx ni e
    in
    let bi = List.map infer_clause l in
    List.fold_left (join_type loc e) b' bi
  | SInt _ -> TCons ("int", [])
  | SStr _ -> TCons ("string", [])
  (* B-CrispSumInfer and B-CrispPairInfer *)
  | SMatch (v, l) ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let t = infer ctx v e in
    let types = List.map (fun (p, n) ->
        let ctx = split_pat ctx Effect.id t p in
        infer ctx n e) l in
    List.fold_left (join_type loc e) (List.hd types) (List.tl types)
  | SSeq (m, n) ->
    let _ = check ctx m (TCons ("unit", [])) e in
    infer ctx n e
  | SLet (x, m, n) ->
    let t = infer ctx m e in
    infer (ctx <: BVar (x, t)) n e
  | _ ->
    failwith "todo"

let check_decl ctx d = match d with
  | (x, SDSig t), _ ->
    let t = check_type ctx t in
    let t = if is_mod t then t else TMod (MAbs [], t) in
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
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let ctx' = { ctx with data = (x, (args, [])) :: ctx.data } in
    let ctx' = List.fold_left (fun ctx x -> ctx <: BType (x, Any)) ctx' args in
    let l = List.map (Pair.map_snd (List.map (check_type ctx'))) l in
    { ctx with data = (x, (args, l)) :: ctx.data }

let check_prog =
  let int = TCons ("int", []) in
  let bool = TCons ("bool", []) in
  let string = TCons ("string", []) in
  let unit = TCons ("unit", []) in
  let (@->) t t' = TArr (t, t') in
  let init_ctx = { gamma = [BVar ("+", TMod (MAbs [], int @-> int @-> int));
                            BVar ("*", TMod (MAbs [], int @-> int @-> int));
                            BVar ("-", TMod (MAbs [], int @-> int @-> int));
                            BVar ("=", TMod (MAbs [], int @-> int @-> bool));
                            BVar ("string_eq", TMod (MAbs [], string @-> string @-> bool));
                            BVar ("^", TMod (MAbs [], string @-> string @-> string));
                            BVar ("&&", TMod (MAbs [], bool @-> bool @-> bool));
                            BVar ("fail", TMod (MAbs [], TForA ("f", Any, unit @-> (TVar ("f", Any)))));
                            BVar ("print", TMod (MAbs [], string @-> unit))
                           ]
                 ; effects = []
                 ; data = ["int", ([], []); "string", ([], [])] } in
  List.fold_left check_decl init_ctx
