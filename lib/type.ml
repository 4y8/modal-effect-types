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

let two_effect_var loc =
  Error.error_str loc "Cannot have two effect variables in a single row"

let not_cons loc c _ = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Constructor %s is not of the good type" c)

let nb_arg_mismatch loc e n l = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e n (List.length l))

let non_last_evar loc e = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Effect type variable %s should be at the end of the row" e)

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SAnn (m, _)
  | SAppT (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let (<<<) k k' =
  k = k' || (k = Abs && k' = Any)

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let rec check_type ctx t =
  let check_type_kind_any ctx t =
    check_type_kind ctx t Any
  in
  match t.stype with
  | STMod (m, t) ->
    TMod (check_mod ctx m, check_type_kind_any ctx t)
  | STArr (t, t') ->
    TArr (check_type_kind_any ctx t, check_type_kind_any ctx t')
  | STForA (x, k, a) ->
    let ctx, v = fresh_tvar ctx x k in
    let a = check_type_kind_any ctx a in
    TForA (k, Bindlib.(box_type a |> bind_var v |> unbox))
  | STCons (c, l) ->
    begin match List.assoc_opt c ctx.data with
      | None -> unknown_var t.tloc c
      | Some { targs; _ } ->
        if List.length targs <> List.length l then
          nb_arg_mismatch t.tloc c (List.length targs) l;
        let args = Array.of_list @@ List.map2 (check_type_kind ctx)
            l targs in
        TCon (c, args)
    end
  | SECtx e -> ECtx (check_effect_ctx ctx e)
  | STVar x ->
    match List.assoc_opt x ctx.tid with
    | Some v ->
      TVar v
    | None ->
      match List.assoc_opt x ctx.data with
      | None -> unknown_var t.tloc x
      | Some _ -> TCon (x, [||])
and check_type_kind ctx t k =
  let a = check_type ctx t in
  let k' = get_kind ctx a in
  if not (k' <<< k) then
    kind_mismatch t.tloc a k k';
  a

and check_mod ctx m = match m.smod with
  | SMAbs e -> MAbs (check_effect_ctx ctx e)
  | SMRel (l, d) ->
    MRel (check_mask ctx l, check_effect_ext ctx d)

and check_effect ctx { seff_name; seff_args; eloc } args_kind t =
  if List.length args_kind <> List.length seff_args then
    nb_arg_mismatch eloc seff_name (List.length args_kind) seff_args;
  let eff_args = List.map2 (check_type_kind ctx) seff_args args_kind
    |> Array.of_list in
  let ectx = Bindlib.msubst t eff_args in
  List.iter (fun { op_in; op_out; _ } ->
      if not (is_abs ctx op_in) then kind_mismatch eloc op_in Abs Any;
      if not (is_abs ctx op_out) then kind_mismatch eloc op_out Abs Any) ectx;
  { eff_name = seff_name; eff_args }

and check_effect_ext ctx l =
  List.map (fun ({ seff_name; eloc; _ } as seff) ->
      match List.assoc_opt seff_name ctx.effects with
      | None -> unknown_eff eloc seff_name
      | Some { eargs ; eops } -> check_effect ctx seff eargs eops) l

and check_effect_ctx ctx l =
  List.fold_right (fun ({ seff_name; eloc; _ } as seff) (d, eps) ->
      match List.assoc_opt seff_name ctx.effects with
      | Some { eargs ; eops } ->
        if not Option.(is_none eps) then
          non_last_evar eloc seff_name;
        (check_effect ctx seff eargs eops :: d, eps)
      | None ->
        match List.assoc_opt seff_name ctx.tid with
        | None -> unknown_eff eloc seff_name
        | Some v ->
          if get_var_kind ctx.gamma v <> Effect then
            kind_mismatch eloc (TVar v) Effect (get_var_kind ctx.gamma v);
          match eps with
          | None -> d, Some (TVar v, [])
          | Some _ -> two_effect_var eloc)
    l ([], None)

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
  | TForA (k, a) -> k, a
  | a -> expected_forall loc a

let split_foralls a =
  let rec aux l = function
    | TForA (k, b) ->
      let v, a = Bindlib.unbind b in
      aux ((v, k) :: l) a
    | a -> a, l
  in Pair.map_snd List.rev @@ aux [] a

let split_cons loc = function
  | TCon (c, l) -> c, l
  | a -> expected_cons loc a

let ectx_of_type = function
  | ECtx e -> e
  | TVar v -> ([], Some (TVar v, []))
  | _ -> failwith "internal error: ectx_of_type"

let rec split_pat ctx vars mu t { spat; ploc } =
  let nu, g = get_guarded t in
  let mu = Effects.compose mu nu in
  match spat with
  | SPWild -> (ctx, vars), PWild
  | SPVar x ->
    let ctx, v = fresh_var ctx x (TMod (mu, g)) in
    (ctx, (v :: vars)), PVar (TMod (mu, g))
  | SPCons (c, l) ->
    let tc, tl = split_cons ploc g in
    let { cons; _ } = List.assoc tc ctx.data in
    let tcons = match List.assoc_opt c cons with
      | None -> not_cons ploc c g
      | Some tcons -> Bindlib.msubst tcons tl
    in
    let res, l = List.fold_right
        (fun (a, p) ((ctx, vars), l) ->
           Pair.map_snd (fun x -> x :: l) @@ split_pat ctx vars mu a p)
        (List.combine tcons l) ((ctx, vars), [])
    in res, PCon (c, l)

let unfold_ext ctx d =
  List.map (fun { eff_name; eff_args } ->
      let { eops; _ } = List.assoc eff_name ctx.effects in
      Bindlib.msubst eops eff_args) d |> List.flatten

let join_type loc ctx f t t' =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g <> g' then
    type_mismatch loc g g';
  if is_abs ctx g then
    g
  else match Effects.join_mod mu nu f with
    | None -> mod_mismatch loc mu nu g
    | Some lam -> TMod (lam, g)

let rec check ctx ({loc; sexpr} as m) a e =
  match sexpr with
  (* B-Mod *)
  | v when is_val v && is_mod a ->
    begin match a with
      | TMod (mu, a) ->
        check (ctx <: Lock (mu, e)) m a (Effects.apply_mod mu e)
      | _ -> failwith "impossible"
    end
  (* B-Forall *)
  | v when is_val v && is_forall a ->
    let k, a = split_forall loc a in
    let v, a = Bindlib.unbind a in
    check (ctx <: BType (v, k)) m a e
  (* B-Abs *)
  | SLam (x, m) ->
    let (a, b) = split_arr loc a in
    let ctx, v = fresh_var ctx x a in
    let m = check ctx m b e in
    Lam (a, Bindlib.(box_expr m |> bind_var v |> unbox))
  (* B-HandlerCheck *)
  | SHand (m, d, (l, (x, n))) ->
    let b = a in (* stay consistent with the paper *)
    let d = check_effect_ext ctx d in
    let ops = unfold_ext ctx d in
    let m, a = infer (ctx <: Lock (MRel ([], d), e)) m (Effects.extend d e) in
    let ctx', ret = fresh_var ctx x (TMod (MRel ([], d), a)) in
    let n = Bindlib.(check ctx' n b e |> box_expr |> bind_var ret |> unbox) in
    let check_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx, pi = fresh_var ctx pi ai in
        let ctx, ri = fresh_var ctx ri (TArr (bi, b)) in
        li, Bindlib.(check ctx ni b e |> box_expr |> bind_var ri |> bind_var pi
                  |> unbox)
    in
    Hand (m, ops, n,  List.map check_clause l)
  (* B-CrispSumCheck and B-CrispPairCheck *)
  | SMatch (v, l) ->
    let m, t = infer ctx v e in
    let l =
      List.map (fun (p, n) ->
          let (ctx, vars), p = split_pat ctx [] Effects.id t p in
          let mvar = Array.of_list vars in
          p, Bindlib.(check ctx n a e |> box_expr |> bind_mvar mvar |> unbox)) l
    in Match (m, l)
  | SSeq (m, n) ->
    let m = check ctx m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    Let (m, TCon ("unit", [||]),
         Bindlib.(check ctx n a e |> box_expr |> bind_var dummy |> unbox))
  | SCons (c, l) ->
    let tc, tl = split_cons loc a in
    let { cons ; _ } = List.assoc tc ctx.data in
    begin
      match List.assoc_opt c cons with
      | None -> unknown_cons loc c tc
      | Some cargs ->
        let cargs = Bindlib.msubst cargs tl in
        if List.length cargs <> List.length l then
          nb_arg_mismatch loc c (List.length cargs) l;
        Con (c, List.map2 (fun n b -> check ctx n b e) l cargs)
  end
  | SLet (x, m, n) ->
    let m, t = infer ctx m e in
    let ctx, v = fresh_var ctx x t in
    Let (m, t, Bindlib.(check ctx n a e |> box_expr |> bind_var v |> unbox))
  (* B-Switch *)
  | _ ->
    let m, b = infer ctx m e in
    let mu, g = get_guarded b in
    let nu, g' = get_guarded a in
    if not Effects.(eq_ty g g') then type_mismatch loc g g'
    else
      if not (Effects.sub_mod mu nu e) && not (is_abs ctx g) then
        mod_mismatch loc mu nu g
      else
        m

and infer ctx {loc; sexpr} e =
  match sexpr with
  (* B-Var *)
  | SVar x ->
    begin match List.assoc_opt x ctx.id with
      | None -> unknown_var loc x
      | Some v ->
        let _, a, gamma' = get_type_context ctx.gamma v in
        let nu, f = locks e gamma' in
        match across ctx a nu f with
        | None -> no_access loc x ctx e
        | Some t -> Var v, t
    end
  (* B-Annotation *)
  | SAnn (m, a) ->
    let a = check_type ctx a in
    let m = check ctx m a e in
    m, a

  (* B-App *)
  | SApp (m, n) ->
    let m, a = infer ctx m e in
    let mu, g = get_guarded a in
    let a, b = split_arr loc g in
    if not Effects.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let n = check ctx n a e in
    App (m, n), b

  (* B-AppT *)
  | SAppT (m, ({tloc; _} as a)) ->
    let a = check_type ctx a in
    let m, b = infer ctx m e in
    let mu, g = get_guarded b in
    if not Effects.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let k, b = split_forall loc g in
    let k' = get_kind ctx a in
    if not (k' <<< k) then
      kind_mismatch tloc a k k';
    m,
    if k = Effect then Effects.subst b (ectx_of_type a) else Bindlib.subst b a

  (* B-Do *)
  | SDo (l, m) ->
    let ops = unfold_ext ctx (fst e) in
    let (a, b) = match Effects.get_op l ops with
      | None -> unknown_eff loc l
      | Some p -> p
    in
    let m = check ctx m a e in
    Do (l, m), b

  (* B-HandlerInfer *)
  | SHand (m, d, (l, (x, n))) ->
    let d = check_effect_ext ctx d in
    let ops = unfold_ext ctx d in
    let m, a = infer (ctx <: Lock (MRel ([], d), e)) m (Effects.extend d e) in
    let ctx', ret = fresh_var ctx x (TMod (MRel ([], d), a)) in
    let n, b' = infer ctx' n e in
    let n = Bindlib.(box_expr n |> bind_var ret |> unbox ) in
    let infer_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx, pi = fresh_var ctx pi ai in
        let ctx, ri = fresh_var ctx ri (TArr (bi, b')) in
        let ni, bi = infer ctx ni e in
        (li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi |> unbox)), bi
    in
    let h, bi = List.map infer_clause l |> List.split in
    let b = List.fold_left (join_type loc ctx e) b' bi in
    Hand (m, ops, n, h), b
  | SInt n -> Lit (Int n), TCon ("int", [||])
  | SStr s -> Lit (Str s), TCon ("string", [||])

  (* B-CrispSumInfer and B-CrispPairInfer *)
  | SMatch (v, l) ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let m, t = infer ctx v e in
    let c, types = List.map (fun (p, n) ->
        let (ctx, vars), p = split_pat ctx [] Effects.id t p in
        let mvar = Array.of_list vars in
        let n, t = infer ctx n e in
        (p, Bindlib.(box_expr n |> bind_mvar mvar |> unbox)), t) l
      |> List.split in
    let a = List.(fold_left (join_type loc ctx e) (hd types) (tl types)) in
    Match (m, c), a
  | SSeq (m, n) ->
    let m = check ctx m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    let n, a = infer ctx n e in
    Let (m, TCon ("unit", [||]),
         Bindlib.(n |> box_expr |> bind_var dummy |> unbox)), a
  | SLet (x, m, n) ->
    let m, a = infer ctx m e in
    let ctx, v = fresh_var ctx x a in
    let n, b = infer ctx n e in
    Let (m, a, Bindlib.(n |> box_expr |> bind_var v |> unbox)), b
  | _ ->
    print_endline (show_surface_desc sexpr);
    failwith "todo"

let check_decl (ctx, prog) d = match d with
  | (x, SDSig t), _ ->
    let t = check_type ctx t in
    let ctx, _ = fresh_var ctx x t in
    ctx, prog
  | (x, SDFun e), loc ->
    let v = match List.assoc_opt x ctx.id with
      | None -> missing_declaration loc x
      | Some v -> v
    in
    let _, a, _ = get_type_context ctx.gamma v in
    let g, alphas = split_foralls a in
    let ctx' = { ctx with
                 tid = List.map (fun (v, _) -> Bindlib.name_of v, v) alphas
               ; gamma = List.map (fun (v, k) -> BType (v, k)) alphas @
                         ctx.gamma }
    in
    let _ = check ctx' e g ([], None) in ctx, (x, e) :: prog
  | (x, SDEff (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let eargs = snd (List.split args) in
    let ctx', mvar = fresh_tvars ctx args in
    let dummy_ops = Bindlib.(box_list [] |> bind_mvar mvar |> unbox) in
    let ctx' = { ctx' with effects = (x, { eargs; eops = dummy_ops }) ::
                                     ctx'.effects } in
    let l =
      List.map (fun (x, (a, b)) ->
        { op_name = x; op_in = check_type ctx' a; op_out = check_type ctx' b })
        l |> box_ops in
    { ctx with
      effects = (x, { eargs; eops = Bindlib.(bind_mvar mvar l |> unbox)}) ::
                ctx.effects }, prog
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let targs = snd (List.split args) in
    let ctx' = { ctx with data = (x, { targs; cons = [] }) :: ctx.data } in
    let ctx', mvar = fresh_tvars ctx' args in
    let cons = List.map
        (fun (c, l) ->
           let l = List.map (Fun.compose box_type (check_type ctx')) l
                |> Bindlib.box_list in
           c, Bindlib.(bind_mvar mvar l |> unbox)) l in
    { ctx with data = (x, { targs; cons }) :: ctx.data }, prog

let check_prog =
  let int = TCon ("int", [||]) in
  let bool = TCon ("bool", [||]) in
  let string = TCon ("string", [||]) in
  let unit = TCon ("unit", [||]) in
  let (@->) t t' = TArr (t, t') in
  let v = Bindlib.new_var (fun v -> TVar v) "fail" in
  let abs t = TMod (MAbs ([], None), t) in
  let init_ctx, _ =
    fresh_vars
      { gamma = [] ; tid = [] ; id = [] ; effects = []
      ; data = ["int", { targs = [] ; cons = [] };
                "string", { targs = [] ; cons = [] } ] }
      [("+", abs (int @-> int @-> int));
       ("*", abs (int @-> int @-> int));
       ("-", abs (int @-> int @-> int));
       ("=", abs (int @-> int @-> bool));
       ("string_eq", abs (string @-> string @-> bool));
       ("^", abs (string @-> string @-> string));
       ("&&", abs (bool @-> bool @-> bool));
       ("fail", abs (TForA (Any, Bindlib.(unit @-> (TVar v) |> box_type |> bind_var v |> unbox))));
       ("print", abs (string @-> unit))]
  in
  Fun.compose snd (List.fold_left check_decl (init_ctx, []))
