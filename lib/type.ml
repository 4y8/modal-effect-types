open Syntax
open Context
open Errors

let rec is_val = function
  | SVar _ -> true
  | SLam _ -> true
  | SAnn (m, _)
  | SAppT (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let (<<<) k k' =
  k = k' || (k = Abs && k' = Any)

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let rec check_type t =
  let check_type_any t =
    check_type_kind t Any
  in
  match t.stype with
  | STMod (mu, a) ->
    let* mu = check_mod mu in
    let* a = check_type_any a in
    return @@ TMod (mu, a)
  | STArr (a, b) ->
    let* a = check_type_any a in
    let* b = check_type_any b in
    return @@ TArr (a, b)
  | STForA (x, k, a) ->
    protect_context @@
    let* v = fresh_tvar x k in
    let* a = check_type_any a in
    return @@ TForA (k, Bindlib.(unbox (bind_var v (box_type a))))
  | STCons (c, l) ->
    let* cons = lookup_data c in
    begin match cons with
      | None -> unknown_var t.tloc c
      | Some { targs; _ } ->
        if List.length targs <> List.length l then
          nb_arg_mismatch t.tloc c (List.length targs) l;
        let* args = M.List.map2 check_type_kind
            l targs $> Array.of_list in
        return @@ TCon (c, args)
    end
  | SECtx e ->
    let* ectx = check_effect_ctx e in
    return @@ ECtx ectx
  | STVar x ->
    let* tid = lookup_tid x in
    match tid with
    | Some v -> return @@ TVar v
    | None ->
      let* ty = lookup_data x in
      match ty with
      | Some { targs = []; _ } -> return @@ TCon (x, [||])
      | _ -> unknown_var t.tloc x

and check_type_kind t k =
  let* a = check_type t in
  let* k' = get_kind a in
  if not (k' <<< k) then
    kind_mismatch t.tloc a ~expected:k ~got:k';
  return a

and check_mod m = match m.smod with
  | SMAbs e ->
    let* ectx = check_effect_ctx e in
    return @@ MAbs ectx
  | SMRel (l, d) ->
    let* l = check_mask l in
    let* d = check_effect_ext d in
    return @@ MRel (l, d)

and check_effect { seff_name; seff_args; eloc } args_kind t =
  if List.length args_kind <> List.length seff_args then
    nb_arg_mismatch eloc seff_name (List.length args_kind) seff_args;
  let* eff_args = M.List.map2 check_type_kind seff_args args_kind
    $> Array.of_list in
  let ectx = Bindlib.msubst t eff_args in
  M.List.iter (fun { op_in; op_out; _ } ->
      unless (is_abs op_in)
        (fun () ->
           Format.printf "%a@." Pprint.ty op_in;
           kind_mismatch eloc op_in ~expected:Abs ~got:Any) >>
      unless (is_abs op_out)
        (fun () ->
           kind_mismatch eloc op_out ~expected:Abs ~got:Any)) ectx >>
  return { eff_name = seff_name; eff_args }

and check_effect_ext l =
  M.List.map (fun ({ seff_name; eloc; _ } as seff) ->
      let* eff = lookup_eff seff_name in
      match eff with
      | None -> unknown_eff eloc seff_name
      | Some { eargs ; eops } -> check_effect seff eargs eops) l

and check_effect_ctx l =
  M.List.fold_right (fun ({ seff_name; eloc; _ } as seff) (d, eps) ->
      let* eff = lookup_eff seff_name in
      match eff with
      | Some { eargs ; eops } ->
        let* e = check_effect seff eargs eops in
        return (e :: d, eps)
      | None ->
        let* v = lookup_tid seff_name in
        match v with
        | None -> unknown_eff eloc seff_name
        | Some v ->
          let* k = get_var_kind v in
          if k <> Effect then
            kind_mismatch eloc (TVar v) ~expected:Effect
              ~got:k;
          if not List.(is_empty d) then
            non_last_evar eloc seff_name;
          if Option.is_some eps then
            two_effect_var eloc;
          return ([], Some (TVar v, [])))
    l ([], None)

and check_mask l =
  M.List.map (fun (e, loc) ->
      let* eff = lookup_eff e in
      if Option.is_none eff then
        unknown_eff loc e;
      return e) l

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

let rec split_pat vars mu t { spat; ploc } =
  let nu, g = get_guarded t in
  let mu = Effects.compose mu nu in
  match spat with
  | SPWild -> return (vars, PWild)
  | SPVar x ->
    let* v = fresh_var x (TMod (mu, g)) in
    return (v :: vars, PVar (TMod (mu, g)))
  | SPCons (c, l) ->
    let tc, tl = split_cons ploc g in
    let* { cons; _ } = get_data tc in
    let tcons = match List.assoc_opt c cons with
      | None -> not_cons ploc c g
      | Some tcons -> Bindlib.msubst tcons tl
    in
    let* res, l = M.List.fold_right
        (fun (a, p) (vars, l) ->
           split_pat vars mu a p $>
           Pair.map_snd (fun x -> x :: l))
        (List.combine tcons l) (vars, [])
    in return (res, PCon (c, l))

let unfold_ext d =
  M.List.map (fun { eff_name; eff_args } ->
      let* { eops; _ } = get_eff eff_name in
      return @@ Bindlib.msubst eops eff_args) d $> List.flatten $>
  List.map (fun { op_name; op_in; op_out } ->
      { op_name ; op_in = Effects.norm_ty op_in
      ; op_out = Effects.norm_ty op_out })

let join_type loc f t t' =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g <> g' then
    type_mismatch loc ~expected:g ~got:g';
  let* abs = is_abs g in
  if abs then
    return g
  else match Effects.join_mod mu nu f with
    | None -> mod_mismatch loc ~expected:mu ~got:nu f
    | Some lam -> return @@ TMod (lam, g)

let rec check ({loc; sexpr} as m) a e =
  match sexpr, a with
  (* B-Mod && T-ModAbs *)
  | v, TMod (mu, a) when is_val v || mu = MAbs (([], None)) ->
    with_binding (Lock (mu, e)) @@
    check m a (Effects.apply_mod mu e)

  (* B-Forall *)
  | v, TForA (k, a) when is_val v ->
    let v, a = Bindlib.unbind a in
    with_binding (BType (v, k)) @@ check m a e

  (* B-Abs *)
  | SLam (x, None, m), TArr (a, b) ->
    protect_context @@
    let* v = fresh_var x a in
    let* m = check m b e in
    return @@ Lam (Bindlib.(box_expr m |> bind_var v |> unbox))

  | SLam _, a ->
    function_non_arr loc a

  (* B-MaskCheck *)
  | SMask (l, m), TMod (MRel (l', []), a)
    when Effects.eq_mask (List.split l |> fst) l' ->
    let l, _ = List.split l in
    let* m = check m a (Effects.remove_labels e l) in
    return @@ Mask (l, m)

  (* B-HandlerCheck *)
  | SHand (m, Some d, mu, (l, (x, n))), a ->
    let b = a in (* stay consistent with the paper *)
    let f = e in
    let* mu = M.List.map check_mod mu
      $> List.fold_left Effects.compose Effects.id in
    if not Effects.(sub_mod mu id f) then
      no_unboxing loc mu f;
    let e = Effects.apply_mod mu f in
    let* d = check_effect_ext d in
    let* ops = unfold_ext d in
    let nu = MRel ([], d) in
    with_binding (Lock (mu, f)) @@
    let* m, a = with_binding (Lock (nu, e)) @@
      infer m (Effects.extend d e) in
    let* ret, n =
      protect_context @@
      let* ret = fresh_var x (TMod (Effects.compose mu nu, a)) in
      let* n = check n b e in
      return (ret, n)
    in
    let n = Bindlib.(n|> box_expr |> bind_var ret |> unbox) in
    let check_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        protect_context @@
        let* pi = fresh_var pi ai in
        let* ri = fresh_var ri (TMod (mu, TArr (bi, b))) in
        let* ni = check ni b e in
        return (li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi
                             |> unbox))
    in
    let* l = M.List.map check_clause l in
    return @@ Hand (m, ops, n, l)

  (* B-CrispSumCheck and B-CrispPairCheck *)
  | SMatch (v, l), a ->
    let* m, b = infer v e in
    let* l =
      M.List.map (fun (p, n) ->
          protect_context @@
          let* vars, p = split_pat [] Effects.id b p in
          let mvar = Array.of_list vars in
          let* n = check n a e in
          return (p, Bindlib.(n |> box_expr |> bind_mvar mvar |> unbox))) l
    in return @@ Match (m, l)

  | SSeq (m, n), a ->
    let* m = check m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    let* n = check n a e in
    return @@
    Let (m, TCon ("unit", [||]),
         Bindlib.(n |> box_expr |> bind_var dummy |> unbox))

  | SCons (c, l), a ->
    let tc, tl = split_cons loc a in
    let* { cons; _ } = get_data tc in
    begin
      match List.assoc_opt c cons with
      | None -> unknown_cons loc c (Some tc)
      | Some cargs ->
        let cargs = Bindlib.msubst cargs tl in
        if List.length cargs <> List.length l then
          nb_arg_mismatch loc c (List.length cargs) l;
        let* l = M.List.map2 (fun n b -> check n b e) l cargs in
        return @@ Con (c, l)
  end
  | SLet (x, m, n), a ->
    let* m, b = infer m e in
    protect_context @@
    let* v = fresh_var x b in
    let* n = check n a e in
    return @@
    Let (m, b, Bindlib.(n |> box_expr |> bind_var v |> unbox))

  (* B-Switch *)
  | _ ->
    let* m, b = infer m e in
    let mu, g = get_guarded b in
    let nu, g' = get_guarded a in
    if not Effects.(eq_ty g g') then type_mismatch loc ~expected:g' ~got:g
    else
      if not (Effects.sub_mod mu nu e) then begin
        unless (is_abs g) (fun () ->
            mod_mismatch loc ~got:mu ~expected:nu e) >>
        return m
      end
      else
        return m

and infer {loc; sexpr} e =
  match sexpr with

  (* B-Var *)
  | SVar x ->
    let* id = lookup_id x in
    begin match id with
      | None -> unknown_var loc x
      | Some v ->
        let* _, a, gamma' = get_type_context v in
        let nu, f = locks e gamma' in
        let* a = across a nu f in
        match a with
        | None -> no_access loc x v e
        | Some a -> return (Var v, a)
    end

  (* B-Annotation *)
  | SAnn (m, a) ->
    let* a = check_type a in
    let* m = check m a e in
    return (m, a)

  (* B-MaskInfer *)
  | SMask (l, m) ->
    M.List.iter (fun (l, loc) ->
        let* eff = lookup_eff l in
        if Option.is_none eff then
          unknown_eff loc l;
        return ()) l >>
    let l, _ = List.split l in
    let* m, a = infer m (Effects.remove_labels e l) in
    let* lext = M.List.map (fun l ->
        let* { eops; _ } = get_eff l in
        return @@
        List.map (fun { op_name; _ } -> op_name) (snd Bindlib.(unmbind eops))) l
       $> List.flatten in
    return (Mask (lext, m), TMod (MRel (l, []), a))

  (* B-App *)
  | SApp (m, n) ->
    let* m, a = infer m e in
    let mu, g = get_guarded a in
    let a, b = match g with
      | TArr (a, b) -> a, b
      | a -> apply_non_arr loc a
    in
    if not Effects.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let* n = check n a e in
    return (App (m, n), b)

  (* B-AppT *)
  | SAppT (m, ({tloc; _} as a)) ->
    let* a = check_type a in
    let* m, b = infer m e in
    let mu, g = get_guarded b in
    if not Effects.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let k, b = split_forall loc g in
    let* k' = get_kind a in
    if not (k' <<< k) then
      kind_mismatch tloc ~expected:k ~got:k' a;
    return (m, Effects.norm_ty @@ Bindlib.subst b a)

  (* B-Do *)
  | SDo (l, m) ->
    let* ops = unfold_ext (fst e) in
    let (a, b) = match Effects.get_op l ops with
      | None -> unknown_eff loc l
      | Some p -> p
    in
    let* m = check m a e in
    return (Do (l, m), b)

  (* B-HandlerInfer *)
  | SHand (m, Some d, mu, (l, (x, n))) ->
    let f = e in
    let* mu = M.List.map check_mod mu
      $> List.fold_left Effects.compose Effects.id in
    if not Effects.(sub_mod mu id f) then
      no_unboxing loc mu f;
    let e = Effects.apply_mod mu f in
    let* d = check_effect_ext d in
    let* ops = unfold_ext d in
    let nu = MRel ([], d) in
    with_binding (Lock (mu, f)) @@
    let* m, a = with_binding (Lock (nu, e)) @@
      infer m (Effects.extend d e) in
    let* ret, n, b' =
      protect_context @@
      let* ret = fresh_var x (TMod (Effects.compose mu nu, a)) in
      let* n, b' = infer n e in
      return (ret, n, b')
    in
    let n = Bindlib.(n|> box_expr |> bind_var ret |> unbox) in

    let infer_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        protect_context @@
        let* pi = fresh_var pi ai in
        let* ri = fresh_var ri (TMod (mu, TArr (bi, b'))) in
        let* ni, bi = infer ni e in
        return ((li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi
                             |> unbox)), bi)
    in
    let* h, bi = M.List.map infer_clause l $> List.split in
    let* b = M.List.fold_left (join_type loc e) b' bi in
    return (Hand (m, ops, n, h), b)
  | SInt n -> return (Lit (Int n), TCon ("int", [||]))
  | SStr s -> return (Lit (Str s), TCon ("string", [||]))

  (* B-CrispSumInfer and B-CrispPairInfer *)
  | SMatch (v, l) ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let* m, a = infer v e in
    let* c, types = M.List.map (fun (p, n) ->
        protect_context @@
        let* vars, p = split_pat [] Effects.id a p in
        let mvar = Array.of_list vars in
        let* n, a = infer n e in
        return ((p, Bindlib.(box_expr n |> bind_mvar mvar |> unbox)), a)) l
      $> List.split in
    let hty, tty = List.hd types, List.tl types in
    let* a = M.List.(fold_left (join_type loc e) (hty) (tty)) in
    return (Match (m, c), a)

  | SSeq (m, n) ->
    let* m = check m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    let* n, a = infer n e in
    return (Let (m, TCon ("unit", [||]),
                 Bindlib.(box_expr n |> bind_var dummy |> unbox)), a)
  | SLet (x, m, n) ->
    let* m, a = infer m e in
    let* n, b, v = protect_context @@
      let* v = fresh_var x a in
      let* n, b = infer n e in
      return (n, b, v) in
    return (Let (m, a, Bindlib.(box_expr n |> bind_var v |> unbox)), b)

  | _ ->
    cannot_infer_expr loc

let check_decl (prog, ctx) d = match d with
  | (x, SDSig t), _ ->
    let a,_ = check_type t ctx in
    let _, ctx = fresh_var x a ctx in
    prog, ctx
  | (x, SDFun e), loc ->
    let v = match List.assoc_opt x ctx.id with
      | None -> missing_declaration loc x
      | Some v -> v
    in
    let (_, a, _), ctx = get_type_context v ctx in
    let g, alphas = split_foralls a in
    let ctx' = { ctx with
                 tid = List.map (fun (v, _) -> Bindlib.name_of v, v) alphas
               ; gamma = List.map (fun (v, k) -> BType (v, k)) alphas @
                         ctx.gamma }
    in
    let m, _ = check e g ([], None) ctx' in (v, m) :: prog, ctx
  | (x, SDEff (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let eargs = snd (List.split args) in
    let mvar, ctx' = fresh_tvars args ctx in
    let dummy_ops = Bindlib.(box_list [] |> bind_mvar mvar |> unbox) in
    let ctx' = { ctx' with effects = (x, { eargs; eops = dummy_ops }) ::
                                     ctx'.effects } in
    let l =
      List.map (fun (x, (a, b)) ->
          { op_name = x; op_in = fst (check_type a ctx')
          ; op_out = fst (check_type b ctx') })
        l |> box_ops in
    prog,
    { ctx with
      effects = (x, { eargs; eops = Bindlib.(bind_mvar mvar l |> unbox)}) ::
                ctx.effects }
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let targs = snd (List.split args) in
    let ctx' = { ctx with data = (x, { targs; cons = [] }) :: ctx.data } in
    let mvar, ctx' = fresh_tvars args ctx' in
    let cons = List.map
        (fun (c, l) ->
           let l = List.map (fun a -> box_type (fst (check_type a ctx'))) l
                |> Bindlib.box_list in
           c, Bindlib.(bind_mvar mvar l |> unbox)) l in
    (* NEW *)
    let _, ctx = M.List.iter
        (fun (c, l) ->
           let v, types = Bindlib.unmbind l in
           let a = List.fold_right (fun a b -> TArr (a, b)) types
               (TCon (x, Array.map (fun v -> TVar v) v)) in
           let a = TMod (MAbs ([], None), a) in
           let v = Array.to_list v in
           let* _ = fresh_var c @@
             List.fold_right2
               (fun v (_, k) a ->
                  (TForA (k, Bindlib.(bind_var v (box_type a) |> unbox))))
               v args a in
           return ()
        ) cons ctx in
    (* END NEW *)
    prog, { ctx with data = (x, { targs; cons }) :: ctx.data }

let _, init_ctx =
  let int = TCon ("int", [||]) in
  let bool = TCon ("bool", [||]) in
  let string = TCon ("string", [||]) in
  let unit = TCon ("unit", [||]) in
  let (@->) t t' = TArr (t, t') in
  let v = Bindlib.new_var (fun v -> TVar v) "fail" in
  let abs t = TMod (MAbs ([], None), t) in
  fresh_vars
    [("+", abs (int @-> int @-> int));
     ("*", abs (int @-> int @-> int));
     ("-", abs (int @-> int @-> int));
     ("=", abs (int @-> int @-> bool));
     ("string_eq", abs (string @-> string @-> bool));
     ("string_of_int", abs (int @-> string));
     ("^", abs (string @-> string @-> string));
     ("&&", abs (bool @-> bool @-> bool));
     ("fail", abs (TForA (Any, Bindlib.(unit @-> (TVar v) |> box_type |> bind_var v |> unbox))));
     ("print", abs (string @-> unit))]
    { gamma = [] ; tid = [] ; id = [] ; effects = []
    ; data = ["int", { targs = [] ; cons = [] };
              "string", { targs = [] ; cons = [] } ] }

let check_prog ctx =
  List.fold_left check_decl ([], ctx)

