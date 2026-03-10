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

let nb_arg_mismatch loc e n l = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e n (List.length l))

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SAnn (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let rec check_type t = match t.stype with
  | STMod (mu, a) ->
    let* mu = check_mod mu in
    let* a = check_type a in
    return @@ TMod (mu, a)
  | STArr (a, b) ->
    let* a = check_type a in
    let* b = check_type b in
    return @@ TArr (a, b)
  | STForA (x, k, a) ->
    protect_context @@
    let* v = fresh_tvar x k in
    let* a = check_type a in
    return @@ TForA (k, Bindlib.(unbox (bind_var v (box_type a))))
  | STCons (c, l) ->
    let* ty = lookup_data c in
    begin match ty with
      | None -> unknown_var t.tloc c
      | Some (n, _) ->
        if n <> List.length l then
          nb_arg_mismatch t.tloc c n l;
        let* l = M.List.map check_type l in
        return @@ TCon (c, Array.of_list l)
    end
  | STVar x ->
    let* tid = lookup_tid x in
    match tid with
    | Some v -> return @@ TVar v
    | None ->
      let* ty = lookup_data x in
      match ty with
      | None -> unknown_var t.tloc x
      | Some _ -> return @@ TCon (x, [||])

and check_mod m = match m.smod with
  | SMAbs e ->
    let* e = check_effect_ctx e in
    return @@ MAbs e
  | SMRel (l, d) ->
    let* d = check_effect_ctx d in
    let* l = check_mask l in
    return @@ MRel (l, d)

and check_effect_ctx l =
  let* e =
    M.List.map (fun {seff_name; seff_args; eloc} ->
        let* eff = lookup_eff seff_name in
        match eff with
        | None -> unknown_eff eloc seff_name
        | Some (n, t) ->
          if n <> List.length seff_args then
            nb_arg_mismatch eloc seff_name n seff_args;
          let* args = M.List.map check_type seff_args in
          let ectx = Bindlib.msubst t (Array.of_list args) in
          M.List.iter (fun { eff_type = (a, b); _ } ->
              let* c = is_abs a in
              if not c then kind_mismatch eloc a Abs Any;
              let* c = is_abs b in
              if not c then kind_mismatch eloc b Abs Any;
              return ()) ectx >>
          return ectx
      ) l
  in return (List.flatten e)

and check_mask = function
  | [] -> return []
  | (e, loc) :: tl->
    let* eff = lookup_eff e in
    match eff with
    | None -> unknown_eff loc e
    | Some (_, b) ->
      let _, l = Bindlib.unmbind b in
      let* tl = check_mask tl in
      return @@ (List.map (fun {eff_name; _} -> eff_name) l) @ tl

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

let rec split_pat vars mu t { spat; ploc } =
  let nu, g = get_guarded t in
  let mu = Effects.compose mu nu in
  match spat with
  | SPWild -> return @@ (vars, PWild)
  | SPVar x ->
    let* v = fresh_var x (TMod (mu, g)) in
    return @@ ((v :: vars), PVar (TMod (mu, g)))
  | SPCons (c, l) ->
    let tc, tl = split_cons ploc g in
    let* _, cons = get_data tc in
    let tcons = match List.assoc_opt c cons with
      | None -> not_cons ploc c g
      | Some tcons -> Bindlib.msubst tcons tl
    in
    let* res, l = M.List.fold_right
        (fun (a, p) (vars, l) ->
           let* vars, p = split_pat vars mu a p in
           return (vars, p :: l))
        (List.combine tcons l) (vars, [])
    in return (res, PCon (c, l))

let join_type loc f t t' =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g = g' then
    type_mismatch loc g g';
  let* c = is_abs g in
  if c then
    return g
  else match Effects.join_mod mu nu f with
    | None -> return @@ mod_mismatch loc mu nu g
    | Some lam -> return @@ TMod (lam, g)

let rec check ({loc; sexpr} as m) a e =
  match sexpr with
  (* B-Mod *)
  | v when is_val v && is_mod a ->
    begin match a with
      | TMod (mu, a) ->
        with_binding (Lock (mu, e)) @@
        check m a (Effects.apply_mod mu e)
      | _ -> failwith "impossible"
    end

  (* B-Forall *)
  | v when is_val v && is_forall a ->
    let k, a = split_forall loc a in
    let v, a = Bindlib.unbind a in
    with_binding (BType (v, k)) @@ check m a e

  (* B-Abs *)
  | SLam (x, m) ->
    let (a, b) = split_arr loc a in
    let* v = fresh_var x a in
    let* m = check m b e in
    return @@ Lam (a, Bindlib.(box_expr m |> bind_var v |> unbox))

  (* B-HandlerCheck *)
  | SHand (m, d, (l, (x, n))) ->
    let b = a in (* stay consistent with the paper *)
    let* d = check_effect_ctx d in
    let* m, a = with_binding (Lock (MRel ([], d), e)) @@
       infer m (d @ e)
    in
    let* n =
      protect_context @@
      let* ret = fresh_var x (TMod (MRel ([], d), a)) in
      let* n = check n b e in
      return Bindlib.(box_expr n |> bind_var ret |> unbox) in
    let check_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        protect_context @@
        let* pi = fresh_var pi ai in
        let* ri = fresh_var ri (TArr (bi, b)) in
        let* ni = check ni b e in
        return (li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi
                             |> unbox))
    in
    let* l = M.List.map check_clause l in
    return @@ Hand (m, d, n, l)
  (* B-CrispSumCheck and B-CrispPairCheck *)
  | SMatch (v, l) ->
    let* m, t = infer v e in
    protect_context @@
    let* l =
      M.List.map (fun (p, n) ->
          let* vars, p = split_pat [] Effects.id t p in
          let mvar = Array.of_list vars in
          let* n = check n a e in
          return (p, Bindlib.(box_expr n |> bind_mvar mvar |> unbox))) l
    in
    return (Match (m, l))
  | SSeq (m, n) ->
    let* m = check m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    let* n = check n a e in
    return @@ Let (m, TCon ("unit", [||]),
                   Bindlib.(box_expr n |> bind_var dummy |> unbox))
  | SCons (c, l) ->
    let tc, tl = split_cons loc a in
    let* _, constructors = get_data tc in
    begin
      match List.assoc_opt c constructors with
      | None -> unknown_cons loc c tc
      | Some cargs ->
        let cargs = Bindlib.msubst cargs tl in
        if List.length cargs <> List.length l then
          nb_arg_mismatch loc c (List.length cargs) l;
        let* l = M.List.map2 (fun n b -> check n b e) l cargs in
        return @@ Con (c, l)
  end
  | SLet (x, m, n) ->
    let* m, t = infer m e in
    protect_context @@
    let* v = fresh_var x t in
    let* n = check n a e in
    return @@ Let (m, t, Bindlib.(box_expr n |> bind_var v |> unbox))
  (* B-Switch *)
  | _ ->
    let* m, b = infer m e in
    let mu, g = get_guarded b in
    let nu, g' = get_guarded a in
    if not Effects.(eq_ty g g') then type_mismatch loc g g'
    else
      let* c = is_abs g in
      if not (Effects.sub_mod mu nu e) && not c then
        mod_mismatch loc mu nu g
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
        | None -> fun ctx -> no_access loc x ctx e
        | Some a -> return (Var v, a)
    end
  (* B-Annotation *)
  | SAnn (m, a) ->
    let* a = check_type a in
    let* m = check m a e in
    return (m, a)

  (* B-App *)
  | SApp (m, n) ->
    let* m, a = infer m e in
    let mu, g = get_guarded a in
    let a, b = split_arr loc g in
    if not Effects.(sub_mod mu id e) then
      no_unboxing loc mu e;
    let* n = check n a e in
    return (App (m, n), b)

  (* B-Do *)
  | SDo (l, m) ->
    let (a, b) = match Effects.get_eff l e with
      | None -> unknown_eff loc l
      | Some p -> p
    in
    let* m = check m a e in
    return (Do (l, m), b)

  (* B-HandlerInfer *)
  | SHand (m, d, (l, (x, n))) ->
    let* d = check_effect_ctx d in
    let* m, a = with_binding (Lock (MRel ([], d), e)) @@
      infer m (d @ e) in
    let* n, b' = protect_context @@
      let* ret = fresh_var x (TMod (MRel ([], d), a)) in
      let* n, b' = infer n e in
      return Bindlib.(box_expr n |> bind_var ret |> unbox, b') in
    let infer_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) -> protect_context @@
        let* pi = fresh_var pi ai in
        let* ri = fresh_var ri (TArr (bi, b')) in
        let* ni, bi = infer ni e in
        return ((li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi
                              |> unbox)), bi)
    in
    let* h, bi = M.List.map infer_clause l $> List.split in
    let* b = M.List.fold_left (join_type loc e) b' bi in
    return (Hand (m, d, n, h), b)
  | SInt n -> return (Lit (Int n), TCon ("int", [||]))
  | SStr s -> return (Lit (Str s), TCon ("string", [||]))

  (* B-CrispSumInfer and B-CrispPairInfer *)
  | SMatch (v, l) ->
    if not (is_val v.sexpr) then
      expected_val v.loc v;
    let* m, t = infer v e in
    let* c, types = M.List.map (fun (p, n) ->
        let* vars, p = split_pat [] Effects.id t p in
        let mvar = Array.of_list vars in
        let* n, t = infer n e in
        return ((p, Bindlib.(box_expr n |> bind_mvar mvar |> unbox)), t)) l
      $> List.split in
    let hty, tty = List.hd types, List.tl types in
    let* a = M.List.(fold_left (join_type loc e) (hty) (tty)) in
    return (Match (m, c), a)
  | SSeq (m, n) ->
    let* m = check m (TCon ("unit", [||])) e in
    let dummy = Bindlib.new_var (fun v -> Var v) "unit" in
    let* n, a = infer n e in
    return (Let (m, TCon ("unit", [||]),
                 Bindlib.(n |> box_expr |> bind_var dummy |> unbox)), a)
  | SLet (x, m, n) ->
    let* m, a = infer m e in
    let* n, b, v = protect_context @@
      let* v = fresh_var x a in
      let* n, b = infer n e in
      return (n, b, v) in
    return (Let (m, a, Bindlib.(n |> box_expr |> bind_var v |> unbox)), b)
  | _ ->
    failwith "todo"

let check_decl (prog, ctx) d = match d with
  | (x, SDSig t), _ ->
    let t, ctx = check_type t ctx in
    let _, ctx = fresh_var x t ctx in
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
    let _ = check e g [] ctx' in (x, e) :: prog, ctx
  | (x, SDEff (args, l)), _ ->
    let mvar, ctx' = fresh_tvars (List.map (fun x -> x, Any) args) ctx in
    let l =
      List.map (fun (x, (a, b)) ->
          { eff_name = x; eff_type = fst (check_type a ctx'),
                                     fst (check_type b ctx') })
        l |> box_effect_ctx in
    prog, { ctx with
            effects =
              (x, (Array.length mvar, Bindlib.(bind_mvar mvar l |> unbox))) ::
              ctx.effects }
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let n = List.length args in
    let ctx' = { ctx with data = (x, (n, [])) :: ctx.data } in
    let mvar, ctx' = fresh_tvars (List.map (fun x -> x, Any) args) ctx' in
    let l = List.map
        (fun (c, l) ->
           let l = List.map (fun a -> box_type (fst (check_type a ctx'))) l
                |> Bindlib.box_list in
           c, Bindlib.(bind_mvar mvar l |> unbox)) l in
    prog, { ctx with data = (x, (n, l)) :: ctx.data }

let _, init_ctx =
  let int = TCon ("int", [||]) in
  let bool = TCon ("bool", [||]) in
  let string = TCon ("string", [||]) in
  let unit = TCon ("unit", [||]) in
  let (@->) t t' = TArr (t, t') in
  let v = Bindlib.new_var (fun v -> TVar v) "fail" in
  fresh_vars
    [("+", TMod (MAbs [], int @-> int @-> int));
     ("*", TMod (MAbs [], int @-> int @-> int));
     ("-", TMod (MAbs [], int @-> int @-> int));
     ("=", TMod (MAbs [], int @-> int @-> bool));
     ("string_eq", TMod (MAbs [], string @-> string @-> bool));
     ("^", TMod (MAbs [], string @-> string @-> string));
     ("&&", TMod (MAbs [], bool @-> bool @-> bool));
     ("fail", TMod (MAbs [],
                    TForA (Any, Bindlib.(unit @-> (TVar v) |> box_type |> bind_var v |> unbox))));
     ("print", TMod (MAbs [], string @-> unit))]
    { gamma = [] ; tid = [] ; id = [] ; effects = []
    ; data = ["int", (0, []); "string", (0, [])] }

let check_prog =
  Fun.compose fst (List.fold_left check_decl ([], init_ctx))
