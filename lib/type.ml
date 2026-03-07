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
  | SAnn (m, _)
  | SAppT (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let rec check_type ctx t = match t.stype with
  | STMod (m, t) -> TMod (check_mod ctx m, check_type ctx t)
  | STArr (t, t') -> TArr (check_type ctx t, check_type ctx t')
  | STForA (x, k, a) ->
    let ctx, v = fresh_tvar ctx x k in
    let a = check_type ctx a in
    TForA (k, Bindlib.unbox (Bindlib.bind_var v (box_type a)))
  | STCons (c, l) ->
    begin match List.assoc_opt c ctx.data with
      | None -> unknown_var t.tloc c
      | Some (n, _) ->
        if n <> List.length l then
          nb_arg_mismatch t.tloc c n l;
        TCon (c, Array.of_list @@ List.map (check_type ctx) l)
    end
  | STVar x ->
    match List.assoc_opt x ctx.tid with
    | Some v ->
      TVar v
    | None ->
      match List.assoc_opt x ctx.data with
      | None -> unknown_var t.tloc x
      | Some _ -> TCon (x, [||])

and check_mod ctx m = match m.smod with
  | SMAbs e -> MAbs (check_effect_ctx ctx e)
  | SMRel (l, d) ->
    MRel (check_mask ctx l, check_effect_ctx ctx d)

and check_effect_ctx ctx l =
  List.map (fun {seff_name; seff_args; eloc} ->
      match List.assoc_opt seff_name ctx.effects with
      | None -> unknown_eff eloc seff_name
      | Some (n, t) ->
        if n <> List.length seff_args then
          nb_arg_mismatch eloc seff_name n seff_args;
        let args = List.map (check_type ctx) seff_args
                |> Array.of_list in
        let ectx = Bindlib.msubst t args in
        List.iter (fun { eff_type = (a, b); _ } ->
            if not (is_abs ctx a) then kind_mismatch eloc a Abs Any;
            if not (is_abs ctx b) then kind_mismatch eloc b Abs Any) ectx;
        ectx
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
    let _, cons = List.assoc tc ctx.data in
    let tcons = match List.assoc_opt c cons with
      | None -> not_cons ploc c g
      | Some tcons -> Bindlib.msubst tcons tl
    in
    let res, l = List.fold_right
        (fun (a, p) ((ctx, vars), l) ->
           Pair.map_snd (fun x -> x :: l) @@ split_pat ctx vars mu a p)
        (List.combine tcons l) ((ctx, vars), [])
    in res, PCon (c, l)

let join_type loc ctx f t t' =
  let mu, g = get_guarded t in
  let nu, g' = get_guarded t' in
  if g = g' then
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
    let d = check_effect_ctx ctx d in
    let m, a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    let ctx', ret = fresh_var ctx x (TMod (MRel ([], d), a)) in
    let n = Bindlib.(check ctx' n b e |> box_expr |> bind_var ret |> unbox) in
    let check_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx, pi = fresh_var ctx pi ai in
        let ctx, ri = fresh_var ctx ri (TArr (bi, b)) in
        li, Bindlib.(check ctx ni b e |> box_expr |> bind_var ri |> bind_var pi
                  |> unbox)
    in
    Hand (m, d, n,  List.map check_clause l)
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
    let _, constructors = List.assoc tc ctx.data in
    begin
      match List.assoc_opt c constructors with
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
    if k = Abs && not (is_abs ctx a) then
      kind_mismatch tloc a Abs Any;
    m, Bindlib.subst b a

  (* B-Do *)
  | SDo (l, m) ->
    let (a, b) = match Effects.get_eff l e with
      | None -> unknown_eff loc l
      | Some p -> p
    in
    let m = check ctx m a e in
    Do (l, m), b

  (* B-HandlerInfer *)
  | SHand (m, d, (l, (x, n))) ->
    let d = check_effect_ctx ctx d in
    let m, a = infer (ctx <: Lock (MRel ([], d), e)) m (d @ e) in
    let ctx', ret = fresh_var ctx x (TMod (MRel ([], d), a)) in
    let n, b' = infer ctx' n e in
    let n = Bindlib.(box_expr n |> bind_var ret |> unbox ) in
    let infer_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_eff li d with
      | None -> unknown_eff loc li
      | Some (ai, bi) ->
        let ctx, pi = fresh_var ctx pi ai in
        let ctx, ri = fresh_var ctx ri (TArr (bi, b')) in
        let ni, bi = infer ctx ni e in
        (li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi |> unbox)), bi
    in
    let h, bi = List.map infer_clause l |> List.split in
    let b = List.fold_left (join_type loc ctx e) b' bi in
    Hand (m, d, n, h), b
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
    let _ = check ctx' e g [] in ctx, (x, e) :: prog
  | (x, SDEff (args, l)), _ ->
    let ctx', mvar = fresh_tvars ctx (List.map (fun x -> x, Any) args) in
    let l =
      List.map (fun (x, (a, b)) ->
        { eff_name = x; eff_type = check_type ctx' a, check_type ctx' b })
        l |> box_effect_ctx in
    { ctx with
      effects = (x, (Array.length mvar, Bindlib.(bind_mvar mvar l |> unbox)))
                :: ctx.effects }, prog
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let n = List.length args in
    let ctx' = { ctx with data = (x, (n, [])) :: ctx.data } in
    let ctx', mvar = fresh_tvars ctx' (List.map (fun x -> x, Any) args) in
    let l = List.map
        (fun (c, l) ->
           let l = List.map (Fun.compose box_type (check_type ctx')) l
                |> Bindlib.box_list in
           c, Bindlib.(bind_mvar mvar l |> unbox)) l in
    { ctx with data = (x, (n, l)) :: ctx.data }, prog

let check_prog =
  let int = TCon ("int", [||]) in
  let bool = TCon ("bool", [||]) in
  let string = TCon ("string", [||]) in
  let unit = TCon ("unit", [||]) in
  let (@->) t t' = TArr (t, t') in
  let v = Bindlib.new_var (fun v -> TVar v) "fail" in
  let init_ctx, _ =
    fresh_vars
      { gamma = [] ; tid = [] ; id = [] ; effects = []
      ; data = ["int", (0, []); "string", (0, [])] }
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
  in
  Fun.compose snd (List.fold_left check_decl (init_ctx, []))
