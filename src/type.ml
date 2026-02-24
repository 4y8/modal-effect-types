open Syntax
open Context

let unknown_var loc x = Error.error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = Error.error_str loc ("Unknown effect " ^ x)

let type_mismatch loc _ _ = Error.error_str loc "Type mismatch todo"

let expected_arr loc _ = Error.error_str loc "Expected function type todo"

let mod_mismatch loc _ _ _ = Error.error_str loc "Modality mismatch todo"

let kind_mismatch loc _ _ _ = Error.error_str loc "Kind mismatch todo"

let no_unboxing loc _ _ =
  Error.error_str loc "Cannot unbox function in application"

let eff_arg_mismatch loc e a b = Error.error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e (List.length a) (List.length b))

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SAnn (m, _) 
  | STApp (m, _) -> is_val m.sexpr
  | _ -> false

let is_mod = function
  | TMod (_, _) -> true
  | _ -> false

let rec check_type ?(s=[]) ctx t = match t.stype with
  | STUnit -> TUnit
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
        List.map (fun { eff_type; eff_name } ->
            { eff_name
            ; eff_type = Pair.map (Subst.pure_type s) (Subst.pure_type s)
                  eff_type
            }) t
    ) l |> List.flatten
      
and check_mask ctx = function
  | [] -> []
  | (e, loc) :: tl->
    if List.mem_assoc e ctx.effects then 
      e :: check_mask ctx tl
    else
      unknown_eff loc e

let split_arrow loc = function
  | TArr (a, b) -> a, b
  | a -> expected_arr loc a

let rec check ctx ({loc; sexpr} as m) a e = match sexpr with
  (* B-Mod *)
  | v when is_val v && is_mod a ->
    begin match a with
      | TMod (mu, a) ->
        check (add_binding ctx (Lock (mu, e))) m a (Effect.apply_mod mu e)
      | _ -> failwith "impossible"
    end
  (* B-Abs *)
  | SLam (x, m) ->
    let (a, b) = split_arrow loc a in
    check (add_binding ctx (BVar (x, a))) m b e
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
        across a nu f
    end
  (* B-Annotation *)
  | SAnn (m, a) ->
    let a = check_type ctx a in
    check ctx m a e;
    a
  (* B-App *)
  | SApp (m, n) ->
    let mu, g = get_guarded (infer ctx m e) in
    let a, b = split_arrow loc g in
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
  | SHand (m, d, (l, (x, n))) ->
    let d = check_effect_ctx ctx d in
    let a = infer (add_binding ctx (Lock (MRel ([], d), e))) m (d @ e) in
    
  | _ -> failwith "todo"
