open Syntax

type ctx_binding
  = Lock : concrete_mod -> ctx_binding
  | BVar : 'a Bindlib.var * pure_type -> ctx_binding
  | BType : tvar * kind -> ctx_binding
  | BFlex : tvar * kind * pure_type option -> ctx_binding
  | Marker : tvar -> ctx_binding

type ctx =
  { gamma : ctx_binding list
  ; effects : (string * (int * (pure_type, effect_ctx) Bindlib.mbinder)) list
  ; data : (string * (int * (string * (pure_type, pure_type list) Bindlib.mbinder) list)) list
  ; id : (string * var) list
  ; tid : (string * tvar) list }

let (<:) ({gamma; _} as ctx) b =
  {ctx with gamma = b :: gamma}

let rec drop_marker v = function
  | [] -> failwith "drop_marker: internal error"
  | Marker v' :: tl when Bindlib.eq_vars v v' -> tl
  | _ :: tl -> drop_marker v tl

let rec drop_type v = function
  | [] -> failwith "drop_type: internal error"
  | BType (v', _) :: tl when Bindlib.eq_vars v v' -> tl
  | _ :: tl -> drop_type v tl

let bind f g = fun ctx ->
  let a, ctx = f ctx in
  g a ctx

let (let*) = bind

let (>>) f g =
  let* () = f in
  g

let return x = fun ctx -> x, ctx

let ($>) x f =
  let* x = x in
  return (f x)

module M = struct
  module List = struct
    let rec map f = function
      | [] -> return []
      | hd :: tl ->
        let* x = f hd in
        let* xs = map f tl in
        return (x :: xs)


    let rec map2 f l l' = match l, l' with
      | [], [] -> return []
      | hd :: tl, hd' :: tl' ->
        let* x = f hd hd' in
        let* xs = map2 f tl tl' in
        return (x :: xs)
      | _, _ -> failwith "internal error: map2"

    let rec iter f = function
      | [] -> return ()
      | hd :: tl -> f hd >> iter f tl

    let rec fold_right f l acc = match l with
      | [] -> return acc
      | hd :: tl -> let* tl = fold_right f tl acc in
        f hd tl

    let rec fold_left f acc l = match l with
      | [] -> return acc
      | hd :: tl ->
        let* acc = f acc hd in
        fold_left f acc tl
  end

  module Array = struct
    let for_all f a =
      let n = Array.length a in
      let rec aux i =
        if i = n then return true
        else
          let* c =  f a.(i) in
          if c then aux (i + 1)
          else return false
      in aux 0
  end
end

let add_binding b = fun ctx ->
  (), ctx <: b

let fresh_marker () =
  let x = Bindlib.new_var (fun v -> TFlex v) "" in
   x

let protect_context f = fun ctx ->
  let x = fresh_marker () in
  let ctx = ctx <: Marker x in
  let a, ctx = f ctx in
  a, { ctx with gamma = drop_marker x ctx.gamma }

let with_binding b f =
  protect_context @@ (add_binding b >> f)

let get_kind x ({gamma; _} as ctx) =
  let rec get_kind gamma x = match gamma with
    | [] -> failwith "get_kind: internal error"
    | BFlex (y, k, _) :: _
    | BType (y, k) :: _ when Bindlib.eq_vars x y -> k
    | _ :: tl -> get_kind tl x
  in
  get_kind gamma x, ctx

(* Section 4.4 *)
let rec is_abs = function
  | TMod (MAbs _, _) -> return true
  | TMod (MRel _, a) -> is_abs a
  | TArr (_, _) -> return false
  | TFlex v
  | TVar v ->
    let* k = get_kind v in
    return (k = Abs)
  | TForA (k, a) ->
    let v, a = Bindlib.unbind a in
    protect_context @@
    add_binding (BType (v, k)) >>
    is_abs a
  | TCon (_, l) -> M.Array.for_all is_abs l

let rec get_guarded = function
  | TMod (mu, t) -> let nu, g = get_guarded t in
    Effects.compose mu nu, g
  | g -> Effects.id, g

let across a nu f =
  let* c = is_abs a in
  if c then return (Some a)
  else
    let mu, g = get_guarded a in
    match Effects.right_residual nu mu f with
    | Some xi -> return @@ Some (TMod (xi, g))
    | _ -> return None

let rec locks e = function
  | [] -> Effects.id, e
  | Lock (m, e) :: tl ->
    let (m', f) = locks e tl in
    Effects.compose m' m, f
  | _ :: tl -> locks e tl


let get_type_context x ({gamma; _} as ctx) =
  let rec get_type_context gamma x = match gamma with
    | [] -> failwith "get_type_context: internal error"
    | BVar (y, a) :: gamma when Bindlib.eq_vars x y -> gamma, a, []
    | hd :: tl ->
      let gamma, a, gamma' = get_type_context tl x in
      gamma, a, hd :: gamma'
  in get_type_context gamma x, ctx

let fresh_tvar x k ({gamma; tid; _} as ctx) =
  let v = Bindlib.new_var (fun v -> TVar v) x in
  v, { ctx with gamma = BType (v, k) :: gamma; tid = (x, v) :: tid }

let fresh_tvars args ctx =
  let vars, ctx =
    List.fold_right (fun (x, k) (vars, ctx) ->
        Pair.map_fst (fun v -> v :: vars) @@ fresh_tvar x k ctx)
      args ([], ctx) in
  let mvar = Array.of_list vars in
  mvar, ctx

let fresh_flex x k ({gamma; tid; _} as ctx) =
  let v = Bindlib.new_var (fun v -> TFlex v) x in
  v, { ctx with gamma = BFlex (v, k, None) :: gamma; tid = (x, v) :: tid }

let fresh_flexs args ctx =
  let vars, ctx =
    List.fold_right (fun (x, k) (vars, ctx) ->
        Pair.map_fst (fun v -> v :: vars) @@ fresh_flex x k ctx)
      args ([], ctx) in
  let mvar = Array.of_list vars in
  mvar, ctx

let fresh_var x a ({gamma; id; _} as ctx) =
  let v = Bindlib.new_var (fun v -> Var v) x in
  v, { ctx with gamma = BVar (v, a) :: gamma; id = (x, v) :: id }

let fresh_vars args ctx =
  let vars, ctx =
    List.fold_right (fun (x, t) (vars, ctx) ->
        Pair.map_fst (fun v -> v :: vars) @@ fresh_var x t ctx)
      args ([], ctx) in
  let mvar = Array.of_list vars in
  mvar, ctx

let subst_single a v b =
  Bindlib.(subst (bind_var v (box_type a) |> unbox) b)

let rec dummy_subst a v = function
  | [] -> failwith "dummy_marker: internal error"
  | Marker v' :: _ when Bindlib.eq_vars v v' -> a
  | BFlex (v', _, None) :: tl ->
    dummy_subst (subst_single a v' @@ TCon ("unit", [||])) v tl
  | BFlex (v', _, Some b) :: tl ->
    dummy_subst (subst_single a v' b) v tl
  | _ :: tl -> dummy_subst a v tl

let apply gamma a =
  List.fold_left
    (fun a b -> match b with
       | BFlex (v, _, Some b) -> subst_single a v b
       | _ -> a) a gamma

let rec def_flex alpha a = function
  | [] -> failwith "internal error: def_flex"
  | BFlex (beta, k, def) :: tl when Bindlib.eq_vars alpha beta ->
    if def = None then
      BFlex (alpha, k, Some a) :: tl
    else
      failwith "internal error: redefining flex"
  | hd :: tl -> hd :: def_flex alpha a tl

let rec split_flex alpha = function
  | [] -> failwith "internal error: split_flex"
  | BFlex (beta, k, _) :: gamma' when Bindlib.eq_vars beta alpha ->
    [], k, gamma'
  | hd :: tl ->
    let gamma, k, gamma' = split_flex alpha tl in
    hd :: gamma, k, gamma'

let rec (<<) alpha alpha' = function
  | [] -> failwith "internal error: split_flex"
  | BFlex (beta, _, _) :: _ when Bindlib.eq_vars alpha beta -> true
  | BFlex (beta, _, _) :: _ when Bindlib.eq_vars alpha' beta -> false
  | _ :: tl -> (alpha << alpha') tl

let lookup_data c ctx =
  List.assoc_opt c ctx.data, ctx

let lookup_con c ctx =
  List.find_map (fun (tc, (n, l)) ->
      List.find_map (fun (c', b) ->
      let v, a = Bindlib.unmbind b in
      if c' = c then
        Some (tc, n, Bindlib.(bind_mvar v (box_list (List.map box_type a))
                              |> unbox))
      else None) l
    ) ctx.data, ctx

let get_data c ctx =
  List.assoc c ctx.data, ctx

let lookup_tid x ctx =
  List.assoc_opt x ctx.tid, ctx

let lookup_id x ctx =
  List.assoc_opt x ctx.id, ctx

let lookup_eff e ctx =
  List.assoc_opt e ctx.effects, ctx
