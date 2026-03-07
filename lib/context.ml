open Syntax

type 'a ctx_binding
  = Lock of concrete_mod
  | BVar of 'a Bindlib.var * pure_type
  | BType of tvar * kind

type 'a ctx =
  { gamma : 'a ctx_binding list
  ; effects : (string * (int * (pure_type, effect_ctx) Bindlib.mbinder)) list
  ; data : (string * (int * (string * (pure_type, pure_type list) Bindlib.mbinder) list)) list
  ; id : (string * var) list
  ; tid : (string * tvar) list }

let (<:) ({gamma; _} as ctx) b =
  {ctx with gamma = b :: gamma}

let rec get_kind gamma x = match gamma with
  | [] -> failwith "get_kind: internal error"
  | BType (y, k) :: _ when Bindlib.eq_vars x y -> k
  | _ :: tl -> get_kind tl x

(* Section 4.4 *)
let rec is_abs ctx = function
  | TMod (MAbs _, _) -> true
  | TMod (MRel _, a) -> is_abs ctx a
  | TArr (_, _) -> false
  | TVar v -> get_kind ctx.gamma v = Abs
  | TForA (k, a) ->
    let v, a = Bindlib.unbind a in is_abs (ctx <: BType (v, k)) a
  | TCon (_, l) -> Array.for_all (is_abs ctx) l

let rec get_guarded = function
  | TMod (mu, t) -> let nu, g = get_guarded t in
    Effects.compose mu nu, g
  | g -> Effects.id, g

let across ctx a nu f =
  if is_abs ctx a then Some a
  else
    let mu, g = get_guarded a in
    match Effects.right_residual nu mu f with
    | Some xi -> Some (TMod (xi, g))
    | _ -> None

let rec locks e = function
  | [] -> Effects.id, e
  | Lock (m, e) :: tl ->
    let (m', f) = locks e tl in
    Effects.compose m' m, f
  | _ :: tl -> locks e tl

let rec get_type_context gamma x = match gamma with
  | [] -> failwith "get_type_context: internal error"
  | BVar (y, a) :: gamma when Bindlib.eq_vars x y -> gamma, a, []
  | hd :: tl ->
    let gamma, a, gamma' = get_type_context tl x in
    gamma, a, hd :: gamma'

let fresh_tvar ({gamma; tid; _} as ctx) x k =
  let v = Bindlib.new_var (fun v -> TVar v) x in
  { ctx with gamma = BType (v, k) :: gamma; tid = (x, v) :: tid }, v

let fresh_tvars ctx args =
    let ctx, vars =
      List.fold_right (fun (x, k) (ctx, vars) ->
          Pair.map_snd (fun v -> v :: vars) @@ fresh_tvar ctx x k)
        args (ctx, []) in
    let mvar = Array.of_list vars in
    ctx, mvar

let fresh_var ({gamma; id; _} as ctx) x a =
  let v = Bindlib.new_var (fun v -> Var v) x in
  { ctx with gamma = BVar (v, a) :: gamma; id = (x, v) :: id }, v

let fresh_vars ctx args =
    let ctx, vars =
      List.fold_right (fun (x, t) (ctx, vars) ->
          Pair.map_snd (fun v -> v :: vars) @@ fresh_var ctx x t)
        args (ctx, []) in
    let mvar = Array.of_list vars in
    ctx, mvar
