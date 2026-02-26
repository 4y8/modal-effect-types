open Syntax

type ctx_binding
  = Lock of concrete_mod
  | BVar of string * pure_type
  | BType of string * kind

type ctx = { gamma : ctx_binding list
           ; effects : (string * (string list * effect_ctx)) list
           ; data : (string * (string list * (string * pure_type list) list)) list }

let rec get_kind gamma x = match gamma with
  | [] -> None
  | BType (y, k) :: _ when x = y -> Some k
  | _ :: tl -> get_kind tl x

(* Section 4.4 *)
let rec is_abs = function
  | TMod (MAbs _, _) -> true
  | TMod (MRel _, a) -> is_abs a
  | TProd (a, b) -> is_abs a && is_abs b
  | TArr (_, _) -> false
  | TVar (_, k) -> k = Abs
  | TForA (_, _, t) -> is_abs t
  | TCons (_, l) -> List.for_all is_abs l

let rec get_guarded = function
  | TMod (mu, t) -> let nu, g = get_guarded t in
    Effect.compose mu nu, g
  | g -> Effect.id, g

let across a nu f =
  if is_abs a then Some a
  else
    let mu, g = get_guarded a in
    match Effect.right_residual nu mu f with
    | Some xi -> Some (TMod (xi, g))
    | _ -> None

let rec locks e = function
  | [] -> Effect.id, e
  | Lock (m, e) :: tl ->
    let (m', f) = locks e tl in
    Effect.compose m' m, f
  | _ :: tl -> locks e tl

let rec get_type_context gamma x = match gamma with
  | [] -> None
  | BVar (y, a) :: _ when x = y -> Some (a, [])
  | hd :: tl ->
    Option.map (fun (a, gamma) -> a, hd :: gamma)
      (get_type_context tl x)

let (<:) ({gamma; _} as ctx) b =
  {ctx with gamma = b :: gamma}
