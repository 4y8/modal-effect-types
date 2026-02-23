open Syntax

exception KindError of string * loc
exception UnknownTypeVar of string * loc

type ctx_binding
  = Lock of concrete_mod
  | BVar of string * pure_type
  | BType of string * kind

(* Section 4.4 *)
let rec is_abs ctx = function
  | TUnit -> true
  | TMod (MAbs _, _) ->
    true
  | TMod (MRel _, a) ->
    is_abs ctx a
  | TProd (a, b) ->
    is_abs ctx a &&
    is_abs ctx b
  | TSum (a, b) ->
    is_abs ctx a &&
    is_abs ctx b
  | TArr (_, _) -> false
  | TVar v ->
    match List.find_map
            (function | BType (v', k) when v' = v -> Some k
                      | _ -> None) ctx with
    | None -> failwith "internal error"
    | Some k -> k = Abs

let rec get_guarded = function
  | TMod (mu, t) -> let nu, g = get_guarded t in
    Effect.compose mu nu, g
  | g -> Effect.id, g

let across ctx a nu f =
  if is_abs ctx a then a
  else
    let mu, g = get_guarded a in
    match Effect.right_residual nu mu f with
    | Some xi -> TMod (xi, g)
    | _ -> failwith "internal error"

let rec locks e = function
  | [] -> Effect.id, e
  | Lock (m, e) :: tl ->
    let (m', f) = locks e tl in
    Effect.compose m' m, f
  | _ :: tl -> locks e tl

let rec get_type_context ctx x = match ctx with
  | [] -> None
  | BVar (y, a) :: _ when x = y -> Some (a, [])
  | hd :: tl ->
    Option.bind (get_type_context tl x)
      (fun (a, ctx) -> Some (a, hd :: ctx))
