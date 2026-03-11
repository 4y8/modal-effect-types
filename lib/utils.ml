open Errors
open Syntax

let rec is_val = function
  | SVar _ -> true
  | SLam (_, _) -> true
  | SAnn (m, _) -> is_val m.sexpr
  | SCons (_, l) -> List.for_all (fun {sexpr; _} -> is_val sexpr) l
  | _ -> false

let is_mod = function TMod _ -> true | _ -> false

let is_forall = function TForA _ -> true | _ -> false

let is_con = function TCon _ -> true | _ -> false

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
