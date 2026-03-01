open Syntax

let rec pure_type s = function
  | TMod (m, t) -> TMod (pure_mod s m, pure_type s t)
  | TArr (t, t') -> TArr (pure_type s t, pure_type s t')
  | TForA (x, k, t) -> TForA (x, k, pure_type (List.remove_assoc x s) t)
  | TCons (c, l) -> TCons (c, List.map (pure_type s) l)
  | TVar (x, _) as t ->
    match List.assoc_opt x s with
    | None -> t
    | Some t -> t
and pure_mod s = function
  | MAbs e -> MAbs (List.map (pure_effect s) e)
  | MRel (l, d) -> MRel (l, (List.map (pure_effect s) d))
and pure_effect s { eff_name ; eff_type } =
  { eff_name; eff_type = Pair.map (pure_type s) (pure_type s) eff_type }
