open Syntax

let erase_types = List.map (fun {eff_name; _} -> eff_name)

let rec get_first f = function
  | [] -> None
  | hd :: tl when f hd -> Some (hd, tl)
  | hd :: tl ->
    Option.map (fun (x, l) -> x, hd :: l) (get_first f tl) 

let find_label_mask lab mask =
  Option.map snd (get_first ((=) lab) mask)

let find_label_eff lab =
  get_first (fun {eff_name; _} -> eff_name = lab)

let rec remove_labels_ext d l = match d with
  | [] -> []
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> hd :: remove_labels_ext tl l
    | Some l -> remove_labels_ext tl l

let remove_labels (d, eps) l =
  remove_labels_ext d l,
  match eps with
  | None -> None
  | Some (eps, l') -> Some (eps, l @ l')

let rec mask_diff l l' = match l with
  | [] -> []
  | hd :: tl -> match find_label_mask hd l' with
    | None -> hd :: mask_diff tl l'
    | Some l' -> mask_diff tl l'

let extend d' (d, eps) =
  (d' @ d, eps)

(* Section 4.2 *)
let rec (><) l = function
  | [] -> (l, [])
  | hd :: d ->
    match find_label_mask hd.eff_name l with
    | None -> let l', d' = l >< d in (l', hd :: d')
    | Some l' -> l' >< d

(* Section 4.3 *)
let apply_mod m f = match m with
  | MAbs e -> e
  | MRel (l, d) -> extend d (remove_labels f l)

let compose m m' = match m, m' with
  | _, MAbs e -> MAbs e
  | MAbs e, MRel (l, d) -> MAbs (extend d (remove_labels e l))
  | MRel (l1, d1), MRel (l2, d2) ->
    let l, d = l2 >< d1 in
    MRel (l1 @ l, d2 @ d)

let id = MRel ([], [])

let rec extract d l = match d with
  | [] -> if l = [] then Some [] else None
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> extract tl l
    | Some l -> Option.map (fun e -> hd :: e) (extract tl l)

(* Appendix D.1 *)
let right_residual m m' f = match m, m' with
  | _, MAbs _ -> Some m'
  | MAbs _, _ -> None
  | MRel (l', d'), MRel (l, d) ->
    match extract (fst f) (mask_diff l' l) with
    | None -> None
    | Some f ->
      Some (MRel (erase_types d' @ (mask_diff l l'), d @ f))

let eq_eff_var (eps, l) (eps', l') =
  match eps, eps' with
  | TVar v, TVar v' ->
    Bindlib.eq_vars v v' && List.sort compare l = List.sort compare l'
  | _ -> failwith "impossible"

let rec sub_eff d d' =
  match d with
  | [] -> true
  | {eff_type = a, b; eff_name} :: tl ->
    match find_label_eff eff_name d' with
    | None -> false
    | Some ({eff_type = a', b'; _}, d') ->
      eq_ty a a' && eq_ty b b' && sub_eff tl d'

and eq_ty a b = a == b ||
  match a, b with
  | TVar v, TVar v' -> Bindlib.eq_vars v v'
  | TCon (c, l), TCon (c', l') -> c = c' && Array.for_all2 eq_ty l l'
  | TArr (a, b), TArr (a', b') -> eq_ty a a' && eq_ty b b'
  | TMod (m, a), TMod (m', a') -> eq_mod m m' && eq_ty a a'
  | TForA (k, b), TForA (k', b') -> k = k' && Bindlib.eq_binder eq_ty b b'
  | _, _ -> false

and eq_mod m m' =
  match m, m' with
  | MAbs (e, None), MAbs (e', None) -> e === e'
  | MAbs (e, Some eps), MAbs (e', Some eps') ->
    eq_eff_var eps eps' && e === e'
  | MRel (l, d), MRel (l', d') ->
    List.sort compare l = List.sort compare l' && d === d'
  | _, _ -> false

and (===) d d' = sub_eff d d' && sub_eff d' d

let sub_eff_ctx (d, eps) (d', eps') =
  sub_eff d d' &&
  match eps, eps' with
  | None, _ -> true
  | Some eps, Some eps' -> eq_eff_var eps eps'
  | _, _ -> false

(* from wenhao's implementation : mu => nu @ f *)
let sub_mod mu nu f = match mu, nu with
  | MAbs e, _ ->
    sub_eff_ctx e (apply_mod nu f)
  | MRel (l1, d1), MRel (l2, d2) ->
    let l, d = l1 >< d1 in
    let l', d' = l2 >< d2 in
    List.sort compare l = List.sort compare l' && d === d' &&
    extract (fst f) l1 <> None && extract (fst f) l2 <> None
  | _, _ -> false

let rec get_eff l = function
  | [] -> None
  | {eff_name; eff_type} :: _ when eff_name = l -> Some eff_type
  | _ :: tl -> get_eff l tl

let get_eff_ctx l (d, _) = get_eff l d

let rec join_eff_ext d d' = match d with
  | [] -> Some d'
  | {eff_name; eff_type} as hd :: d ->
    match find_label_eff eff_name d' with
    | None -> Option.map (fun e -> hd :: e) (join_eff_ext d d')
    | Some ({eff_type = t; _}, d') when t = eff_type ->
      Option.map (fun e -> hd :: e) (join_eff_ext d d')
    | _ -> None

let join_eff_ctx (d, eps) (d', eps') =
  match join_eff_ext d d' with
  | None -> None
  | Some d ->
    match eps, eps' with
    | None, eps
    | eps, None -> Some (d, eps)
    | Some eps, Some eps' when eq_eff_var eps eps' -> Some (d, Some eps)
    | _, _ -> None

let rec meet_eff e e' = match e with
  | [] -> Some []
  | {eff_name; eff_type} as hd :: e ->
    match find_label_eff eff_name e' with
    | None -> meet_eff e e'
    | Some ({eff_type = t; _}, e') when t = eff_type ->
      Option.map (fun e -> hd :: e) (meet_eff e e')
    | _ -> None

let meet_mask l l' =
  let l = List.sort compare l in
  let l' = List.sort compare l' in
  let rec aux l l' =
    match l, l' with
    | [], _ | _, [] -> []
    | hd :: tl, hd' :: tl' ->
      if hd = hd' then hd :: aux tl tl'
      else if hd < hd' then aux tl l'
      else aux l tl'
  in aux l l'

let join_mod m m' f = match m, m' with
  | MAbs e, MAbs e' -> Option.map (fun e -> MAbs e) (join_eff_ctx e e')
  | MAbs e, MRel (l, d) | MRel (l, d), MAbs e ->
    if sub_eff_ctx e (extend d (remove_labels f l))
    then Some (MRel (l, d))
    else None
  | MRel (l, d), MRel (l', d') ->
    match meet_eff d d' with
    | None -> None
    | Some d'' ->
      let mu = MRel (meet_mask l l', d'') in
      if sub_mod m mu f && sub_mod m' mu f then
        Some mu
      else None

let subst b e =
  let a = Bindlib.subst b (TMod (MAbs e, TCon ("", [||]))) in
  let rec ty = function
    | TVar a -> TVar a
    | TCon (s, a) -> TCon (s, Array.map ty a)
    | TForA (k, b) ->
      let v, a = Bindlib.unbind b in
      Bindlib.(bind_var v (box_type (ty a)) |> tfora_ k |> unbox)
    | TArr (a, b) -> TArr (ty a, ty b)
    | TMod (MRel (l, d), a) -> TMod (MRel (l, eff_ext d), ty a)
    | TMod (MAbs eps, a) -> TMod (MAbs (eff_ctx eps), ty a)
    | ECtx eps -> ECtx (eff_ctx eps)
  and eff_ext d =
    List.map (fun ({ eff_type = (a, b); _ } as e) ->
        { e with eff_type = (ty a, ty b) }) d

  and eff_ctx (d, eps) = match eps with
    | Some (ECtx e, l) -> extend (eff_ext d) (remove_labels e l)
    | eps -> eff_ext d, eps
  in
  ty a
