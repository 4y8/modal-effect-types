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

let rec remove_labels e l = match e with
  | [] -> []
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> hd :: remove_labels tl l
    | Some l -> remove_labels tl l

let rec mask_diff l l' = match l with
  | [] -> []
  | hd :: tl -> match find_label_mask hd l' with
    | None -> hd :: mask_diff tl l'
    | Some l' -> mask_diff tl l'

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
  | MRel (l, d) -> d @ (remove_labels f l)

let compose m m' = match m, m' with
  | _, MAbs e -> MAbs e
  | MAbs e, MRel (l, d) -> MAbs (d @ (remove_labels e l))
  | MRel (l1, d1), MRel (l2, d2) ->
    let l, d = l2 >< d1 in
    MRel (l1 @ l, d2 @ d)

let id = MRel ([], [])

let rec extract e l = match e with
  | [] -> if l = [] then Some [] else None
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> extract tl l
    | Some l -> Option.map (fun e -> hd :: e) (extract tl l) 

(* Appendix D.1 *)
let right_residual m m' f = match m, m' with
  | _, MAbs _ -> Some m'
  | MAbs _, _ -> None
  | MRel (l', d'), MRel (l, d) ->
    match extract f (mask_diff l' l) with
    | None -> None
    | Some f ->
      Some (MRel (erase_types d' @ (mask_diff l l'), d @ f))

let rec sub_eff e f =
  match e with
  | [] -> true
  | {eff_type; eff_name} :: tl ->
    match find_label_eff eff_name f with
    | None -> false
    | Some ({eff_type = t'; _}, f') -> eff_type = t' && sub_eff tl f'

let (===) e f = sub_eff e f && sub_eff f e

(* from wenhao's implementation : mu f => nu f *)
let sub_mod mu nu f = match mu, nu with
  | MAbs e, _ ->
    sub_eff e (apply_mod nu f)
  | MRel (l1, d1), MRel (l2, d2) ->
    let l, d = l1 >< d1 in
    let l', d' = l2 >< d2 in
    List.sort compare l = List.sort compare l' && d === d' &&
    extract f l1 <> None && extract f l2 <> None
  | _, _ -> false

let rec get_eff l = function
  | [] -> None
  | {eff_name; eff_type} :: _ when eff_name = l -> Some eff_type
  | _ :: tl -> get_eff l tl

let rec join_eff e e' = match e with
  | [] -> Some e'
  | {eff_name; eff_type} as hd :: e ->
    match find_label_eff eff_name e' with
    | None -> Option.map (fun e -> hd :: e) (join_eff e e')
    | Some ({eff_type = t; _}, e') when t = eff_type ->
      Option.map (fun e -> hd :: e) (join_eff e e')
    | _ -> None

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
  | MAbs e, MAbs e' -> Option.map (fun e -> MAbs e) (join_eff e e')
  | MAbs e, MRel (l, d) | MRel (l, d), MAbs e ->
    if sub_eff e (d @ (remove_labels f l))
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
