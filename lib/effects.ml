open Syntax

let erase_types = List.map (fun { eff_name; _ } -> eff_name)

let rec get_first f = function
  | [] -> None
  | hd :: tl when f hd -> Some (hd, tl)
  | hd :: tl ->
    Option.map (fun (x, l) -> x, hd :: l) (get_first f tl)

let find_label_mask lab mask =
  Option.map snd (get_first ((=) lab) mask)

let find_label_eff lab d eff_ho =
  if eff_ho then
    match d with
    | { eff_name; _ } as hd :: tl when eff_name = lab -> Some (hd, tl)
    | _ -> None
  else
    get_first (fun { eff_name; _ } -> eff_name = lab) d

let rec remove_labels_ext d l = match d with
  | [] -> ([], l)
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None ->
      let tl, l = remove_labels_ext tl l in
      hd :: tl, l
    | Some l -> remove_labels_ext tl l

let remove_labels d l =
  let d, _ = remove_labels_ext d l in
  d

let rec mask_diff l l' = match l with
  | [] -> []
  | hd :: tl -> match find_label_mask hd l' with
    | None -> hd :: mask_diff tl l'
    | Some l' -> mask_diff tl l'

let extend d' d =
  d' @ d

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
let right_residual mu nu f =
  match mu, nu with
  | _, MAbs _ -> Some nu
  | MAbs _, _ -> None
  | MRel (l', d'), MRel (l, d) ->
    match extract f (mask_diff l' l) with
    | None -> None
    | Some f ->
      Some (MRel (erase_types d' @ (mask_diff l l'), d @ f))

let eq_mask l l' =
  List.sort compare l = List.sort compare l'

let rec get_op l = function
  | [] -> None
  | { op_name; op_in; op_out } :: _ when op_name = l -> Some (op_in, op_out)
  | _ :: tl -> get_op l tl

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
