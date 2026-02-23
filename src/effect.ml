open Syntax

let erase_types = List.map (fun {eff_name; _} -> {eff_name; eff_type = None})

let rec find_label_mask l = function
  | [] -> None
  | hd :: tl when hd.eff_name = l -> Some tl
  | hd :: tl -> match find_label_mask l tl with
    | None -> None
    | Some mask -> Some (hd :: mask)

let rec remove_labels e l = match e with
  | [] -> []
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> hd :: remove_labels tl l
    | Some l -> remove_labels tl l

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

let present = List.for_all (fun { eff_type; _ } -> eff_type <> None )

let rec extract e l = match e with
  | [] -> if l = [] then Some [] else None
  | hd :: tl -> match find_label_mask hd.eff_name l with
    | None -> extract tl l
    | Some l -> Option.bind (extract tl l) (fun e -> Some (hd :: e))

(* Appendix D.1 *)
let right_residual m m' f = match m, m' with
  | _, MAbs _ -> Some m'
  | MAbs _, _ -> None
  | MRel (l', d'), MRel (l, d) ->
    match extract f (remove_labels l' l) with
    | None -> None
    | Some f ->
      if present f then
        Some (MRel (erase_types d' @ (remove_labels l l'), d @ f))
      else
        None
