open Syntax
open Context
open Errors

exception UnifyError of pure_type * pure_type * expr ctx_binding list
exception Occurs of tvar * pure_type

type mode
  = Infer
  | Check of pure_type
  | Fun of pure_type * mode

let check_ = Bindlib.box_apply (fun a -> Check a)
let fun_ = Bindlib.box_apply2 (fun a m -> Fun (a, m))

let rec box_mode = function
  | Infer -> Bindlib.box Infer
  | Check a -> check_ (box_type a)
  | Fun (a, m) -> fun_ (box_type a) (box_mode m)

let is_guarded a = match a with
  | UGhost _ | Ghost | TForA _ | TMod _ -> false
  | TVar _ | TCon _ | MFlex _ | TArr _ -> true

let is_flex_var = function
  | MFlex _ -> true
  | _ -> false

let rec is_mono = function
  | TVar _
  | MFlex _ -> true
  | TCon (_, a) -> Array.for_all is_mono a
  | TForA _
  | TMod _
  | Ghost
  | UGhost _ -> false
  | TArr (a, b) -> is_mono a && is_mono b

let rec is_type a =
  let ext =
    List.for_all (fun { eff_args; _ } -> Array.for_all is_type eff_args) in
  match a with
  | TVar _ | MFlex _ -> true
  | TArr (a, b) -> is_type a && is_type b
  | Ghost | UGhost _ -> false
  | TCon (_, a) -> Array.for_all is_type a
  | TMod (MAbs d, a) | TMod (MRel (_, d), a) -> ext d && is_type a
  | TForA (_, a) -> is_type (snd (Bindlib.unbind a))

let rec is_wf_ gamma p =
  let ext =
    List.for_all (fun { eff_args; _ } -> Array.for_all (is_wf_ gamma) eff_args)
  in
  match p with
  | TVar alpha | MFlex alpha -> is_in_dom_ alpha gamma
  | TArr (p, q) -> is_wf_ gamma p && is_wf_ gamma q
  | Ghost -> true
  | UGhost p -> is_wf_ gamma p
  | TMod (MAbs d, p) | TMod (MRel (_, d), p) -> ext d && is_wf_ gamma p
  | TForA (k, p) ->
    let alpha, p = Bindlib.unbind p in
    is_wf_ (BType (alpha, k) :: gamma) p
  | TCon (_, a) -> Array.for_all (is_wf_ gamma) a

let is_wf p ({ gamma; _ } as ctx) =
  is_wf_ gamma p, ctx

let subst_var a b v =
  Bindlib.(subst (bind_var v (box_type a) |> unbox) b)

let subst_var_sk m a v =
  Bindlib.(subst (bind_var v (box_mode m) |> unbox) a)

let subst_suffix xi s =
  List.fold_left (fun t b -> match b with
      | BMFlex (a, Some tau, _) -> subst_var t tau a
      | _ -> t) s xi

let guess_mono p k theta ctx =
  let rec aux l k = function
    | MFlex v -> l, MFlex v
    | TVar v -> l, TVar v
    | TCon (c, a) ->
      let { targs; _ } = List.assoc c ctx.data in
      let l, a = aux_array l targs a in
      l, TCon (c, a)
    | UGhost p -> aux l k p
    | TForA (k', a) ->
      let v, a = Bindlib.unbind a in
      let l, a = aux l k a in
      l, Bindlib.(box_type a |> bind_var v |> tfora_ k' |> unbox)
    | Ghost ->
      incr counter;
      let v = Bindlib.new_var (fun v -> MFlex v)
          (Printf.sprintf "x%d" !counter) in
      (BMFlex (v, None, k)) :: l, MFlex v
    | TArr (a, b) ->
      let l, a = aux l Any a in
      let l, b = aux l Any b in
      l, TArr (a, b)
    | TMod (MAbs e, a) ->
      let l, d = aux_eff_ext l e in
      let l, a = aux l Any a in
      l, TMod (MAbs d, a)
    | TMod (MRel (mask, d), a) ->
      let l, d = aux_eff_ext l d in
      let l, a = aux l k a in
      l, TMod (MRel (mask, d), a)
  and aux_array l k a = Array.fold_left_map (fun l (k, a) -> aux l k a) l
      Array.(combine (of_list k) a)
  and aux_eff_ext l =
    List.fold_left_map (fun l { eff_name; eff_args; eff_ho } ->
        let { eargs; _ } = List.assoc eff_name ctx.effects in
        let l, eff_args = aux_array l eargs eff_args in
        l, { eff_name ; eff_args; eff_ho }) l
  in
  aux theta k p

let level = ref 0
let debug = ref false
let rule s =
  incr level;
  if !debug then
    Format.printf "%s %s@." (String.make !level '-') s
let end_rule x =
  decr level;
  x

let protect_context f = fun ctx ->
  let rec drop_marker = function
    | [] -> failwith "drop_marker: internal error"
    | Marker :: tl -> tl
    | BMFlex _ as b :: tl -> b :: drop_marker tl
    | _  :: tl -> drop_marker tl
  in
  let id = ctx.id in
  let tid = ctx.tid in
  let ctx = ctx <: Marker in
  let a, ctx = f ctx in
  a, { ctx with gamma = drop_marker ctx.gamma; id; tid }

(* we do not need Delta as the variables we unbind cannot appear in p *)
let rec join_sk p0 p theta ctx =
  let ctx = { ctx with gamma = theta } in
  match p0, p with
  (* U-GhostR *)
  | Ghost, p ->
    rule "U-GhostR";
    end_rule (p, theta)

  (* U-Ghost *)
  | p, Ghost ->
    rule "U-Ghost";
    end_rule (p, theta)

  (* U-Unit (generalised) *)
  | TCon (c, a), TCon (c', a') when c = c' ->
    rule "U-Con";
    let a, theta = join_sk_array a a' theta ctx in
    end_rule (TCon (c, a), theta)

  (* U-Rigid *)
  | TVar x, TVar y when Bindlib.eq_vars x y ->
    rule "U-Rigid";
    end_rule (TVar x, theta)

  (* U-Flex *)
  | MFlex beta , MFlex alpha ->
    rule "U-Flex";
    let k = get_var_kind_ alpha theta in
    let k' = get_var_kind_ beta theta in
    let theta = join_var alpha k beta k' theta ctx in
    end_rule (MFlex alpha, theta)

  (* U-FlexR *)
  | MFlex alpha, p ->
    rule "U-FlexR";
    let theta = assign alpha p [] theta ctx in
    end_rule (MFlex alpha, theta)

  (* U-FlexL *)
  | p0, MFlex alpha ->
    rule "U-FlexL";
    let theta = assign alpha p0 [] theta ctx in
    end_rule (MFlex alpha, theta)

  (* U-Arrow *)
  | TArr (p1', p2'), TArr (p1, p2) ->
    rule "U-Arrow";
    let q1, theta = join_sk p1' p1 theta ctx in
    let q2, theta = join_sk p2' p2 theta ctx in
    end_rule (TArr (q1, q2), theta)

  (* U-ForallInh *)
  | TForA (k, p0), TForA (k', p) when k = k' ->
    rule "U-ForallInh";
    let alpha, p0, p = Bindlib.unbind2 p0 p in
    let q, theta = join_sk p0 p (BType (alpha, k) :: theta) ctx in
    end_rule ();
    Bindlib.(bind_var alpha (box_type q) |> tfora_ k |> unbox), List.tl theta

  (* U-UnivGhost *)
  | UGhost p0, UGhost p ->
    rule "U-UnivGhost";
    let q, theta = join_sk p0 p theta ctx in
    end_rule (UGhost q, theta)

  (* U-UnivGhost1 *)
  | TForA (k, p0), (UGhost _ as p) ->
    rule "U-UnivGhost1";
    let alpha, p0 = Bindlib.unbind p0 in
    let q, theta = join_sk p0 p (BType (alpha, k) :: theta) ctx in
    end_rule ();
    Bindlib.(bind_var alpha (box_type q) |> tfora_ k |> unbox), List.tl theta

  (* U-ForallSyn *)
  | (UGhost _ as p0), TForA (k, p) ->
    rule "U-ForallSyn";
    let alpha, p = Bindlib.unbind p in
    let q, theta = join_sk p0 p (BType (alpha, k) :: theta) ctx in
    end_rule ();
    Bindlib.(bind_var alpha (box_type q) |> tfora_ k |> unbox), List.tl theta

  (* NEW *)
  (* U-ModInh *)
  | TMod (mu, p0), TMod (nu, p) ->
    rule "U-ModInh";
    let mu', theta = match join_sk_mod mu nu theta ctx with
    | None -> raise (UnifyError (TMod (mu, p0), TMod (nu, p), theta))
    | Some x -> x
    in
    let q, theta = join_sk p0 p theta ctx in
    end_rule (TMod (mu', q), theta)

  (* U-UnivGhost3 *)
  | TMod (mu, p0), (UGhost _ as p) ->
    rule "U-UnivGhost3";
    let q, theta = join_sk p0 p theta ctx in
    end_rule (TMod (mu, q), theta)
    
  (* U-ModSyn *)
  | (UGhost _ as p0), TMod (mu, p) -> 
    rule "U-ModSyn";
    let s', theta = join_sk p0 p theta ctx in
    end_rule (TMod (mu, s'), theta)

  (* END NEW *) 

  (* U-UnivGhost2 *)
  | p0, UGhost p when is_guarded p0 && not (is_flex_var p0) ->
    rule "U-UnivGhost2";
    let res = join_sk p0 p theta ctx in
    end_rule res

  (* U-UnivGhostR *)
  | UGhost p0, p when is_guarded p && not (is_flex_var p) ->
    rule "U-UnivGhostR";
    let res = join_sk p0 p theta ctx in
    end_rule res

  | _ ->
    raise (UnifyError (p0, p, theta))

and join_sk_array a a' theta ctx =
  let l, theta = Array.fold_right (fun (s, p) (a, theta) ->
      let s', theta = join_sk s p theta ctx in
      (s' :: a), theta) (Array.combine a a') ([], theta)
  in Array.of_list l, theta

(* NEW *)
and join_sk_mod mu nu theta ctx =
  let join_sk_eff_ext d d' theta =
    Option.bind
    (List.fold_right (fun { eff_name; eff_args; eff_ho } o -> match o with
          | None -> None
          | Some (d, d', theta) ->
            match Effects.find_label_eff eff_name d' eff_ho with
            | None -> None
            | Some ({ eff_args = eff_args'; _ }, d') ->
              let eff_args, theta =
                join_sk_array eff_args eff_args' theta ctx in
              Some ({ eff_name; eff_args; eff_ho } :: d, d', theta))
       d (Some ([], d', theta)))
    (fun (d, d', theta) ->
       if d' = [] then
         Some (d, theta)
       else None)
  in
  let join_sk_ectx e e' theta = join_sk_eff_ext e e' theta in
  match mu, nu with
  | MRel (l, d), MRel (l', d') when Effects.eq_mask l l' ->
    Option.map (fun (d, theta) -> MRel (l, d), theta)
      (join_sk_eff_ext d d' theta)
  | MAbs e, MAbs e' ->
    Option.map (fun (e, theta) -> MAbs e, theta) (join_sk_ectx e e' theta)
  | _, _ -> None
(* END NEW *)

and join_var alpha k beta k' theta ctx =
  match theta with
  (* U-Flex-Flex-Id *)
  | theta when Bindlib.eq_vars alpha beta && is_in_dom_ alpha theta ->
    rule "U-Flex-Flex-Id";
    end_rule theta

  (* U-Flex-Flex-L *)
  | BMFlex (a', None, k) :: theta when Bindlib.eq_vars alpha a' && k' <<< k ->
    rule "U-Flex-Flex-L"; end_rule ();
    BMFlex (a', Some (MFlex beta), k) :: theta

  (* U-Flex-Flex-R *)
  | BMFlex (b', None, k') :: theta when Bindlib.eq_vars beta b' && k <<< k' ->
    rule "U-Flex-Flex-R"; end_rule ();
    BMFlex (beta, Some (MFlex alpha), k) :: theta

  (* U-Flex-Flex-Assign *)
  | (BMFlex (gamma, Some tau, _) as hd) :: theta ->
    rule "U-Flex-Flex-Assign";
    let _, theta = join_sk (subst_var (MFlex alpha) tau gamma)
        (subst_var (MFlex beta) tau gamma) theta ctx in
    end_rule (hd :: theta)

  (* U-Flex-Flex-Skip *)
  | (BMFlex _ as hd) :: theta ->
    rule "U-Flex-Flex-Skip";
    let theta = join_var alpha k beta k' theta ctx in
    end_rule (hd :: theta)

  (* U-Flex-Flex-Skip' *)
  | ((BVar _ | Marker | BType _ | Lock _) as hd) :: theta ->
    rule "U-Flex-Flex-Skip'";
    let theta = join_var alpha k beta k' theta ctx in
    end_rule (hd :: theta)

  | [] ->
    raise (UnifyError (MFlex alpha, MFlex beta, theta))

and assign alpha p xi theta ctx =
  let ctx = { ctx with gamma = theta } in
  match theta with
  | BMFlex (a', None, k) :: theta when Bindlib.eq_vars alpha a' ->
    begin match p with
      | UGhost (MFlex a') when Bindlib.eq_vars alpha a' ->
        rule "U-Assign-UnivGhost-Id";
        end_rule ((BMFlex (alpha, None, k)) :: theta)
      | _ ->
        rule "U-Assign-SolveM";
        if Bindlib.occur alpha (box_type p) then
          raise (Occurs (alpha, p));
        let beta, tau = guess_mono p k (xi @ theta) ctx in
        if not (is_mono tau) then
          raise (UnifyError (MFlex alpha, tau, theta));
        if k = Abs && not (is_abs tau ctx |> fst) then
          Errors.kind_mismatch None ~expected:Abs ~got:Any tau;
        end_rule (BMFlex (a', Some tau, k) :: beta)
    end

  (* U-Assign-Assign *)
  | (BMFlex (beta, Some tau, _) as hd) :: theta ->
    rule "U-Assign-Assign";
    let _, theta = join_sk (subst_var p tau beta)
        (subst_var (MFlex alpha) tau beta) (xi @ theta) ctx in
    end_rule (hd :: theta)

  (* U-Assign-Depend *)
  | (BMFlex (beta, None, _) as hd) :: theta when
      Bindlib.(occur beta (box_type p) && not (eq_vars alpha beta)) ->
    rule "U-Assign-Depend";
    let theta = assign alpha p (xi @ [hd]) theta ctx in
    end_rule theta

  (* U-Assign-Skip *)
  | (BMFlex (beta, _, _) as hd) :: theta when
      not Bindlib.(occur beta (box_type p) || eq_vars beta alpha) ->
    rule "U-Assign-Skip";
    let theta = assign alpha p xi theta ctx in
    end_rule (hd :: theta)

  (* U-Assign-SkipRigid *)
  | (BType (beta, _) as hd) :: theta when
      not Bindlib.(occur beta (box_type p)) ->
    rule "U-Assign-SkipRigid";
    let theta = assign alpha p xi theta ctx in
    end_rule (hd :: theta)

  (* U-Assign-SkipTmVar *)
  | ((BVar _ | Marker | Lock _) as hd) :: theta ->
    rule "U-Assign-SkipOthers";
    let theta = assign alpha p xi theta ctx in
    end_rule (hd :: theta)

  | _ ->
    raise (UnifyError (MFlex alpha, p, theta))

let rec sk_of_mode = function
  | Infer -> Ghost
  | Check p -> p
  | Fun (p, m) -> TArr (p, sk_of_mode m)

type sup = Ty | Sk

(* polymorphic information extraction does not take kinds into account *)

let rec solve_eq p q =
  match p, q with
  | TCon (c, a), TCon (c', a') when c = c' ->
    rule "SolE-Con";
    end_rule (TCon (c, Array.map2 solve_eq a a'))
  | TVar alpha, _ ->
    rule "SolE-Var";
    end_rule (TVar alpha)
  | Ghost, q ->
    rule "SolE-GhostL";
    end_rule q
  | p, Ghost ->
    rule "SolE-Vacuous";
    end_rule p
  | TArr (p1, p2), TArr (q1, q2) ->
    rule "SolE-Arrow";
    end_rule (TArr (solve_eq p1 q1, solve_eq p2 q2))
  | TForA (k, p), TForA (k', q) when k = k' ->
    rule "SolE-Forall";
    let alpha, p, q = Bindlib.unbind2 p q in
    let p =
      TForA (k, Bindlib.(solve_eq p q |> box_type |> bind_var alpha |> unbox))
    in
    end_rule p
  | UGhost p, UGhost q ->
    rule "SolE-UnivGhost";
    end_rule (UGhost (solve_eq p q))
  | UGhost _ as p, TForA (k, q) ->
    rule "SolE-GhostForall";
    let alpha, q = Bindlib.unbind q in
    let p =
      TForA (k, Bindlib.(solve_eq p q |> box_type |> bind_var alpha |> unbox))
    in
    end_rule p
  | TForA (k, p), (UGhost _ as q) ->
    rule "SolE-ForallGhost";
    let alpha, p = Bindlib.unbind p in
    let p =
      TForA (k, Bindlib.(solve_eq p q |> box_type |> bind_var alpha |> unbox))
    in
    end_rule p
  | TMod (mu, p), TMod (nu, q) ->
    rule "SolE-Mod";
    begin match solve_eq_mod mu nu with
      | None -> raise (UnifyError (TMod (mu, p), TMod (nu, q), []))
      | Some mu -> end_rule (TMod (mu, solve_eq p q))
    end
  | TMod (mu, p), (UGhost _ as q) ->
    rule "SolE-ModGhost";
    end_rule (TMod (mu, solve_eq p q))
  | (UGhost _ as p), TMod (mu, q) ->
    rule "SolE-GhostMod";
    end_rule (TMod (mu, solve_eq p q))
  | UGhost p, q when is_guarded q ->
    rule "SolE-GhostGuarded";
    end_rule (solve_eq p q)
  | p, UGhost q when is_guarded p ->
    rule "SolE-GuardedGhost";
    end_rule (solve_eq p q)
  | MFlex _ as alpha, _ ->
    rule "SolE-FlexL";
    end_rule alpha
  | _, (MFlex _ as alpha) ->
    rule "SolE-FlexR";
    end_rule alpha
  | p, q -> raise (UnifyError (p, q, []))

and solve_eq_mod mu nu =
  let solve_eq_ext d d' =
    Option.bind
    (List.fold_right (fun { eff_name; eff_args; eff_ho } o -> match o with
          | None -> None
          | Some (d, d') ->
            match Effects.find_label_eff eff_name d' eff_ho with
            | None -> None
            | Some ({ eff_args = eff_args'; _ }, d') ->
              let eff_args = Array.map2 solve_eq eff_args eff_args' in
              Some ({ eff_name; eff_args; eff_ho } :: d, d'))
       d (Some ([], d')))
    (fun (d, d') ->
       if d' = [] then
         Some d
       else None)
  in
  match mu, nu with
  | MAbs e, MAbs e' -> Option.map (fun e -> MAbs e) (solve_eq_ext e e')
  | MRel (l, d), MRel (l', d') when Effects.eq_mask l l' ->
    Option.map (fun d -> MRel (l, d)) (solve_eq_ext d d')
  | _, _ -> None

let rec solve_sub m p =
  match m, p with
  | _, (TVar _ as alpha) ->
    rule "SolS-Var";
    end_rule alpha
  | m, TForA (k, p) ->
    rule "SolS-ForallL";
    let alpha, p = Bindlib.unbind p in
    let p =
      TForA (k, Bindlib.(solve_sub m p |> box_type |> bind_var alpha |> unbox))
    in
    end_rule p
  | m, TMod (mu, p) ->
    rule "SolS-ModL";
    end_rule (TMod (mu, solve_sub m p))
  | m, UGhost p ->
    rule "SolS-UnivGhostL";
    end_rule (UGhost (solve_sub m p))
  | (Infer | Check Ghost), p ->
    rule "SolS-Vacuous";
    end_rule p
  | Check (TForA (_, b)), a when is_type a ->
    rule "SolS-ForallR";
    let _, b = Bindlib.unbind b in
    end_rule (solve_sub (Check b) a)
  | Check (TMod (_, b)), a when is_type a ->
    rule "SolS-ModR";
    end_rule (solve_sub (Check b) a)
  | Check b, p when is_guarded p && is_guarded b -> 
    rule "SolS-Check";
    end_rule (solve_eq p b)
  | Fun (q1, m), TArr (p1, p2) ->
    rule "SolS-Arrow";
    end_rule (TArr (solve_eq p1 q1, solve_sub m p2))
  | Fun (q1, m), Ghost ->
    rule "SolS-GhostLF";
    end_rule (UGhost (TArr (solve_eq Ghost q1, solve_sub m Ghost)))
  | Check b, Ghost when is_guarded b ->
    rule "SolS-GhostL";
    end_rule (UGhost b)
  | _, (MFlex _ as alpha) ->
    rule "SolS-Flex";
    end_rule alpha
  | _, p ->
    raise (UnifyError (p, sk_of_mode m, []))

type constr = Empty | Sub of mode | Eq of pure_type * constr

let rec constr_solve p = function
  | Empty -> p
  | Sub m -> solve_sub m p
  | Eq (q, c) -> constr_solve (solve_eq p q) c

let rec constr_collect_eq p p' alpha xi c =
  match p, p' with
  | TVar alpha', p when Bindlib.eq_vars alpha alpha' ->
    rule "LE-Var";
    end_rule (xi, Eq (p, c))

  | p, _ when not Bindlib.(occur alpha (box_type p)) ->
    rule "LE-Absent";
    end_rule (xi, c)

  | _, Ghost ->
    rule "LE-Vacuous";
    end_rule (xi, c)

  | _, MFlex beta ->
    rule "LE-FlexR";
    incr counter;
    let gamma = Bindlib.new_var (fun v -> MFlex v)
        (Printf.sprintf "Ɣ%d" !counter) in
    end_rule ((beta, gamma) :: xi, Eq (MFlex gamma, c))

  | TArr (p1, p2), TArr (q1, q2) ->
    rule "LE-Arrow";
    let xi, c = constr_collect_eq p1 q1 alpha xi c in
    let res = constr_collect_eq p2 q2 alpha xi c in
    end_rule res

  | TCon (con, a), TCon (con', a') when con = con' ->
    rule "LE-Con";
    let res = constr_collect_array a a' alpha xi c in
    end_rule res

  | TForA (k, p), TForA (k', p') when k = k' ->
    rule "LE-ForallInh";
    let _, p, p' = Bindlib.unbind2 p p' in
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | TMod (mu, p), TMod (nu, p') ->
    rule "LE-ModInh";
    begin match constr_collect_mod mu nu alpha xi c with
      | Some (xi, c) ->
        let res = constr_collect_eq p p' alpha xi c in
        end_rule res
      | None ->
        raise (UnifyError (TMod (mu, p), TMod (nu, p'), []))
    end

  | TForA (_, p), (UGhost _ as p') ->
    rule "LE-ForallSyn";
    let res = constr_collect_eq (snd Bindlib.(unbind p)) p' alpha xi c in
    end_rule res

  | TMod (_, p), (UGhost _ as p') ->
    rule "LE-ModSyn";
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | UGhost p, UGhost p' ->
    rule "LE-UnivGhost";
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | UGhost _ as p, TForA (_, p') ->
    rule "LE-UnivGhost1";
    let res = constr_collect_eq p (snd Bindlib.(unbind p')) alpha xi c in
    end_rule res

  | UGhost _ as p, TMod (_, p') ->
    rule "LE-UnivGhost3";
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | UGhost p, p' ->
    rule "LE-UnivGhost2";
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | p, UGhost p' ->
    rule "LE-UnivGhostR";
    let res = constr_collect_eq p p' alpha xi c in
    end_rule res

  | p, p' ->
    raise (UnifyError (p, p', []))

and constr_collect_array a a' alpha xi c =
  Array.combine a a' |>
  Array.fold_left
    (fun (xi, c) (p, p') -> constr_collect_eq p p' alpha xi c) (xi, c)

and constr_collect_mod mu nu alpha xi c =
  let rec ext d d' xi c =
    match d with
    | [] -> if d' = [] then Some (xi, c) else None
    | { eff_ho; eff_args = args; eff_name } :: d ->
      match Effects.find_label_eff eff_name d' eff_ho with
      | None -> None
      | Some ({ eff_args = args'; _ }, d') ->
        let xi, c = constr_collect_array args args' alpha xi c in
        ext d d' xi c
  in
  match mu, nu with
  | MAbs e, MAbs e' -> ext e e' xi c
  | MRel (l, d), MRel (l', d') when Effects.eq_mask l l' -> ext d d' xi c
  | _, _ -> None

let rec constr_collect_sub m p alpha xi =
  match m, p with
  | _, p when not Bindlib.(occur alpha (box_type p)) ->
    rule "LS-Absent";
    end_rule (xi, Empty)

  | m, TVar alpha' when Bindlib.eq_vars alpha alpha' ->
    rule "LS-Var";
    end_rule (xi, Sub m)

  | (Infer | Check Ghost), _ ->
    rule "LS-Vacuous";
    end_rule (xi, Empty)

  | Check (TForA (_, b) as b'), a when is_type a && is_type b' ->
    rule "LS-ForallR";
    let _, b = Bindlib.unbind b in
    let res = constr_collect_sub (Check b) a alpha xi in
    end_rule res

  | Check (TMod (_, b) as b'), a when is_type a && is_type b' ->
    rule "LS-ModR";
    let res = constr_collect_sub (Check b) a alpha xi in
    end_rule res

  | Fun (p1', m), TArr (p1, p2) ->
    rule "LS-Arrow";
    let xi, c = constr_collect_sub m p2 alpha xi in
    let res = constr_collect_eq p1 p1' alpha xi c in
    end_rule res

  | m, TForA (_, p) ->
    rule "LS-ForallL";
    let res = constr_collect_sub m (snd Bindlib.(unbind p)) alpha xi in
    end_rule res

  | m, TMod (_, p) ->
    rule "LS-ModL";
    let res = constr_collect_sub m p alpha xi in
    end_rule res

  | m, UGhost p ->
    rule "LS-UnivGhostL";
    let res = constr_collect_sub m p alpha xi in
    end_rule res

  | Check b, a when is_guarded a && is_guarded b && is_type a && is_type b ->
    rule "LS-Check";
    let res = constr_collect_eq a b alpha xi Empty in
    end_rule res

  | m, p ->
    raise (UnifyError (p, sk_of_mode m, []))

let look p m n alpha k =
  let* () = return () in
  let xi, c = constr_collect_sub m p alpha [] in
  let* xi = M.List.map (fun (alpha, beta) ->
      let* k = get_kind (MFlex alpha) in
      return (BMFlex (beta, None, k))) xi
  in
  let q = constr_solve Ghost c in
  match n with
  | Ty -> fun ctx -> guess_mono q k xi ctx, ctx
  | Sk -> return (xi, q)

let guess_mono_ = guess_mono

let guess_mono p k = fun ({ gamma; _ } as ctx) ->
  let gamma, p = guess_mono p k gamma ctx in
  p, { ctx with gamma }

let rule s = fun ctx ->
  (rule s, ctx)

let end_rule x = fun ctx ->
  end_rule (x, ctx)

let join_sk loc p0 p ({ gamma; _ } as ctx) =
  let p', gamma =
    try
      join_sk p0 p gamma ctx
    with
    | UnifyError _ ->
      Errors.type_mismatch loc ~expected:p0 ~got:p
    | Occurs _ ->
      Errors.type_mismatch loc ~expected:p0 ~got:p
  in
  p', { ctx with gamma }

let check_mask l =
  M.List.map (fun (e, loc) ->
      let* eff = lookup_eff e in
      if Option.is_none eff then
        unknown_eff loc e;
      return e) l

let rec check_type t =
  let check_type_any t =
    check_type_kind t Any
  in
  match t.stype with
  | STMod (mu, a) ->
    let* mu = check_mod mu in
    let* a = check_type_any a in
    return @@ TMod (mu, a)
  | STArr (a, b) ->
    let* a = check_type_any a in
    let* b = check_type_any b in
    return @@ TArr (a, b)
  | STForA (x, k, a) ->
    protect_context @@
    let* v = fresh_tvar x k in
    let* a = check_type_any a in
    return @@ TForA (k, Bindlib.(unbox (bind_var v (box_type a))))
  | STCons (c, l) ->
    let* cons = lookup_data c in
    begin match cons with
      | None -> unknown_var t.tloc c
      | Some { targs; _ } ->
        if List.length targs <> List.length l then
          nb_arg_mismatch t.tloc c (List.length targs) l;
        let* args = M.List.map2 check_type_kind
            l targs $> Array.of_list in
        return @@ TCon (c, args)
    end
  | STVar x ->
    let* tid = lookup_tid x in
    match tid with
    | Some v -> return @@ TVar v
    | None ->
      let* ty = lookup_data x in
      match ty with
      | Some { targs = []; _ } -> return @@ TCon (x, [||])
      | _ -> unknown_var t.tloc x

and check_type_kind t k =
  let* a = check_type t in
  let* k' = get_kind a in
  if not (k' <<< k) then
    kind_mismatch t.tloc a ~expected:k ~got:k';
  return a

and check_mod m = match m.smod with
  | SMAbs e ->
    let* ectx = check_ext e in
    return @@ MAbs ectx
  | SMRel (l, d) ->
    let* l = check_mask l in
    let* d = check_ext d in
    return @@ MRel (l, d)

and check_effect { seff_name; seff_args; eloc } args_kind eff_ho =
  if List.length args_kind <> List.length seff_args then
    nb_arg_mismatch eloc seff_name (List.length args_kind) seff_args;
  let* eff_args = M.List.map2 check_type_kind seff_args args_kind
    $> Array.of_list in
  return { eff_name = seff_name; eff_args; eff_ho }

and check_ext l =
  M.List.map (fun ({ seff_name; eloc; _ } as seff) ->
      let* eff = lookup_eff seff_name in
      match eff with
      | None -> unknown_eff eloc seff_name
      | Some { eargs; eho; _ } -> check_effect seff eargs eho) l

let unfold_ext d =
  M.List.map (fun { eff_name; eff_args; _ } ->
      let* { eops; _ } = get_eff eff_name in
      return @@ Bindlib.msubst eops eff_args) d $> List.flatten $>
  List.map (fun { op_name; op_in; op_out } -> { op_name; op_in; op_out })

let rec sub_eff loc d d' =
  match d with
  | [] -> return true
  | { eff_args; eff_name; eff_ho } :: tl ->
    match Effects.find_label_eff eff_name d' eff_ho with
    | None ->
      return false
    | Some ({ eff_args = eff_args'; _ }, d') ->
      let* _ = M.Array.map2 (join_sk loc) eff_args eff_args' in
      sub_eff loc tl d'

let eq_eff loc d d' = sub_eff loc d d' &&& sub_eff loc d' d

let sub_mod loc mu nu f =
  match mu, nu with
  | MAbs e, _ ->
    sub_eff loc e (Effects.apply_mod nu f)
  | MRel (l1, d1), MRel (l2, d2) ->
    let g = Effects.apply_mod mu f in
    let g' = Effects.apply_mod nu f in
    let l, _ = Effects.(l1 >< d1) in
    let l', _ = Effects.(l2 >< d2) in
    eq_eff loc g g' &&&
    return Effects.(eq_mask l l')
  | _, _ -> return false

let rec join_eff_ext loc d d' = match d with
  | [] -> return (Some d')
  | { eff_name; eff_args; eff_ho } as hd :: d ->
    match Effects.find_label_eff eff_name d' eff_ho with
    | None ->
      join_eff_ext loc d d' >>= begin function
        | None -> return None
        | Some e -> return (Some (hd :: e))
      end
    | Some ({ eff_args = eff_args'; _ }, d') ->
      let* _ = M.Array.map2 (join_sk loc) eff_args eff_args' in
      join_eff_ext loc d d' >>= function
        | None -> return None
        | Some e -> return (Some (hd :: e))

let join_ectx e e' =
  join_eff_ext e e'

let rec meet_eff loc e e' = match e with
  | [] -> return (Some [])
  | { eff_name; eff_args; eff_ho } as hd :: e ->
    match Effects.find_label_eff eff_name e' eff_ho with
    | None -> meet_eff loc e e'
    | Some ({ eff_args = eff_args'; _ }, e') ->
      let* _ = M.Array.map2 (join_sk loc) eff_args eff_args' in
      meet_eff loc e e' >>= function
      | None -> return None
      | Some e -> return (Some (hd :: e))

let join_mod loc m m' f = match m, m' with
  | MAbs e, MAbs e' ->
    join_ectx loc e e' >>= begin function
    | None -> return None
    | Some e -> return (Some (MAbs e))
    end
  | MAbs e, MRel (l, d) | MRel (l, d), MAbs e ->
    sub_eff loc e Effects.(extend d (remove_labels f l)) >>= begin function
    | true -> return (Some (MRel (l, d)))
    | false -> return None
    end
  | MRel (l, d), MRel (l', d') ->
    meet_eff loc d d' >>= function
    | None -> return None
    | Some d'' ->
      let mu = MRel (Effects.meet_mask l l', d'') in
      sub_mod loc m mu f &&& sub_mod loc m' mu f >>= function
      | true -> return (Some mu)
      | false -> return None

let rec sub loc m n p e =
  match m, n, p with
  (* SI-Infer *)
  | Infer, _, s ->
    rule "SI-Infer" >>
    end_rule s

  (* SI-ForallR *)
  | Check TForA (k, b), Ty, a ->
    rule "SI-ForallR" >>
    let v, b = Bindlib.unbind b in
    with_binding (BType (v, k)) @@
    let* _ = sub loc (Check b) Ty a e in
    end_rule a

  (* SI-Arrow *)
  | Fun (p1', m), n, TArr (p1, p2) ->
    rule "SI-Arrow" >>(
    let* q1 = join_sk loc p1' p1 in
    let* q2 = sub loc m n p2 e in
    end_rule (TArr (q1, q2)))

  (* NEW *)
  (* SI-Mod *)
  | Check (TMod _ as b'), Ty, a' ->
    rule "SI-Mod" >>
    let mu, b = get_guarded b' in
    let nu, a = get_guarded a' in
    let* b = sub loc (Check b) Ty a (Effects.apply_mod mu e) in
    unless (is_abs b ||| sub_mod loc nu mu e)
      (fun () -> Errors.mod_mismatch loc ~expected:mu ~got:nu e) >>
    end_rule b'
  | Check b, Ty, (TMod _ as a) ->
    sub loc (Check (TMod (Effects.id, b))) Ty a e >>= begin function
      | TMod (MRel ([], []), a) -> return a
      | _ -> failwith "sub: internal error"
    end

  (* SI-ModFun *)
  | (Fun _ as m), Ty, (TMod _ as s) -> 
    rule "SI-ModFun-Ty" >>
    let mu, s = get_guarded s in
    unless (sub_mod loc mu Effects.id e)
      (fun () ->
         Errors.no_unboxing loc mu e) >>
    sub loc m n s e >>=
    end_rule

  (* SI-Mod-Sk *)
  | (Fun _ | Check _), Sk, TMod (_, s) ->
    rule "SI-ModFun-Sk" >>
    sub loc m Sk s e >>=
    end_rule
  (* END NEW *)
    
  (* SI-ForallL *)
  | (Fun _ | Check _) as m, n, TForA (k, bp) ->
    rule "SI-ForallL" >>
    let alpha, p = Bindlib.unbind bp in
    let* xi, p1 = look p m n alpha k in
    add_bindings xi >>
    unless (is_wf p1)
      (fun () -> Errors.type_mismatch loc
          ~expected:(sk_of_mode m) ~got:(TForA (k, bp))) >>
    (if n = Ty then
      let* k' = get_kind p1 in
      if k = Abs && k' = Any then
        Errors.kind_mismatch loc ~expected:k ~got:k' p1
      else return ()
    else
      return ()) >>
    sub loc m n (Bindlib.subst bp p1) e >>= 
    end_rule

  (* SI-UnivGhostL *)
  | (Fun _ | Check _), Sk, UGhost p ->
    rule "SI-UnivGhostL" >>
    sub loc m Sk p e >>=
    end_rule

  (* SI-Ghost *)
  | (Fun _ | Check _), Sk, Ghost ->
    rule "SI-Ghost" >>
    end_rule @@ sk_of_mode m

  (* SI-FlexMono *)
  | Fun _, _, (MFlex alpha) ->
    rule "SI-FlexMono" >>
    let* k = get_kind (MFlex alpha) in
    if k = Abs then
      Errors.kind_mismatch loc ~expected:Any ~got:k (MFlex alpha);
    sub_flex loc [] m n alpha e >>=
    end_rule

  (* SI-Check *)
  | Check b, Ty, a when is_guarded a && is_guarded b  ->
    rule "SI-Check" >>
    join_sk loc a b >>=
    end_rule

  (* SI-UnivGhostR *)
  | Check Ghost, Sk, p when is_guarded p ->
    rule "SI-UnivGhostR" >>
    end_rule (UGhost p)

  | mode, _, s ->
    Errors.type_mismatch loc ~expected:(sk_of_mode mode) ~got:s

and sub_flex loc xi m n alpha0 e =
  let* b = pop_binding () in
  match b with
  | BMFlex (alpha0', None, _) when Bindlib.eq_vars alpha0 alpha0' ->
    rule "SI-Flex-Solve" >>
    let* alpha = fresh_mflex Any in
    let* beta = fresh_mflex Any in
    let a = TArr (MFlex alpha, MFlex beta) in
    add_binding (BMFlex (alpha0', Some a, Any)) >>
    add_bindings xi >>
    sub loc m n a e >>=
    end_rule
    
  | BMFlex (beta, Some tau, _) as bind ->
    rule "SI-Flex-Assign" >>
    add_bindings xi >>
    let* q =
      sub loc (subst_var_sk m tau beta) n (subst_var (MFlex alpha0) tau beta) e
    in
    add_binding bind >>
    end_rule q

  | BMFlex (b, None, _) as bind when Bindlib.occur b (box_mode m) ->
    rule "SI-Flex-Depend" >>
    sub_flex loc (xi @ [bind]) m n alpha0 e >>=
    end_rule

  | BMFlex (_, None, _) as bind ->
    rule "SI-Flex-Skip" >>
    let* q = sub_flex loc xi m n alpha0 e in
    add_binding bind >>
    end_rule q

  | BType (b, _) as bind when not Bindlib.(occur b (box_mode m)) ->
    rule "SI-Flex-SkipRigid" >>
    let* q = sub_flex loc xi m n alpha0 e in
    add_binding bind >>
    end_rule q

  | Marker | Lock _ -> failwith "broom_flex_poly: should not happen"

  | _ ->
    Errors.type_mismatch loc ~expected:(sk_of_mode m) ~got:(MFlex alpha0)

let split_fun loc = function
  | Ghost -> return (Ghost, Ghost)
  | TArr (p, q) -> return (p, q)
  | MFlex a ->
    let* b = fresh_mflex Any in
    let* c = fresh_mflex Any in
    let* _ = join_sk loc (MFlex a) (TArr (MFlex b, MFlex c)) in
    return (MFlex b, MFlex c)
  | a -> Errors.function_non_arr loc a

let unfun_mode m p = match m with
  | Fun (_, m) -> m
  | Check _ -> Check p
  | Infer -> Infer

let rec split_fun_check loc a e = match a with
  (* NEW *)
  | TMod (mu, a) ->
    add_binding (Lock (mu, e)) >>
    split_fun_check loc a Effects.(apply_mod mu e)
  (* END NEW *)
  | TForA (k, a) ->
    let v, a = Bindlib.unbind a in
    add_binding (BType (v, k)) >>
    split_fun_check loc a e
  | TArr (a, b) -> return (a, b, e)
  | a -> Errors.function_non_arr loc a

let rec split_con_check a e = match a with
  (* NEW *)
  | TMod (mu, a) ->
    add_binding (Lock (mu, e)) >>
    split_con_check a Effects.(apply_mod mu e)
  (* END NEW *)
  | TForA (k, a) ->
    let v, a = Bindlib.unbind a in
    add_binding (BType (v, k)) >>
    split_con_check a e
  | a -> return (a, e)

let app_of_con loc c l =
  List.fold_left (fun m n -> { sexpr = SApp (m, n) ; loc = m.loc })
    { sexpr = SVar c; loc = loc } l

let con_of_app c m =
  let rec get_args acc = function
    | App (m, n) -> get_args (n :: acc) m
    | _ -> acc
  in
  Con (c, get_args [] m)

let let_of_seq loc m n =
  { sexpr = SLet ("_", { sexpr = SAnn (m, { stype = STCons ("unit", []) ; tloc = None }); loc = m.loc }, n ); loc }

let get_con_args = function
  | TCon (_, a) -> a
  | _ -> failwith "get_con_args: internal error"
  

let rec split_pat vars mu e a { spat; ploc } =
  let nu, g = get_guarded a in
  let mu = Effects.compose mu nu in
  match spat with
  | SPWild -> return (vars, PWild)
  | SPVar x ->
    let* v = fresh_var x (TMod (mu, g)) in
    return (v :: vars, PVar (TMod (mu, g)))
  | SPCons (con, pats) ->
    lookup_con con >>= function
    | None -> Errors.unknown_cons ploc con None
    | Some (c, targs, l) ->
      let* l =
        sub ploc (Check g) Ty
          (TCon (c, Array.make (List.length targs) Ghost))
          Effects.(apply_mod mu e) $> get_con_args $> Bindlib.msubst l in
      let* res, l = M.List.fold_right (fun (a, p) (vars, l) ->
          split_pat vars mu e a p $> Pair.map_snd (fun x -> x :: l))
          (List.combine l pats) (vars, []) in
      return (res, PCon (con, l))

let join loc f a b =
  let mu, a = get_guarded a in
  let nu, b = get_guarded b in
  let* a = join_sk loc a b in
  is_abs a >>= function
  | true -> return a
  | false ->
    join_mod loc mu nu f >>= function
    | None -> Errors.mod_mismatch loc ~expected:mu ~got:nu f
    | Some mu ->
      return (TMod (mu, a)) 

let rec sk_infer m { sexpr; loc } e = match m, sexpr with
  | m, SInt _ ->
    rule "PI-Int" >>
    let* q = sub loc m Sk (TCon ("int", [||])) e in
    end_rule q

  | m, SStr _ ->
    rule "PI-Str" >>
    let* q = sub loc m Sk (TCon ("string", [||])) e in
    end_rule q

  (* PI-Var *)
  | m, SVar x ->
    rule "PI-Var" >>
    lookup_id x >>= begin function
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, q, _ = get_type_context v in
        sub loc m Sk q e >>= end_rule
    end

  (* PI-Anno *)
  | m, SAnn (_, a) ->
    rule "PI-Anno" >>
    let* a = check_type a in
    sub loc m Sk a e >>= end_rule

  (* PI-Freeze *)
  | Check Ghost, SFreeze m ->
    rule "PI-Freeze" >>
    sk_infer Infer m e >>=
    end_rule

  (* PI-AbsCheck *)
  | Check Ghost, SLam (x, None, m) ->
    rule "PI-AbsCheck" >>
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x Ghost in
        get_suffix @@
        sk_infer (Check Ghost) m e
      end in
    add_bindings xi >>
    end_rule @@ UGhost (TArr (Ghost, q))

  (* PI-Abs *)
  | (Fun _ | Infer) as mode, SLam (x, None, m) ->
    rule "PI-Abs" >>
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x p in
        get_suffix @@
        sk_infer (unfun_mode mode q) m e
      end in
    add_bindings xi >>
    end_rule @@ TArr (p, q')

  (* PI-AbsAnnoCheck *)
  | Check Ghost, SLam (x, Some a, m) ->
    rule "PI-AbsAnnoCheck" >>
    let* a = check_type a in
    let* q, xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (Check Ghost) m e
      end in
    add_bindings xi >>
    end_rule @@ UGhost (TArr (a, q))

  (* PI-Abs *)
  | (Fun _ | Infer) as mode, SLam (x, Some a, m) ->
    rule "PI-Abs" >>
    let* a = check_type a in
    let* _, q = split_fun loc (sk_of_mode mode) in
    let* q', xi =
      protect_context begin
        let* _ = fresh_var x a in
        get_suffix @@
        sk_infer (unfun_mode mode q) m e
      end in
    add_bindings xi >>
    end_rule @@ TArr (a, q')

  (* PI-App *)
  | mode, SApp (m, n) ->
    rule "PI-App" >>
    let* p = sk_infer (Check Ghost) n e in
    let* q' = sk_infer (Fun (p, mode)) m e >>= split_fun None $> snd in
    end_rule q'

  (* NEW *)
  (* PI-Do *)
  | mode, SDo (op, _) ->
    (* The interaction of skeleton inference and the effect context is complex
    we might be under a universal ghost, who could introduce the effect we are
    looking for. We stay conservative for now *)
    rule "PI-Do" >>
    let* _, { eargs; _ }, bop = lookup_op op >>= function
      | None -> Errors.unknown_eff loc op
      | Some p -> return p
    in
    let { op_out; _ } = Bindlib.msubst bop
        (List.map (fun _ -> Ghost) eargs |> Array.of_list) in
    sub loc mode Sk op_out e >>= 
    end_rule

  (* PI-Handle *)
  | mode, SHand (m, _, (h, (x, n))) ->
    rule "PI-Handle" >>
    let* eff_name, { eargs; eho; _ }, _ =
      lookup_op (fst (List.hd h)) >>= function
      | Some x -> return x
      | None ->
        let (op, (loc, _, _, _)) = List.hd h in
        Errors.unknown_eff loc op
    in
    let* p = sk_infer Infer m e in
    let d =
      [{ eff_name
       ; eff_args = List.map (fun _ -> Ghost) eargs |> Array.of_list
       ; eff_ho = eho }] in
    let* ops = unfold_ext d in
    let* p, xi = protect_context @@
      let* _ = fresh_var x (TMod (MRel ([], d), p)) in
      get_suffix @@
      sk_infer mode n e
    in
    add_bindings xi >>
    let sk_infer_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> Errors.unknown_eff loc li
      | Some (ai, bi) ->
        let* p, xi = 
          protect_context @@
          let* _ = fresh_var pi ai in
          let* _ = fresh_var ri (TArr (bi, p)) in
          get_suffix @@
          sk_infer mode ni e
        in
        add_bindings xi >> return p
    in
    let* p' = M.List.map sk_infer_clause h in
    M.List.fold_left (join_sk loc) p p' >>=
    end_rule

  (* PI-Match *)
  | mode, SMatch (m, l) ->
    ignore (mode, m, l);
    rule "PI-Match" >>
    let rec split_pat p { spat; ploc } = match spat with
      | SPWild -> return ()
      | SPVar x ->
        let* _ = fresh_var x p in return ()
      | SPCons (con, l) ->
        let* c, args, bp = lookup_con con >>= function
          | None -> Errors.unknown_cons ploc con None
          | Some x -> return x
        in
        let* targs =
         join_sk loc (TCon (c, List.map (fun _ -> Ghost) args
                |> Array.of_list)) p
         $> get_con_args in
        M.List.iter2 split_pat (Bindlib.msubst bp targs) l
    in
    let* p = sk_infer Infer m e in
    M.List.map (fun (pat, n) ->
        let* p, xi =
          protect_context @@
          (split_pat p pat >> get_suffix (sk_infer mode n e))
        in
        add_bindings xi >> return p) l >>=
    M.List.fold_left (join_sk loc) Ghost >>=
    end_rule

  (* PI-Con *)
  | mode, SCons (c, l) ->
    rule "PI-Con" >>
    let* p = sk_infer mode (app_of_con loc c l) e in
    begin match mode, p with
      | Check _, (UGhost _ as p) -> end_rule p
      | Check _, p -> end_rule (UGhost p)
      | _ -> end_rule p
    end

  (* PI-Let *)
  | mode, SLet (x, m, n) ->
    rule "PI-Let" >>
    let* s = sk_infer Infer m e in
    protect_context @@
    let* _ = fresh_var x s in
    (sk_infer mode n e >>= end_rule)
  | mode, SSeq (m, n) ->
    sk_infer mode (let_of_seq loc m n) e

  (* PI-Mask *)
  | mode, SMask (_, m) ->
    rule "PI-Mask" >>
    sk_infer mode m e

  (* END NEW *) 

  | _, _ -> Errors.cannot_infer_expr loc

let rec finfer m { sexpr; loc } e = match m, sexpr with
  (* I-Unit *)
  | m, SCons ("Unit", []) ->
    rule "I-Unit" >>
    let* a = sub loc m Ty (TCon ("unit", [||])) e in
    end_rule (a, Con ("Unit", []))

  | m, SInt n ->
    rule "I-Int" >>
    let* a = sub loc m Ty (TCon ("int", [||])) e in
    end_rule (a, Lit (Int n))

  | m, SStr s ->
    rule "I-Str" >>
    let* a = sub loc m Ty (TCon ("string", [||])) e in
    end_rule (a, Lit (Str s))

  (* I-Var *)
  | m, SVar x ->
    rule "I-Var" >>
    lookup_id x >>= begin function
      | None -> Errors.unknown_var loc x
      | Some v ->
        let* _, a, gamma' = get_type_context v in
        (* NEW *)
        let nu, f = locks e gamma' in
        let* a = across a nu f in
        match a with
        | None -> Errors.no_access loc x v e
        | Some a ->
          let* b = sub loc m Ty a e in
          end_rule (b , Var v)
        (* END NEW *)
    end

  (* I-Anno *)
  | mode, SAnn (m, a) ->
    rule "I-Anno" >>
    let* a = check_type a in
    let* _, m = finfer (Check a) m e in
    let* b = sub loc mode Ty a e in
    end_rule (b, m)

  (* I-Freeze *)
  | Check a, SFreeze m ->
    rule "I-Freeze" >>
    let* b, m = finfer Infer m e in
    let* _ = join_sk loc b a in
    end_rule (a, m)

  (* I-AbsCheck and I-AbsAnnoCheck *)
  | Check t, SLam (x, a, m) ->
    rule "I-AbsCheck" >>
    protect_context begin
      let* a', b, e = split_fun_check loc t e in
      let* a = match a with
        (* I-AbsCheck *)
        | None -> return a'
        (* I-AbsAnnoCheck *)
        | Some a ->
          let* a = check_type a in
          join_sk loc a' a
      in
      let* v = fresh_var x a in
      let* _, m = finfer (Check b) m e in
      end_rule (t, Bindlib.(box_expr m |> bind_var v |> lam_ |> unbox))
    end

  (* I-Abs and I-AbsAnno *)
  | (Infer | Fun _) as mode, SLam (x, a', m) ->
    rule "I-Abs" >>
    let* p, q = split_fun loc (sk_of_mode mode) in
    let* a = match a' with
      (* I-Abs *)
      | None -> guess_mono p Any
      (* I-AbsAnno  *)
      | Some a ->
        let* a = check_type a in
        join_sk loc p a
    in let* p, xi =
      protect_context begin
        let* v = fresh_var x a in
        get_suffix @@
        let* b, m = finfer (unfun_mode mode q) m e in
        return (TArr (a, b),
                Bindlib.(box_expr m |> bind_var v |> lam_ |> unbox))
      end in
    add_bindings xi >>
    end_rule p

  (* I-App *)
  | mode, SApp (m, n) ->
    rule "I-App" >>
    let* p = sk_infer (Check Ghost) n e in
    let* t, m = finfer (Fun (p, mode)) m e in
    let* a, b = split_fun None t in
    let* _, n = finfer (Check a) n e in
    end_rule (b, App (m, n))

  (* NEW *)
  (* I-Do *)
  | mode, SDo (op, m) ->
    rule "I-Do" >>
    let* a, b = lookup_op_in_ectx op e >>= function
    | None -> Errors.unknown_eff loc op
    | Some (l, ({ op_in; op_out; _ }, { eff_ho; _ }), _) ->
      (if eff_ho && l <> [] then
         Errors.higher_order_effect_not_first loc op e
      else return ()) >>
      return (op_in, op_out)
    in
    let* _, m = finfer (Check a) m e in
    let* b = sub loc mode Ty b e in
    end_rule (b, Do (op, m))

  (* I-Handle *)
  | mode, SHand (m, None, (h, (x, n))) ->
    rule "I-Handle" >>
    let* eff_name, { eargs; eho; _} , _ = lookup_op (fst (List.hd h)) >>=
      function
      | Some x -> return x
      | None ->
        let (op, (loc, _, _, _)) = List.hd h in
        Errors.unknown_eff loc op
    in
    let* vars = fresh_mflexs eargs in
    let eff_args = Array.map (fun a -> MFlex a) vars in
    let d = [{ eff_name; eff_args; eff_ho = eho }] in
    let nu = MRel ([], d) in
    let* a, m = with_binding (Lock (nu, e)) @@
      finfer Infer m (Effects.extend d e) in
    let* (b, n), xi = protect_context @@
      let* ret = fresh_var x (TMod (nu, a)) in
      get_suffix @@
      let* b, n = finfer mode n e in
      let n = Bindlib.(n |> box_expr |> bind_var ret |> unbox) in
      return (b, n)
    in
    add_bindings xi >>
    let* ops = unfold_ext d in
    let homod = if eho then fun a ->
        is_abs a >>= function
        | true -> return a
        | false -> return (TMod (nu, a))
      else fun a -> return a in
    let check_clause (li, (loc, pi, ri, ni)) =
      match Effects.get_op li ops with
      | None -> Errors.unknown_eff loc li
      | Some (ai, bi) ->
        let* bi, ni, xi = 
          protect_context @@
          let* pi = homod ai >>= fresh_var pi in
          let* bi = homod bi in
          let* ri = fresh_var ri (TArr (bi, b)) in
          let* (bi, ni), xi = get_suffix @@ finfer mode ni e in
          return (bi, (li, Bindlib.(box_expr ni |> bind_var ri |> bind_var pi
                             |> unbox)), xi)
        in add_bindings xi >> return (bi, ni)
    in
    let* b', h = M.List.map check_clause h $> List.split in
    let* b = M.List.fold_left (join loc e) b b' in
    end_rule (b, Hand (m, ops, n, h))

  (* I-ConCheck *)
  | Check a, (SCons (c, l) as m) when is_val m ->
    rule "I-ConCheck" >>
    protect_context @@
    let* a, e = split_con_check a e in
    (finfer (Check a) (app_of_con loc c l) e $>
     Pair.map_snd (con_of_app c) >>= end_rule)

  (* I-Con *)
  | mode, SCons (c, l) ->
    rule "I-Con" >>
    finfer mode (app_of_con loc c l) e $>
    Pair.map_snd (con_of_app c) >>=
    end_rule

  (* I-Match *)
  | mode, SMatch (m, l) -> 
    rule "I-Match" >>
    let* b, m = finfer Infer m e in
    let check_branch (p, n) =
      protect_context @@
      let* vars, p = split_pat [] Effects.id e b p in
      let mvar = Array.of_list vars in
      let* a, n = finfer mode n e in
      return (a, (p, Bindlib.(n |> box_expr |> bind_mvar mvar |> unbox)))
    in
    let* a, l = M.List.map check_branch l $> List.split in
    let* a = M.List.fold_left (join loc e) Ghost a in
    end_rule (a, Match (m, l))

  (* I-Let *)
  | mode, SLet (x, m, n) ->
    rule "I-Let" >>
    let* a, m = finfer Infer m e in
    let* b, n, v = protect_context @@
      let* v = fresh_var x a in
      let* b, n = finfer mode n e in
      return (b, n, v)
    in
    end_rule (b, Let (m, a, Bindlib.(box_expr n |> bind_var v |> unbox)))
  | mode, SSeq (m, n) ->
    finfer mode (let_of_seq loc m n) e

  (* I-MaskInfer *)
  | Infer, SMask (l, m) -> 
    let* l = check_mask l in
    let* a, m =
      with_binding (Lock (MRel (l, []), e)) @@
      finfer Infer m (Effects.remove_labels e l)
    in
    end_rule (TMod (MRel (l, []), a), Mask (l, m))

  (* I-MaskCheck *)
  | Check (TMod (MRel (l', []), a) as a'), SMask (l, m)
    when Effects.eq_mask (List.split l |> fst) l' ->
    rule "I-MaskCheck" >>
    let* _, m =
      with_binding (Lock (MRel (l', []), e)) @@
      finfer (Check a) m (Effects.remove_labels e l')
    in
    end_rule (a', Mask (l', m))

  (* I-MaskSwitch *)
  | mode, (SMask _ as sexpr) ->
    rule "I-MaskSwitch" >>
    let* a, m = finfer Infer { sexpr; loc } e in
    let* a = sub loc mode Ty a e in
    end_rule (a, m)

  (* END NEW *)

  | _ ->
    Errors.cannot_infer_expr loc


let _, init_ctx =
  let int = TCon ("int", [||]) in
  let bool = TCon ("bool", [||]) in
  let string = TCon ("string", [||]) in
  let unit = TCon ("unit", [||]) in
  let (@->) t t' = TArr (t, t') in
  let v = Bindlib.new_var (fun v -> TVar v) "fail" in
  let abs t = TMod (MAbs [], t) in
  fresh_vars
    [("+", abs (int @-> int @-> int));
     ("*", abs (int @-> int @-> int));
     ("-", abs (int @-> int @-> int));
     ("=", abs (int @-> int @-> bool));
     ("string_eq", abs (string @-> string @-> bool));
     ("string_of_int", abs (int @-> string));
     ("^", abs (string @-> string @-> string));
     ("&&", abs (bool @-> bool @-> bool));
     ("fail", abs (TForA (Any, Bindlib.(unit @-> (TVar v) |> box_type |> bind_var v |> unbox))));
     ("print", abs (string @-> unit))]
    { gamma = [] ; tid = [] ; id = [] ; effects = []
    ; data = ["int", { targs = [] ; cons = [] };
              "string", { targs = [] ; cons = [] } ] }

let check_decl (prog, ctx) d = match d with
  | (_, SDFun _), _ -> failwith "check_decl: internal error"
  | (x, SDSig t), _ ->
    let a,_ = check_type t ctx in
    let _, ctx = fresh_var x a ctx in
    prog, ctx
  | (x, SDEff (eho, args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let eargs = snd (List.split args) in
    let mvar, ctx' = fresh_tvars args ctx in
    let dummy_ops = Bindlib.(box_list [] |> bind_mvar mvar |> unbox) in
    let ctx' = { ctx' with effects = (x, { eargs; eops = dummy_ops; eho }) ::
                                     ctx'.effects } in
    let k = if eho then Any else Abs in
    let l =
      List.map (fun (x, (a, b)) ->
          { op_name = x; op_in = fst (check_type_kind a k ctx')
          ; op_out = fst (check_type_kind b k ctx') })
        l |> box_ops in
    prog,
    { ctx with
      effects = (x, { eargs; eops = Bindlib.(bind_mvar mvar l |> unbox); eho}) ::
                ctx.effects }
  | (x, SDADT (args, l)), _ ->
    (* add mock definition in the context just for type verification *)
    let targs = snd (List.split args) in
    let ctx' = { ctx with data = (x, { targs; cons = [] }) :: ctx.data } in
    let mvar, ctx' = fresh_tvars args ctx' in
    let cons = List.map
        (fun (c, l) ->
           let l = List.map (fun a -> box_type (fst (check_type a ctx'))) l
                |> Bindlib.box_list in
           c, Bindlib.(bind_mvar mvar l |> unbox)) l in
    (* NEW *)
    let _, ctx = M.List.iter
        (fun (c, l) ->
           let v, types = Bindlib.unmbind l in
           let a = List.fold_right (fun a b -> TArr (a, b)) types
               (TCon (x, Array.map (fun v -> TVar v) v)) in
           let a = TMod (MAbs [], a) in
           let v = Array.to_list v in
           let* _ = fresh_var c @@
             List.fold_right2
               (fun v (_, k) a ->
                  (TForA (k, Bindlib.(bind_var v (box_type a) |> unbox))))
               v args a in
           return ()
        ) cons ctx in
    (* END NEW *)
    prog, { ctx with data = (x, { targs; cons }) :: ctx.data }

