open Syntax

let counter = ref 0

type 'a ctx_binding
  = Lock of concrete_mod
  | BVar of 'a Bindlib.var * pure_type
  | BType of tvar * kind
  | Marker

  | BMFlex of tvar * pure_type option * kind
  | BPFlex of tvar * pure_type * kind
type eff =
  { eargs : kind list ; eops : (pure_type, op list) Bindlib.mbinder ; eho : bool }

type adt =
  { targs : kind list ; cons : (string * (pure_type, pure_type list) Bindlib.mbinder) list }

type 'a ctx =
  { gamma : 'a ctx_binding list
  ; effects : (string * eff) list
  ; data : (string * adt) list
  ; id : (string * var) list
  ; tid : (string * tvar) list }

let (<:) ({gamma; _} as ctx) b =
  { ctx with gamma = b :: gamma }

let bind f g = fun ctx ->
  let a, ctx = f ctx in
  g a ctx

let (let*) = bind

let (>>=) = bind

let (>>) f g =
  let* () = f in
  g

let return x = fun ctx -> x, ctx

let ($>) x f =
  let* x = x in
  return (f x)

let (|||) a b =
  let* a = a in
  if a then
    return true
  else b

let (&&&) a b =
  let* a = a in
  if a then
    b
  else return false

let unless c f =
  let* c = c in
  if c then
    return ()
  else
    f ()

let (@>) f g =
  let* x = f in
  g x

module M = struct
  module List = struct
    let rec map f = function
      | [] -> return []
      | hd :: tl ->
        let* x = f hd in
        let* xs = map f tl in
        return (x :: xs)


    let rec map2 f l l' = match l, l' with
      | [], [] -> return []
      | hd :: tl, hd' :: tl' ->
        let* x = f hd hd' in
        let* xs = map2 f tl tl' in
        return (x :: xs)
      | _, _ -> failwith "map2: internal error"

    let rec iter f = function
      | [] -> return ()
      | hd :: tl -> f hd >> iter f tl
    
    let rec iter2 f l l' = match l, l' with
      | [], [] -> return ()
      | hd :: tl, hd' :: tl' -> f hd hd' >> iter2 f tl tl'
      | _, _ -> failwith "iter2: internal error"

    let rec fold_right f l acc = match l with
      | [] -> return acc
      | hd :: tl -> let* tl = fold_right f tl acc in
        f hd tl

    let rec fold_left f acc = function
      | [] -> return acc
      | hd :: tl ->
        let* acc = f acc hd in
        fold_left f acc tl

    let rec for_all f = function
      | [] -> return true
      | hd :: tl ->
        let* c = f hd in
        if c then
          for_all f tl
        else
          return false
  end

  module Array = struct
    let for_all f a =
      let n = Array.length a in
      let rec aux i =
        if i = n then return true
        else
          let* c =  f a.(i) in
          if c then aux (i + 1)
          else return false
      in aux 0

    let map2 f a b =
      let n = Array.length a in
      if n <> Array.length b then
        raise (Invalid_argument "map2");
      
      if n = 0 then return [||]
      else
        let* c = f a.(0) b.(0) in
        let a' = Array.make n c in
        let rec aux i =
          if i = n then return ()
          else
            let* c = f a.(i) b.(i) in begin
              a'.(i) <- c;
              aux (i + 1)
            end
        in aux 1 >> return a'
  end
end

let get_data c ctx =
  List.assoc c ctx.data, ctx

let lookup_data c ctx =
  List.assoc_opt c ctx.data, ctx

let lookup_tid x ctx =
  List.assoc_opt x ctx.tid, ctx

let lookup_id x ctx =
  List.assoc_opt x ctx.id, ctx

let get_eff e ctx =
  List.assoc e ctx.effects, ctx

let lookup_eff e ctx =
  List.assoc_opt e ctx.effects, ctx

let lookup_op op ctx =
  List.find_map (fun (e, ({ eops; _ } as eff)) ->
      let v, l = Bindlib.unmbind eops in
      List.find_map (fun { op_name; op_in; op_out } ->
          if op_name = op then
            Some (e, eff,
                  Bindlib.(bind_mvar v
                             (op_ op_name (box_type op_in) (box_type op_out))
                           |> unbox))
          else None) l
    ) ctx.effects, ctx

let lookup_con con ctx =
  List.find_map (fun (c, { targs; cons }) ->
      List.find_map (fun (con', l) ->
          if con' = con then
            Some (c, targs, l)
          else None) cons
    ) ctx.data, ctx

let lookup_op_in_ectx op e ctx =
  let rec find_map_split f = function
    | [] -> None
    | hd :: tl ->
      match f hd with
      | None ->
        find_map_split f tl |>
        Option.map (fun (l, x, l') -> hd :: l, x, l')
      | Some x -> Some ([], x, tl)
  in
  let is_op_in_eff ({ eff_name; eff_args; _ } as eff) =
    let { eops; _ } = List.assoc eff_name ctx.effects in
    let eops = Bindlib.msubst eops eff_args in
    List.find_opt (fun { op_name; _ } -> op_name = op) eops
    |> Option.map (fun op -> op, eff)
  in
  find_map_split is_op_in_eff e, ctx

let add_binding b = fun ctx ->
  (), ctx <: b

let replace_bindings gamma = fun ctx ->
  (), { ctx with gamma }

let add_bindings gamma' = fun ({ gamma ; _} as ctx) ->
  (), { ctx with gamma = gamma' @ gamma }


let pop_binding () = fun ({ gamma ; _ } as ctx) ->
  List.hd gamma, { ctx with gamma = List.tl gamma }

let rec drop_marker = function
  | [] -> failwith "drop_marker: internal error"
  | Marker :: tl -> tl
  | _ :: tl -> drop_marker tl

let rec split_marker = function
  | [] -> failwith "split_marker: internal error"
  | Marker :: tl -> [], tl
  | hd :: tl -> let l, r = split_marker tl in
    hd :: l, r

let protect_context f = fun ctx ->
  let id = ctx.id in
  let tid = ctx.tid in
  let ctx = ctx <: Marker in
  let a, ctx = f ctx in
  a, { ctx with gamma = drop_marker ctx.gamma; id; tid }

let get_suffix f = fun ctx ->
  let id = ctx.id in
  let tid = ctx.tid in
  let ctx = ctx <: Marker in
  let a, ctx = f ctx in
  let suffix, gamma = split_marker ctx.gamma in
  (a, suffix), { ctx with gamma; id; tid }

let with_binding b f =
  protect_context @@ (add_binding b >> f)

let get_var_kind x ({gamma; _} as ctx) =
  let rec get_var_kind = function
  | [] -> failwith "get_var_kind: internal error"
  | BPFlex (y, _, k) :: _
  | BMFlex (y, _, k) :: _
  | BType (y, k) :: _ when Bindlib.eq_vars x y -> k
  | _ :: tl -> get_var_kind tl
  in get_var_kind gamma, ctx

let rec get_pflex_def_ x = function
  | [] -> failwith "get_pflex_def_: internal error"
  | BPFlex (y, p, _) :: _ when Bindlib.eq_vars x y -> p
  | _ :: tl -> get_pflex_def_ x tl

let get_pflex_def x ({gamma; _} as ctx) =
  get_pflex_def_ x gamma, ctx

let rec get_pflex_split_ x = function
  | [] -> failwith "get_pflex_split_: internal error"
  | BPFlex (y, p, k) :: tl when Bindlib.eq_vars x y -> [], (p, k), tl
  | hd :: tl ->
    let g, p, g' = get_pflex_split_ x tl in
    hd :: g, p, g'

let get_pflex_split x ({gamma; _} as ctx) =
  get_pflex_split_ x gamma, ctx

(* Section 4.4 *)

let rec get_kind ?(seen_adt=[]) = function
  | TMod (MAbs _, _) -> return Abs
  | TMod (MRel _, a) -> get_kind ~seen_adt a
  | TArr (_, _) -> return Any
  | Ghost -> return Any
  | PFlex v
  | MFlex v
  | TVar v -> get_var_kind v
  | UGhost p -> get_kind p
  | TForA (k, a) ->
    let v, a = Bindlib.unbind a in
    with_binding (BType (v, k)) @@
    get_kind ~seen_adt  a
  | TCon (c, _) when List.mem c seen_adt -> return Abs
  | TCon (c, arr) ->
    let seen_adt = c :: seen_adt in
    let* { cons; _ } = get_data c in
    let types = List.map (fun (_, b) -> Bindlib.msubst b arr) cons |>
      List.flatten in
    let* abs = M.List.for_all
        (fun a -> get_kind ~seen_adt a $> (=) Abs) types in
    if abs then return Abs
    else return Any
  | ECtx _ -> return Effect

let is_abs a =
  get_kind a $> (=) Abs

let is_type a =
  get_kind a $> (<>) Effect

let rec get_guarded = function
  | TMod (mu, t) -> let nu, g = get_guarded t in
    Effects.compose mu nu, g
  | g -> Effects.id, g

let across a nu f =
  let* c = is_abs a in
  if c then return (Some a)
  else
    let mu, g = get_guarded a in
    match Effects.right_residual nu mu f with
    | Some (MRel ([], [])) -> return @@ Some g
    | Some xi -> return @@ Some (TMod (xi, g))
    | _ -> return None

let rec locks e = function
  | [] -> Effects.id, e
  | Lock (m, e) :: tl ->
    let (m', f) = locks e tl in
    Effects.compose m' m, f
  | _ :: tl -> locks e tl

let get_type_context x ({gamma; _} as ctx) =
  let rec get_type_context gamma x = match gamma with
    | [] -> failwith "get_type_context: internal error"
    | BVar (y, a) :: gamma when Bindlib.eq_vars x y -> gamma, a, []
    | hd :: tl ->
      let gamma, a, gamma' = get_type_context tl x in
      gamma, a, hd :: gamma'
  in get_type_context gamma x, ctx

let fresh_tvar x k ({ gamma; tid; _ } as ctx) =
  let v = Bindlib.new_var (fun v -> TVar v) x in
  v, { ctx with gamma = BType (v, k) :: gamma; tid = (x, v) :: tid }

let fresh_var x a ({ gamma; id; _ } as ctx) =
  let v = Bindlib.new_var (fun v -> Var v) x in
  v, { ctx with gamma = BVar (v, a) :: gamma; id = (x, v) :: id }

let fresh_vars_ f args ctx =
  let vars, ctx =
    List.fold_right (fun x (vars, ctx) ->
        Pair.map_fst (fun v -> v :: vars) @@ f x ctx)
      args ([], ctx) in
  let mvar = Array.of_list vars in
  mvar, ctx

let fresh_mflex k ctx =
  incr counter;
  let v = Bindlib.new_var (fun v -> MFlex v) (Printf.sprintf "x%d" !counter) in
  v, ctx <: BMFlex (v, None, k)

let fresh_pflex k ctx =
  incr counter;
  let v = Bindlib.new_var (fun v -> PFlex v) (Printf.sprintf "x%d" !counter) in
  v, ctx <: BPFlex (v, Ghost, k)

let fresh_vars args ctx = fresh_vars_ (fun (x, t) -> fresh_var x t) args ctx

let fresh_tvars args ctx = fresh_vars_ (fun (x, k) -> fresh_tvar x k) args ctx

let fresh_pflexs kinds ctx = fresh_vars_ fresh_pflex kinds ctx

let fresh_mflexs kinds ctx = fresh_vars_ fresh_mflex kinds ctx
