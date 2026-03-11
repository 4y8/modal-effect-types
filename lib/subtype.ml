open Syntax

exception Mismatch of pure_type * pure_type
exception Occurs of tvar * pure_type

let (@:) = Context.apply

let (^:) = TT.app_

let fresh_var name =
  Bindlib.new_var (fun v -> TT.Var v) name

let fresh_flex name =
  Bindlib.new_var (fun v -> TFlex v) name

let id a =
  let x = fresh_var "x" in
  TT.(lam_ a Bindlib.(bind_var x (var_ x)))

let rec is_mono = function
  | TVar _
  | TFlex _ -> true
  | TArr (a, b) -> is_mono a && is_mono b
  | TCon (_, a) -> Array.for_all is_mono a
  | TMod _
  | TForA _ -> false

let rec is_wf a gamma = match a with
  | TVar v ->
    List.exists (function Context.BType (v', _) -> Bindlib.eq_vars v' v
                        | _ -> false) gamma
  | TFlex v ->
    List.exists (function Context.BFlex (v', _, _) -> Bindlib.eq_vars v' v
                        | _ -> false) gamma
  | TArr (a, b) -> is_wf a gamma && is_wf b gamma
  | TCon (_, a) -> Array.for_all (Fun.flip is_wf gamma) a
  | TForA (k, b) ->
    let v, a = Bindlib.unbind b in
    is_wf a (Context.BType (v, k) :: gamma)
  | TMod (mu, a) ->
    let eff_wf {eff_type = (a, b); _} =
      is_wf a gamma && is_wf b gamma
    in
    let mod_wf = function
      | MAbs e -> List.for_all eff_wf e
      | MRel (_, d) -> List.for_all eff_wf d
    in
    mod_wf mu && is_wf a gamma

let articulate alpha gamma =
  let gamma, k, gamma' = Context.split_flex alpha gamma in
  if k <> Any then
      Errors.no_apply_abs None alpha;
  let alpha1 = fresh_flex "alpha_1" in
  let alpha2 = fresh_flex "alpha_2" in
  let tau = TArr (TFlex alpha1, TFlex alpha2) in
  alpha1, alpha2,
  gamma @ Context.(BFlex (alpha1, Any, None) :: BFlex (alpha2, Any, None) ::
                   BFlex (alpha, Any, Some tau) :: gamma')

let rec instanciateR a alpha gamma = match a with
  | TFlex beta when Context.(alpha << beta) gamma->
    id (tflex_ alpha), Context.def_flex beta (TFlex alpha) gamma
  | tau when is_mono tau ->
    let gamma, k, gamma' = Context.split_flex alpha gamma in
    id (box_type tau), gamma @ (Context.BFlex (alpha, k, Some tau) :: gamma')
  | TArr (a, b) as a' ->
    let alpha1, alpha2, gamma = articulate alpha gamma in
    let m, theta = instanciateL alpha1 a gamma in
    let n, delta = instanciateR b alpha2 theta in
    let f = fresh_var "f" in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (box_type a') @@ bind_var f @@ lam_ (tflex_ alpha1) @@
        bind_var x (n ^: (var_ f ^: (m ^: var_ x))))),
    delta
  | TForA (k, b) as b' ->
    let beta = fresh_flex "beta" in
    let b = Bindlib.subst b (TFlex beta) in
    let m, delta = instanciateR b alpha
        Context.(BFlex (beta, k, None) :: Marker beta :: gamma) in
    let tau = Context.dummy_subst (TFlex beta) beta delta |> box_type in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (box_type b') @@ bind_var x @@ m ^: tapp_ (var_ x) tau)),
    Context.drop_marker beta delta

  | _ -> failwith "todo"

and instanciateL alpha a gamma = match a with
  | TFlex beta when Context.(alpha << beta) gamma->
    id (tflex_ alpha), Context.def_flex beta (TFlex alpha) gamma
  | tau when is_mono tau ->
    let gamma, k, gamma' = Context.split_flex alpha gamma in
    id (box_type tau), gamma @ (Context.BFlex (alpha, k, Some tau) :: gamma')
  | TArr (a, b) ->
    let alpha1, alpha2, gamma = articulate alpha gamma in
    let tau = TArr (TFlex alpha1, TFlex alpha2) in
    let m, theta = instanciateR a alpha1 gamma in
    let n, delta = instanciateL alpha2 b theta in
    let f = fresh_var "f" in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (box_type tau) @@ bind_var f @@ lam_ (box_type a) @@
        bind_var x (n ^: (var_ f ^: (m ^: var_ x))))),
    delta
  | TForA (k, b) ->
    let beta, b = Bindlib.unbind b in
    let m, delta = instanciateL alpha b Context.(BType (beta, k) :: gamma) in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (tflex_ alpha) @@ bind_var x @@ tlam_ k @@
        bind_var beta (m ^: var_ x))),
    Context.drop_type beta delta

  | _ -> failwith "todo"

let rec check_ a b gamma = match a, b with
  | TFlex v, TFlex v'
  | TVar v, TVar v' when Bindlib.eq_vars v v' ->
    id (box_type a), gamma
  | TCon (s, arr), TCon (s', arr') when s = s' ->
    let n = Array.length arr in
    let rec loop i gamma =
      if i = n then gamma
      else
        let _, theta = check_ (Context.apply gamma arr.(i))
            (Context.apply gamma arr'.(i)) gamma in
        let _, delta = check_ (Context.apply theta arr'.(i))
            (Context.apply theta arr.(i)) theta in
        loop (i + 1) delta
    in
    id (box_type a), loop 0 gamma

  | TArr (a, b), TArr (a', b') ->
    let m, theta = check_ a' a gamma in
    let n, delta = check_ (theta @: b) (theta @: b') theta in
    let f = fresh_var "f" in
    let x = fresh_var "x" in
    let t = box_type (TArr (a, b)) in
    TT.(Bindlib.(
        lam_ t @@ bind_var f @@ lam_ (box_type b') @@
        bind_var x (n ^: (var_ f ^: (m ^: var_ x))))),
    delta

  | TForA (k, a) as a', b ->
    let alpha = fresh_flex "alpha" in
    let a = Bindlib.subst a (TFlex alpha) in
    let m, theta = check_ a b
        (BFlex (alpha, k, None) :: Marker alpha :: gamma) in
    let tau = Context.dummy_subst (TFlex alpha) alpha theta |> box_type in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (box_type a') (bind_var x @@ m ^: (tapp_ (var_ x) tau)))),
    Context.drop_marker alpha theta

  | a, TForA (k, b) ->
    let alpha, b = Bindlib.unbind b in
    let m, theta = check_ a b (BType (alpha, k) :: gamma) in
    let x = fresh_var "x" in
    TT.(Bindlib.(
        lam_ (box_type a) @@ bind_var x @@ tlam_ k @@
        bind_var alpha (m ^: var_ x))),
    Context.drop_type alpha theta

  | TFlex alpha, a ->
    if Bindlib.occur alpha (box_type a) then
      failwith "occurs check_ failed";
    instanciateL alpha a gamma


  | a, TFlex alpha ->
    if Bindlib.occur alpha (box_type a) then
      failwith "occurs check_ failed";
    instanciateR a alpha gamma

  | a, b ->
    let mu, g = Context.get_guarded a in
    let nu, g' = Context.get_guarded b in
    if a != g && b != g' && Effects.eq_mod mu nu then
      let x = fresh_var "x" in
      let x' = fresh_var "x" in
      let y = fresh_var "y" in
      let mu_ = box_mod mu in
      let m, delta = check_ g g' gamma in
      TT.(Bindlib.(
          lam_ (box_type a) @@ bind_var x @@
          letmod_ (box_mod Effects.id) mu_ (var_ x) @@ bind_var x' @@
          lam_ (box_type g') (bind_var y @@ mod_ mu_ (var_ y)) ^:
          m ^: var_ x')), delta
    else
      raise (Mismatch (a, b))

let check a b gamma =
  let m, delta = check_ a b gamma in
  Bindlib.unbox m, delta
