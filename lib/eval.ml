open Syntax
open Effect
open Effect.Deep

module SMap = Map.Make(String)

type value
  = VClo of (value -> value)
  | VInt of int
  | VStr of string
  | VCon of string * value list
[@@deriving show]

type _ Effect.t += Do : string * value -> value t

let unint = function
  | VInt n -> n
  | _ -> failwith "internal error"

let unstr = function
  | VStr s -> s
  | _ -> failwith "internal error"

let vbool = function
  | true -> VCon ("True", [])
  | false -> VCon ("False", [])

let unbool = (=) (VCon ("True", []))

exception Fail

let stdlib =
  SMap.of_list
  [ "+", VClo (fun x -> VClo (fun y -> VInt (unint x + unint y)))
  ; "-", VClo (fun x -> VClo (fun y -> VInt (unint x - unint y)))
  ; "*", VClo (fun x -> VClo (fun y -> VInt (unint x - unint y)))
  ; "=", VClo (fun x -> VClo (fun y -> vbool (unint x = unint y)))
  ; "string_eq", VClo (fun x -> VClo (fun y -> vbool (unstr x = unstr y)))
  ; "^", VClo (fun x -> VClo (fun y -> VStr (unstr x ^ unstr y)))
  ; "&&", VClo (fun x -> VClo (fun y -> vbool (unbool x && unbool y)))
  ; "fail", VClo (fun _ -> raise Fail)
  ; "print", VClo (fun x -> print_endline (unstr x); VCon ("Unit", []))
  ]

let rec eval ctx env {sexpr; _} = match sexpr with
  | SInt n -> VInt n
  | SStr s -> VStr s
  | SCons (c, l) -> VCon (c, List.map (eval ctx env) l)
  | SVar x ->
    begin match List.assoc_opt x env with
      | Some v -> v
      | None -> SMap.find x !ctx
    end
  | SLam (x, m) -> VClo (fun v -> eval ctx ((x, v) :: env) m)
  | SApp (m, n) ->
    begin match eval ctx env m with
      | VClo f -> f (eval ctx env n)
      | _ -> failwith "internal error"
    end
  | SAppT (m, _)
  | SAnn (m, _) -> eval ctx env m
  | SSeq (m, n) -> let _ = eval ctx env m in eval ctx env n
  | SDo (e, m) -> perform (Do (e, eval ctx env m))
  | SMask _ -> failwith "todo"
  | SLet (x, m, n) -> eval ctx ((x, eval ctx env m) :: env) n
  | SMatch (m, l) ->
    let v = eval ctx env m in
      begin match List.find_map (fun (p, n) -> Option.map (fun env -> env, n)
                                    (eval_pat env v p)) l with
      | None -> failwith "missing case"
      | Some (env, n) -> eval ctx env n
    end
  | SHand (m, _, (h, (r, n))) ->
    try
      let v = eval ctx env m in
      eval ctx ((r, v) :: env) n
    with
    | effect (Do (e, v)), k ->
      match List.assoc_opt e h with
      | None -> continue k (perform (Do (e, v)))
      | Some (_, pi, ri, ni) ->
        eval ctx ((pi, v) :: (ri, VClo (continue k)) :: env) ni

and eval_pat env v {spat; _} = match spat with
  | SPWild -> Some env
  | SPVar x -> Some ((x, v) :: env)
  | SPCons (c, l) ->
    match v with
    | VCon (c', l') when c = c' ->
      List.fold_left
        (function
          | None -> fun _ -> None
          | Some env -> fun (p, v) -> eval_pat env v p)
        (Some env) (List.combine l l')
    | _ -> None

let eval_prog p =
  let ctx = ref stdlib in
  let first _ x y = match x with None -> y | _ -> x in
  ctx := SMap.(merge first (of_list (List.map (Pair.map_snd (eval ctx [])) p)) stdlib);
  match SMap.find "main" !ctx with
  | VClo f -> ignore (f (VCon ("Unit", []))); !ctx
  | _ -> failwith "main should be a function"
