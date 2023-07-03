open Hflmc2_util

type op =
  | Add
  | Sub
  | Mult
  | Div
  | Mod
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type opl =
  | Nil
  | Cons
  | Tail
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* List -> Int *)
type size =
  | Length
  | Head
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* arithmetic expresion parametrized by variable type *)
type ('avar, 'lvar) gen_t =
  | Int of int
  | Var of 'avar
  | Op  of op * ('avar, 'lvar) gen_t list
  | Size of size * ('avar, 'lvar) gen_lt
  [@@deriving eq,ord,show,iter,map,fold,sexp]
and ('avar, 'lvar) gen_lt =
  | Opl of opl * ('avar, 'lvar) gen_t list * ('avar, 'lvar) gen_lt list
  | LVar of 'lvar
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t = ([`Int] Id.t, [`List] Id.t) gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type lt = ([`Int] Id.t, [`List] Id.t) gen_lt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n     = Int(n)
let mk_nil       = Opl(Nil, [], [])
let mk_cons hd tl  = Opl(Cons, [hd], [tl])
let mk_tail ls  = Opl(Tail, [], [ls])
let mk_op op as' = Op(op,as')
let mk_var' v    = Var v
(* specific to [t] *)
let mk_var v : t = Var({v with ty = `Int})
let mk_lvar v : lt = LVar({v with ty = `List})


let rec fold_two_lists = function
  | [] -> ([],[])
  | (a1, a2)::xs ->
  let (b1, b2) = fold_two_lists xs in
  (List.append a1 b1, List.append a2 b2)

let rec fvs : ('avar, 'lvar) gen_t -> 'avar list * 'lvar list = function
  | Int _ -> [], []
  | Var v -> [v], []
  | Op (_, as') -> 
    let v = List.map as' ~f:fvs in
    fold_two_lists v
  | Size (_, ls) -> lfvs ls
and lfvs : ('avar, 'lvar) gen_lt -> 'avar list * 'lvar list = function
  | Opl (_, as', ls') -> 
    let fvs1 = List.map ~f:fvs as' in
    let fvs2 = List.map ~f:lfvs ls' in
    let fvs = fvs1 @ fvs2 in
    fold_two_lists fvs
  | LVar v -> [], [v]

let fvs_of_ariths as' = 
  let v = List.map as' ~f:fvs in
    fold_two_lists v

let fvs_of_lists as' = 
  let v = List.map as' ~f:lfvs in
    fold_two_lists v

let fvs_notype t = 
  let (vs1, vs2) = fvs t in
  let (vs1, vs2) = (List.map ~f:Id.remove_ty vs1, List.map ~f:Id.remove_ty vs2) in
  List.append vs1 vs2

let lfvs_notype t = 
  let (vs1, vs2) = lfvs t in
  let (vs1, vs2) = (List.map ~f:Id.remove_ty vs1, List.map ~f:Id.remove_ty vs2) in
  List.append vs1 vs2

let lift f x y = match (x, y) with
  | Some(x), Some(y) -> Some(f x y)
  | _ -> None

let op_func = function 
  | Add -> (+)
  | Sub -> (-)
  | Mult -> ( * )
  | Div -> (/)
  | Mod -> (mod)

let rec evaluate_opt x = match x with
  | Op(op, x::xs) -> 
  List.fold ~init:(evaluate_opt x) ~f:(lift @@ op_func op) (List.map ~f:evaluate_opt xs)
  | Var _ -> None
  | Int(x) -> Some(x)
  | _ -> failwith "evaluation error"


type t' = 
  | Int' of int
  | Var' of [`Int] Id.t
  | Op'  of [`Addit | `Mult | `Div | `Mod] * (t' * [`Add | `Sub]) list

let serial psi =
  let negate (e, p) = (e, match p with | `Add -> `Sub | `Sub -> `Add) in
  let negate_except_first e = match e with x::xs -> x::(List.map ~f:negate xs) | _ -> failwith "negate_except_first" in
  let rec go_addit p = match p with
    | Op (Add, xs) ->
      List.map ~f:go_addit xs |> List.concat
    | Op (Sub, [x1; x2]) ->
      (go_addit x1) @ (go_addit x2 |> List.map ~f:negate)
    | Op (_, _) -> [go p, `Add]
    | Var v -> [(Var' v, `Add)]
    | Int i            -> [(Int' i, `Add)]
  and go p = match p with
    | Op (Add, _) -> Op' (`Addit, go_addit p)
    | Op (Sub, _) -> Op' (`Addit, go_addit p |> negate_except_first)
    | Op (Mult, xs) -> Op' (`Mult, List.map ~f:go xs |> List.map ~f:(fun e -> (e, `Add)))
    | Op (Div, xs) -> Op' (`Div, List.map ~f:go xs |> List.map ~f:(fun e -> (e, `Add)))
    | Op (Mod, xs) -> Op' (`Mod, List.map ~f:go xs |> List.map ~f:(fun e -> (e, `Add)))
    | Var v -> Var' v
    | Int i -> Int' i in
  go psi
    

let evaluate xs =
  List.fold xs ~init:0 ~f:(fun acc (e, p) ->
    match e with
    | Int' i -> begin
      match p with
      | `Add -> acc + i
      | `Sub -> acc - i
    end
    | _ -> failwith "evaluate"
    )
  
  (* TODO: 動いていないので修正 *)
let rec calc psi = match psi with
  | Op' (`Addit, xs) ->
    let xs = List.map ~f:(fun (e, p) -> (calc e, p)) xs in
    let consts, terms = List.partition_tf xs ~f:(fun (x, _) -> match x with | (Int' _) -> true | _ -> false) in
    Op' (`Addit, terms @ [(Int' (evaluate consts), `Add)])
  | Op' (op, xs) -> Op' (op, List.map ~f:(fun (e, p) -> (calc e, p)) xs)
  | Var' _| Int' _ -> psi
    
let rec modoshi phi = match phi with
  | Op' (`Addit, x::xs) -> begin
    let (e, p) = x in
    let e = modoshi e in
    let e = 
      if p = `Sub then
        Op (Sub, [Int 0; e])
      else e in
    List.fold ~init:e ~f:(fun acc (e, p) ->
      let op = if p = `Sub then Sub else Add in
      Op (op, [acc; modoshi e])
    ) xs
  end
  | Op' (op, [(x1, _); (x2, _)]) -> begin
    let op =
      match op with
      | `Mult -> Mult
      | `Div -> Div
      | `Mod -> Mod
      | _ -> assert false in
    Op (op, [modoshi x1; modoshi x2])
  end
  | Op' _ -> failwith "modoshi"
  | Var' x -> Var x
  | Int' x -> Int x

let do_all phi = 
  let phi' = serial phi in
  let phi' = calc phi' in
  let phi' = modoshi phi' in
  phi'

let rec simple_partial_evaluate_ psi = match psi with
  | Op (op, xs) -> begin
    match List.map ~f:simple_partial_evaluate_ xs with
    | [Int i; Int j] ->  Int (op_func op i j)
    | _ -> psi
  end
  | Var x -> Var x
  | Int x -> Int x
  | Size (size, l) -> Size (size, l)

let simple_partial_evaluate psi =
  simple_partial_evaluate_ psi
  