module List' = List

open Hflmc2_util
open Id
open Type

(* Notを追加したHFLzのsyntax sugar *)
module Sugar = struct
  type 'ty t =
    | Bool   of bool
    | Var    of 'ty Id.t
    | Or     of 'ty t * 'ty t
    | And    of 'ty t * 'ty t
    | Not    of 'ty t
    | Abs    of 'ty arg Id.t * 'ty t
    | Forall of 'ty arg Id.t * 'ty t
    | Exists of 'ty arg Id.t * 'ty t
    | App    of 'ty t * 'ty t
    | Arith  of Arith.t
    | LsExpr of Arith.lt
    | Pred of Formula.pred * Arith.t list * Arith.lt list
    [@@deriving eq,ord,show,iter,map,fold,sexp]

  type 'ty hes_rule =
    { var  : 'ty Id.t
    ; body : 'ty t
    ; fix  : Fixpoint.t
    }
    [@@deriving eq,ord,show,iter,map,fold,sexp]
  
  type 'ty hes = 'ty t * 'ty hes_rule list
    [@@deriving eq,ord,show,iter,map,fold,sexp]
    
  let mk_var x : 'a t = Var x
  let mk_abs x t = Abs(x, t)
  let mk_abss xs t = List.fold_right xs ~init:t ~f:mk_abs
  let decompose_abs =
    let rec go acc phi = match phi with
      | Abs(x, phi) -> go (x::acc) phi
      | _ -> (List.rev acc, phi)
    in fun phi -> go [] phi
end

type 'ty t =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty t * 'ty t
  | And    of 'ty t * 'ty t
  | Abs    of 'ty arg Id.t * 'ty t
  | Forall of 'ty arg Id.t * 'ty t
  | Exists of 'ty arg Id.t * 'ty t
  | App    of 'ty t * 'ty t
  | Arith  of Arith.t
  | LsExpr of Arith.lt
  | Pred of Formula.pred * Arith.t list * Arith.lt list
  [@@deriving eq,ord,show,iter,map,fold,sexp]
    
type 'ty hes_rule =
  { var  : 'ty Id.t
  ; body : 'ty t
  ; fix  : Fixpoint.t
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

type 'ty hes = 'ty t * 'ty hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* Construction *)
let mk_bool b = Bool b

let mk_ands = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:(fun a b -> And(a,b))

let mk_ors = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:(fun a b -> Or(a,b))

let mk_pred pred a1 a2 = Pred(pred, [a1;a2], [])

let mk_arith a = Arith a

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

(* Decomposition *)
let decompose_abs =
  let rec go acc phi = match phi with
    | Abs(x, phi) -> go (x::acc) phi
    | _ -> (List.rev acc, phi)
  in fun phi -> go [] phi

let decompose_app =
  let rec go phi acc = match phi with
    | App(phi,x) -> go phi (x::acc)
    | _ -> (phi, acc)
  in
  fun phi -> go phi []

let desugar_formula (formula : 'a Sugar.t) : 'a t = 
  let rec neg (f : 'a Sugar.t) : 'a t = match f with
    | Bool b -> Bool (not b)
    | Or  (f1, f2) -> And (neg f1, neg f2)
    | And (f1, f2) -> Or  (neg f1, neg f2)
    | Forall (x, f) -> Exists (x, neg f)
    | Exists (x, f) -> Forall (x, neg f)
    | Pred (p, arga, argl) -> Pred (Formula.negate_pred p, arga, argl)
    | Arith _-> failwith "(negate_subformula) cannot negate Arith"
    | LsExpr _-> failwith "(negate_subformula) cannot negate LsExpr"
    | Var _  -> failwith "(negate_subformula) cannot negate Var"
    | Abs _  -> failwith "(negate_subformula) cannot negate Abs"
    | App _  -> failwith "(negate_subformula) cannot negate App"
    | Not f  -> thr f
  and thr (f : 'a Sugar.t) : 'a t = match f with
    | Var x  -> Var x
    | Bool b -> Bool b
    | Or  (phi1, phi2) -> Or  (thr phi1, thr phi2)
    | And (phi1, phi2) -> And (thr phi1, thr phi2)
    | App (phi1, phi2) -> App (thr phi1, thr phi2)
    | Abs (x, phi1)    -> Abs (x, thr phi1)
    | Forall (x, phi1) -> Forall (x, thr phi1)
    | Exists (x, phi1) -> Exists (x, thr phi1)
    | Arith a          -> Arith a
    | LsExpr a        -> LsExpr a
    | Pred (x, as',ls') -> Pred (x, as', ls')
    | Not phi1         -> neg phi1 in
  thr formula
    
let desugar ((entry, rules) : 'a Sugar.hes) : 'a hes =
  desugar_formula entry,
  List.map ~f:(fun { var; body; fix } -> { var; fix; body = desugar_formula body }) rules
  
let rec fvs = function
  | Var x          -> IdSet.singleton x
  | Bool _         -> IdSet.empty
  | Or (phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | And(phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | App(phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | Abs(x,phi)     -> IdSet.remove (fvs phi) x
  | Forall (x,phi) -> IdSet.remove (fvs phi) x
  | Exists (x,phi) -> IdSet.remove (fvs phi) x
  | Arith a        -> IdSet.of_list @@ Arith.fvs_notype a
  | LsExpr a       -> IdSet.of_list @@ Arith.lfvs_notype a
  | Pred(_,as',ls')  ->
    let fvs1 = List.concat @@ List.map as' ~f:Arith.fvs_notype in
    let fvs2 = List.concat @@ List.map ls' ~f:Arith.lfvs_notype in
    IdSet.of_list @@ List.append fvs1 fvs2


let fvs_with_type : 'ty t -> 'ty Type.arg Id.t list = fun hes ->
  let rec go = function
    | Var x          -> [{ x with ty = Type.TySigma x.ty}]
    | Bool _         -> []
    | Or (phi1,phi2) -> (go phi1) @ (go phi2)
    | And(phi1,phi2) -> (go phi1) @ (go phi2)
    | App(phi1,phi2) -> (go phi1) @ (go phi2)
    | Abs(x, phi)    -> List'.filter (fun t -> not @@ Id.eq t x) @@ go phi(* listだと、ここが毎回線形時間になる... *)
    | Forall(x, phi) -> List'.filter (fun t -> not @@ Id.eq t x) @@ go phi
    | Exists(x, phi) -> List'.filter (fun t -> not @@ Id.eq t x) @@ go phi
    | Arith a        -> 
      let (afvs, lfvs) = Arith.fvs a in
      let afvs = List'.map (fun id -> {id with Id.ty = Type.TyInt}) afvs in
      let lfvs = List'.map (fun id -> {id with Id.ty = Type.TyList}) lfvs in
      afvs @ lfvs
    | LsExpr l       ->
      let (afvs, lfvs) = Arith.lfvs l in
      let afvs = List'.map (fun id -> {id with Id.ty = Type.TyInt}) afvs in
      let lfvs = List'.map (fun id -> {id with Id.ty = Type.TyList}) lfvs in
      afvs @ lfvs
    | Pred (_, as', ls')-> 
      let (fvsa1, fvsl1) = as' |> List'.map (fun a -> Arith.fvs a) |> List.unzip in
      let (fvsa2, fvsl2) = ls' |> List'.map (fun a -> Arith.lfvs a) |> List.unzip in
      let (fvsa, fvsl) = (List'.flatten (fvsa1 @ fvsa2), List'.flatten (fvsl1 @ fvsl2)) in
      let fvsa = fvsa |> List'.map (fun id -> {id with Id.ty = Type.TyInt}) in
      let fvsl = fvsl |> List'.map (fun id -> {id with Id.ty = Type.TyList}) in
      fvsa @ fvsl in 
  go hes |> Hflmc2_util.remove_duplicates (fun e x -> Id.eq e x) |> List.sort ~compare:(fun a b -> Int.compare a.id b.id)

exception CannotNegate
(* 全体を一度にnegateすると単純なやり方でよい。 *)
let is_negation_of f1 f2 =
  let rec neg (f : 'a t) : 'a t = match f with
    | Bool b -> Bool (not b)
    | Or  (f1, f2) -> And (neg f1, neg f2)
    | And (f1, f2) -> Or  (neg f1, neg f2)
    | Forall (x, f) -> Exists (x, neg f)
    | Exists (x, f) -> Forall (x, neg f)
    | Pred (p, arga, argl) -> Pred (Formula.negate_pred p, arga, argl)
    | Arith _ | LsExpr _ | Var _ | Abs _ | App _ -> raise CannotNegate in
  try
    neg f1 = f2
  with CannotNegate -> false

let negate_formula (formula : Type.simple_ty t) =
  let rec go formula = match formula with
    | Bool b -> Bool (not b)
    | Var x  -> Var x
    | And (Or (f1, f2), Or(f3, f4)) when is_negation_of f1 f3 ->
      (* ifのとき *)
      (* !((p \/ q) /\ (!p \/ r))  =  (!p /\ !q) \/ (p /\ !r)  =
         (!p => !q) /\ (p => !r)  =  ((p \/ !q) /\ (!p \/ !r)) *)
      (* print_endline "NEGATE IF!!!"; *)
      And (Or (f1, go f2), Or(f3, go f4))
    | Or  (f1, f2) -> And (go f1, go f2)
    | And (f1, f2) -> Or  (go f1, go f2)
    | Abs (x, f1)  -> Abs (x, go f1)
    | App (f1, f2) -> App (go f1, go f2)
    | Forall (x, f) -> Exists (x, go f)
    | Exists (x, f) -> Forall (x, go f)
    | Arith (arith) -> Arith (arith)
    | LsExpr (ls)  -> LsExpr (ls)
    | Pred (p, arga, argl) -> Pred (Formula.negate_pred p, arga, argl) in
  go formula

let negate_rule ({var; body; fix} : Type.simple_ty hes_rule) = 
  {var; body=negate_formula body; fix=Fixpoint.flip_fixpoint fix}

let id_n n t = { Id.name = "x_" ^ string_of_int n; id = n; ty = t }


let dummy_entry_name = "MAIN__"
let mk_entry_rule body = {var=Id.gen ~name:dummy_entry_name (Type.TyBool ()); fix=Fixpoint.Greatest; body=body }
let merge_entry_rule (entry, rules) = (mk_entry_rule entry) :: rules
let decompose_entry_rule rules = match rules |> Stdlib.List.partition (fun r -> r.var.name = dummy_entry_name) with
  | [e], rules -> e.body, rules
  | _ -> failwith "decompose_entry_rule"


let ensure_no_mu_exists (hes : 'a hes) =
  let rec no_exists = function
    | Bool _ -> true
    | Var _  -> true
    | Or (f1, f2)  -> no_exists f1 && no_exists f2
    | And (f1, f2) -> no_exists f1 && no_exists f2
    | Abs (_, f1)  -> no_exists f1
    | Forall (_, f1) -> no_exists f1
    | Exists _ -> false
    | App (f1, f2) -> no_exists f1 && no_exists f2
    | Arith _ -> true
    | LsExpr _ -> true
    | Pred _ -> true in
  List.for_all ~f:(fun {body; fix; _} -> fix = Fixpoint.Greatest && no_exists body) ((mk_entry_rule (fst hes))::(snd hes))
  