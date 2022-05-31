(* variables *)
type var = string

(* maps with variables as keys *)
module VarMap = Map.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* maps with variables as keys *)
module VarSet = Set.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* locations *)
type loc = int

(* types *)
type typ = 
    TInt                             (* int *)
  | TBool                            (* bool *)
  | TVar of var                      (* X *)
  | TPair of typ * typ               (* t1 * t2 *)
  | TArrow of typ * typ              (* t1 -> t2 *)

(* expressions *)
type exp =
    Var of var                      (* x *)
  | App of exp * exp                (* e1 e2 *)
  | Lam of var * exp                (* lambda x : t . e *)
  | Let of var * exp * exp          (* let x = e1 in e2 *)
  | Int of int                      (* n *)
  | Plus of exp * exp               (* e1 + e2 *)
  | Times of exp * exp              (* e1 * e2 *)
  | Minus of exp * exp              (* e1 - e2 *)
  | Pair of exp * exp               (* e1,e2 *)
  | Fst of exp                      (* #1 e *)
  | Snd of exp                      (* #2 e *)
  | True                            (* true *)
  | False                           (* false *)
  | Eq of exp * exp                 (* e1 = e2 *) 
  | If of exp * exp * exp           (* if e1 then e2 else e3 *)
  | Letrec of var * var * exp * exp (* let rec f = lambda x : t. e1 in e2 *)

(* values *)
type value = 
    VInt of int
  | VBool of bool
  | VPair of value * value
  | VFun of (value VarMap.t) ref * var * exp 

(* sets of pairs of types *)
module Constr = Set.Make(struct
  type t = typ * typ
  let compare = Pervasives.compare
end)

(* evaluation environments *)
type env = value VarMap.t

(* constraints *)
type constr = Constr.t

(* sets of type variables *)
type varset = VarSet.t

(* type substitutions *)
type subst = typ VarMap.t

(* type scheme - this is a pair of a set of generalized type variables and a type *)
type typ_scheme = varset * typ

(* typechecking environments - maps variables to types *)
type context = typ VarMap.t

(* typechecking environments - for let-polymorphism, contexts map variables to type schemes *)
type pcontext = typ_scheme VarMap.t
