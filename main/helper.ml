open Ast

(* [typ_eq t1 t2] returns [true] iff [t1] and [t2] are equal *)  
let typ_eq (t1:typ) (t2:typ) : bool = 
  t1 = t2

(* ---------- SUBSTITUTIONS ----------- *)

(* [subst_typ t0 x t] replaces [TVar x] with [t] in [t0] *)
let rec subst_typ (t0:typ) (x:var) (t:typ) : typ =
  match t0 with
    | TInt ->
      t0
    | TBool ->
      t0
    | TVar y ->
      if x = y then t else t0
    | TPair(t1,t2) ->
      TPair(subst_typ t1 x t, subst_typ t2 x t)
    | TArrow(t1,t2) ->
      TArrow(subst_typ t1 x t, subst_typ t2 x t)

(* [apply_subst s t0] applies the substitution [s] to [t0] *)
let rec apply_subst (s:subst) (t0:typ) : typ =
  match t0 with
    | TInt ->
      t0
    | TBool ->
      t0
    | TVar y ->
      (try (apply_subst s (VarMap.find y s))
       with Not_found -> t0)
    | TPair(t1,t2) ->
      TPair(apply_subst s t1, apply_subst s t2)
    | TArrow(t1,t2) ->
      TArrow(apply_subst s t1, apply_subst s t2)

(* [subst_constr c0 x t] replaces [TVar x] with [t] in [c0] *)
let rec subst_constr (c0:constr) (x:var) (t:typ) : constr =
  Constr.fold
    (fun (t1,t2) -> Constr.add (subst_typ t1 x t, subst_typ t2 x t))
    c0 Constr.empty

(* [subst_pcontext g s] applies the substitution [s] to all types appearing in [g] *)
let subst_pcontext (g:pcontext) (s:subst) : pcontext =
  let subst_mapping v (vs,t) c = VarMap.add v (vs,(apply_subst s t)) c in
  VarMap.fold subst_mapping g VarMap.empty

(* ---------- FREE TYPE VARIABLES ---------- *)

(* [ftvs t0] calculates the set of free variables of [t0] *)
let rec ftvs (t0:typ) : varset =
  match t0 with
    | TInt ->
      VarSet.empty
    | TBool ->
      VarSet.empty
    | TVar y ->
      VarSet.singleton y
    | TPair(t1,t2) | TArrow(t1,t2) ->
      VarSet.union (ftvs t1) (ftvs t2)

(* [ftvs_context g] calcuates the set of free variables of [g] *)
let ftvs_context (g:context) : varset =
  VarMap.fold (fun _ t tvs -> VarSet.union (ftvs t) tvs) g VarSet.empty

(* [ftvs_pcontext g] calcuates the set of free variables of [g] *)
let ftvs_pcontext (g:pcontext) : varset =
  VarMap.fold (fun _ (_,t) tvs -> VarSet.union (ftvs t) tvs) g VarSet.empty

(* ---------- FRESH TYPE VARIABLES ---------- *)
let tvar_cell = ref 0

let tvar_name x =
  let c = Char.chr (x mod 26 + 97) in
  let n = x / 26 in
  let s = "'" ^ String.make 1 c in
  if n = 0 then s
  else s ^ "_" ^ string_of_int n

(* [next_tvar ()] generates a fresh type variable *)
let next_tvar () : typ =
  let x = !tvar_cell in
  incr tvar_cell;
  TVar (tvar_name x)
