open Ast
open Helper

exception TypeError 
exception UnificationError
exception UnimplementedError

(* [unify c0] solves [c0] (if possible), yielding a substitution. Raise UnificationError if constraints cannot be unified. *)
let rec unify (c0:constr) : subst = 
  (* FILL IN HERE FOR QUESTION 4 *)
  if c0 = Constr.empty then VarMap.empty
  else (
    let t, t_ = Constr.min_elt c0 in
    let c = Constr.remove (t, t_) c0 in
    if t = t_ then unify c
    else (
      match t with
      | TVar v -> if not (VarSet.mem v (Helper.ftvs t_))
                  then (
                    let sigma = VarMap.singleton v t_ in 
                    VarMap.map (Helper.apply_subst sigma) (VarMap.add v (TVar v) (unify (Helper.subst_constr c v t_)))  
                  )
                  else (
                    match t_ with
                    | TVar v -> if not (VarSet.mem v (Helper.ftvs t)) 
                                then (
                                  let sigma = VarMap.singleton v t in
                                  VarMap.map (Helper.apply_subst sigma) (VarMap.add v (TVar v) (unify (Helper.subst_constr c v t)))
                                )
                                else (
                                  match t, t_ with
                                  | TArrow (t0, t1), TArrow (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                                  | TPair (t0, t1), TPair (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                                  | _ -> raise UnificationError
                                )
                    | _ -> (
                            match t, t_ with
                            | TArrow (t0, t1), TArrow (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                            | TPair (t0, t1), TPair (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                            | _ -> raise UnificationError
                           )
                  )
      | _ -> (
              match t_ with
              | TVar v ->  if not (VarSet.mem v (Helper.ftvs t)) 
                          then (
                            let sigma = VarMap.singleton v t in
                            VarMap.map (Helper.apply_subst sigma) (VarMap.add v (TVar v) (unify (Helper.subst_constr c v t)))
                          )
                          else (
                            match t, t_ with
                            | TArrow (t0, t1), TArrow (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                            | TPair (t0, t1), TPair (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                            | _ -> raise UnificationError
                          )
              | _ -> (
                      match t, t_ with
                      | TArrow (t0, t1), TArrow (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                      | TPair (t0, t1), TPair (t0_, t1_) -> unify (Constr.add (t0, t0_) (Constr.add (t1, t1_) c))
                      | _ -> raise UnificationError
                     )
             )
    )
  )

  

(* [check g e0] typechecks [e0] in the context [g] generating a type and a set of constraints. Raise TypeError if constraints cannot be generated. *)
let rec check (g:context) (e0:exp) : typ * constr = 
  match e0 with
    (* FILL IN HERE FOR QUESTION 4 *)
    | Var v -> if VarMap.mem v g then (VarMap.find v g, Constr.empty) else raise TypeError
    | App (e1, e2) -> (let x = Helper.next_tvar () in
                       match (check g e1, check g e2) with 
                       | (t1, c1), (t2, c2) -> (x, Constr.add (t1, TArrow (t2, x)) (Constr.union c1 c2)))
    | Lam (v, e) -> (let t1 = Helper.next_tvar () in
                     match check (VarMap.add v t1 g) e with
                     | t2, c -> (TArrow (t1, t2), c))
    | Let (v, e1, e2) -> (match check g e1 with 
                          | (t1, c1) -> (
                                          match check (VarMap.add v t1 g) e2 with 
                                          | (t2, c2) -> (t2, Constr.union c1 c2)
                                        )
                         )
    | Int n -> (TInt, Constr.empty)
    | Plus (e1, e2) -> (match (check g e1, check g e2) with 
                        | (t1, c1), (t2, c2) -> (TInt, Constr.add (t1, TInt) (Constr.add (t2, TInt) (Constr.union c1 c2))))
    | Times (e1, e2) -> (match (check g e1, check g e2) with 
                        | (t1, c1), (t2, c2) -> (TInt, Constr.add (t1, TInt) (Constr.add (t2, TInt) (Constr.union c1 c2))))
    | Minus (e1, e2) -> (match (check g e1, check g e2) with 
                        | (t1, c1), (t2, c2) -> (TInt, Constr.add (t1, TInt) (Constr.add (t2, TInt) (Constr.union c1 c2))))
    | Pair (e1, e2) -> (match (check g e1, check g e2) with 
                        | (t1, c1), (t2, c2) -> (TPair (t1, t2), Constr.union c1 c2))
    | Fst e -> (let x = Helper.next_tvar () in
                let y = Helper.next_tvar () in
                match check g e with
                | t, c -> (x, Constr.add (t, TPair(x,y)) c))
    | Snd e -> (let x = Helper.next_tvar () in
                let y = Helper.next_tvar () in
                match check g e with
                | t, c -> (y, Constr.add (t, TPair(x,y)) c))
    | True -> (TBool, Constr.empty)
    | False -> (TBool, Constr.empty)
    | Eq (e1, e2) -> (match (check g e1, check g e2) with 
                      | (t1, c1), (t2, c2) -> (TBool, Constr.add (t1, TInt) (Constr.add (t2, TInt) (Constr.union c1 c2))))
    | If (e1, e2, e3) -> (let x = Helper.next_tvar () in
                          match (check g e1, check g e2, check g e3) with 
                          | (t1, c1), (t2, c2), (t3, c3) -> (x, Constr.add (t3, x) (Constr.add (t2, x) (Constr.add (t1, TBool) (Constr.union (Constr.union c1 c2) c3)))))
    | Letrec (f, v, e1, e2) -> (  
                                let x = Helper.next_tvar () in 
                                let y = Helper.next_tvar () in
                                match (check (VarMap.add v x (VarMap.add f (TArrow (x, y)) g)) e1, check (VarMap.add f (TArrow (x, y)) g) e2) with 
                                | (t1, c1), (t2, c2) -> (t2, Constr.add (t1, y) (Constr.union c1 c2))
                               )
