open Ast
open Helper

exception TypeError 
exception UnificationError
exception UnimplementedError

(* [unify c0] solves [c0] (if possible), yielding a substitution. Raise UnificationError if constraints cannot be unified. *)
let rec unify (c0:constr) : subst =
  (* we will just use your solution from Question 4. No need to implement it again! *)
  Check.unify c0 

(* [quantify g t] takes a context [g] and a type [t] and finds all type variables in [t] that are also not used in [g] and forms a type scheme from these type variables and [t] *)
let quantify (g:pcontext) (t:typ) : typ_scheme = 
  (* FILL IN HERE FOR BONUS QUESTION *)
  raise UnimplementedError

(* [instantiate s] takes a type scheme, generates fresh type variables for any quantified type variables in [s], and returns a new type with those fresh variables substituted for the quantified ones *)
let instantiate (s:typ_scheme) : typ = 
  (* FILL IN HERE FOR BONUS QUESTION *)
  raise UnimplementedError

(* [check g e0] typechecks [e0] in the context [g] generating a type and a set of constraints. Raise TypeError if constraints cannot be generated. *)
let rec check (g:pcontext) (e0:exp) : typ * constr = 
  match e0 with
    (* FILL IN HERE FOR BONUS QUESTION *)
    | _ -> raise UnimplementedError
