open Ast

exception IllformedExpression 

let rec eval_arith ev op e1 e2 : value = 
      (match eval ev e1 with
        | VInt n1 -> 
          (match eval ev e2 with
            | VInt n2 -> 
              VInt (op n1 n2)
            | _ -> 
              raise IllformedExpression)
        | _ -> 
          raise IllformedExpression)

(* large-step evaluation function *)
and eval (ev:env) (e:exp) : value = 
  match e with 
    | Var x -> 
      (try VarMap.find x ev
       with Not_found -> raise IllformedExpression) 
    | Int n -> 
      VInt n
    | True -> 
      VBool true 
    | False -> 
      VBool false
    | Lam(x,e) ->
      VFun(ref ev,x,e)
    | App(e1,e2) ->       
      (match eval ev e1 with 
        | VFun(evf,x,ef) -> 
          eval (VarMap.add x (eval ev e2) !evf) ef
        | _ -> raise IllformedExpression)
    | Let(x,e1,e2) -> 
      eval (VarMap.add x (eval ev e1) ev) e2 
    | Plus(e1,e2) ->  
      eval_arith ev ( + ) e1 e2
    | Times(e1,e2) -> 
      eval_arith ev ( * ) e1 e2
    | Minus(e1,e2) -> 
      eval_arith ev ( - ) e1 e2
    | Eq(e1,e2) ->
      (match eval ev e1 with
        | VInt n1 -> 
          (match eval ev e2 with
            | VInt n2 -> 
              if n1 = n2 then VBool(true) else VBool(false)
            | _ -> 
              raise IllformedExpression)
        | _ -> 
          raise IllformedExpression)
    | Pair(e1,e2) -> 
      VPair (eval ev e1, eval ev e2)
    | Fst e -> 
      (match eval ev e with 
        | VPair(v1,v2) -> v1
        | _ -> raise IllformedExpression)
    | Snd e -> 
      (match eval ev e with 
        | VPair(v1,v2) -> v2
        | _ -> raise IllformedExpression)
    | If(e1,e2,e3) ->       
      (match eval ev e1 with
        | VBool(true) -> eval ev e2 
        | VBool(false) -> eval ev e3
        | _ -> raise IllformedExpression)
    | Letrec(f,x,e1,e2) -> 
      let evr = ref ev in 
      let v = VFun(evr,x,e1) in
      evr := VarMap.add f v !evr;
      eval !evr e2
