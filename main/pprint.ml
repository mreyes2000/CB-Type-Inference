open Ast
open Format

let ident v = printf "%s" v
let printBop op p l r = printf "@[(%a@ %s@ %a)@]" p l op p r
let printLam p x e = printf "@[<2>(\\%s.@ %a)@]" x p e
let printApp p l r = printf "@[<2>(%a@ %a)@]" p l p r
let printIf p e c a = printf "@[<2>if@ %a@ then@ %a@ else@ %a@]" p e p c p a
let printLet p x e1 e2 = printf "@[let %s@ =@ %a@ in@ %a@]" x p e1 p e2
let printLetrec p f x e1 e2 = printf "@[let rec %s =@ \\%s@ . %a@ in@ %a@]" f x p e1 p e2

let rec printExp' ppf = function
  | Var v -> ident v
  | App (l,r) -> printApp printExp' l r
  | Lam (x,e) -> printLam printExp' x e
  | Let(x,e1,e2) -> printLet printExp' x e1 e2
  | Plus (l,r) -> printBop "+" printExp' l r
  | Times (l,r) -> printBop "*" printExp' l r
  | Minus (l,r) -> printBop "-" printExp' l r
  | Int n -> printf "%d" n
  | Pair(l,r) -> printBop "," printExp' l r
  | Fst e -> printf "@[#1 %a@]" printExp' e
  | Snd e -> printf "@[#2 %a@]" printExp' e
  | True -> ident "true"
  | False -> ident "false"
  | If (e,c,a) -> printIf printExp' e c a
  | Eq (l,r) -> printBop "=" printExp' l r
  | Letrec(f,x,e1,e2) -> printLetrec printExp' f x e1 e2

and printTyp' ppf = function
  | TInt -> printf "int"
  | TBool -> printf "bool"
  | TVar x -> printf "%s" x
  | TPair(t1,t2) -> printf "@[(%a * %a)@]" printTyp' t1 printTyp' t2
  | TArrow(t1,t2) -> printf "@[(%a -> %a)@]" printTyp' t1 printTyp' t2

and printTypSch' ppf (vs, t) =
  printf "forall. " ;
  VarSet.iter (fun x -> printf "%s " x) vs;
  printf "@[(%a)@]" printTyp' t

and printVal' ppf = function
  | VInt(n) -> printf "%d" n
  | VBool(b) -> printf "%b" b
  | VPair(v1,v2) -> printf "@[(%a, %a)@]" printVal' v1 printVal' v2
  | VFun(ev,x,e) -> printf "@[%sclosure%s@]" "<" ">"

let printExp e = 
  printExp' Format.std_formatter e

let printTyp t = 
  printTyp' Format.std_formatter t

let printTypSch ts = 
  printTypSch' Format.std_formatter ts

let printVal v = 
  printVal' Format.std_formatter v

