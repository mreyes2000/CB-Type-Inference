open Ast

let () =
  let usage_exit () = (Format.printf "Usage: lam [-letpoly] <file>\n"; exit 0) in
  let _ =
    if (Array.length Sys.argv < 2) || (Array.length Sys.argv > 4) then
      usage_exit()
    else if Sys.argv.(1).[0] = '-' && Sys.argv.(1) <> "-letpoly" && Sys.argv.(1) <> "-grade" then
      usage_exit()
    else if Array.length Sys.argv > 2 && Sys.argv.(2).[0] = '-' && Sys.argv.(2) <> "-letpoly" && Sys.argv.(2) <> "-grade" then
      usage_exit()
  in
  
  let letpoly = (Sys.argv.(1) = "-letpoly" || (Array.length Sys.argv > 2 && Sys.argv.(2) = "-letpoly")) in
  let grade = (Sys.argv.(1) = "-grade" || (Array.length Sys.argv > 2 && Sys.argv.(2) = "-grade")) in
  let filearg = 1 + (if letpoly then 1 else 0) + (if grade then 1 else 0) in
  let file = open_in (Sys.argv.(filearg)) in
  let lexbuf = Lexing.from_channel file in
  let e =
    try Parser.exp Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at line %d\n" pos.Lexing.pos_lnum;
      exit 1 in

  
  let _ = 
    Format.printf "@[";
    Format.printf "Expression:@\n  @[";
    Pprint.printExp e;
    Format.printf "@]@\n@\n" in

  let _ = 
    Format.printf "Typechecking the expression...@\n";
    if letpoly then Format.printf "  using let polymorphism@\n\n" else ();
    Format.print_flush () in

  let t,c = if letpoly then (Poly.check VarMap.empty e) else (Check.check VarMap.empty e) in

  let _ = if not grade then
            (Format.printf "Initial Type:@\n  @[";
             Pprint.printTyp t;
             Format.printf "@]@\n@\n") in
             
  let _ = if not grade then (
            Format.printf "Constraints:@\n  @[";
            let _ =
              Constr.fold
                (fun (t1,t2) b ->
                  if b then Format.printf "@\n";
                  Pprint.printTyp t1;
                  Format.printf "@ =@ ";
                  Pprint.printTyp t2;
                  true)
                c false in
            Format.printf "@]@\n@\n") in
  
  let s = Check.unify c in
  let restype = Helper.apply_subst s t in


  (* Utility function for grading to rename the type variables in result to a canonical form *)
  let canon_name t =
    let m = ref VarMap.empty in
    let c = ref 2600 in
    let rec visit s =
      match s with
      | TInt | TBool -> s
      | TVar y ->
         (if not (VarMap.mem y !m) then
            let i = !c in
            incr c;
            m := VarMap.add y (Helper.tvar_name i) !m
         );
         TVar (VarMap.find y !m)
      | TPair(t1,t2) ->
         let t1' = visit t1 in
         let t2' = visit t2 in
         TPair(t1', t2')
      | TArrow(t1,t2) ->
         let t1' = visit t1 in
         let t2' = visit t2 in
         TArrow(t1', t2')
    in
    visit t
  in
  
  let _ = 
    Format.printf "Result:@\n  @[";
    Pprint.printTyp (if grade then canon_name restype else restype);
    Format.printf "@]@\n@\n" in

  let _ = 
    Format.printf "Evaluating the expression...@\n";
    Format.print_flush () in
  
  let v = Eval.eval VarMap.empty e in

  let _ = 
    Format.printf "Result:@\n  @[";
    Pprint.printVal v;
    Format.printf "@]@\n";
    Format.printf "@]" in
  ()
