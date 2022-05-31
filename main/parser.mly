%{
  open Ast
  open Printf
  open Lexing
%}

%token <int> INTEGER
%token <string> VAR
%token PLUS DASH LPAREN RPAREN COMMA COLON DOT EQUALS TRUE FALSE
       IF THEN ELSE FST SND LAMBDA LET REC IN EOF AND
       INT BOOL ARROW STAR

%type <Ast.exp> exp

%start exp
 
%%

exp : LET VAR EQUALS exp IN exp         { Let($2,$4,$6) }
    | LET REC VAR EQUALS LAMBDA VAR DOT exp IN exp { Letrec($3,$6,$8,$10) }
    | lexp                              { $1 }

lexp : LAMBDA VAR DOT lexp  { Lam ($2,$4) }
    | cexp                  { $1 }
 
cexp : IF exp THEN oexp ELSE oexp  { If ($2,$4,$6) }
     | oexp                        { $1 }

oexp : oexp PLUS appexp            { Plus($1,$3) }
     | oexp STAR appexp            { Times($1,$3) }
     | oexp DASH appexp            { Minus($1,$3) }
     | appexp EQUALS appexp        { Eq ($1,$3) }
     | appexp                      { $1 }

appexp : appexp aexp               { App($1,$2) }
    | FST aexp                     { Fst $2 }              
    | SND aexp                     { Snd $2 }              
    | aexp                         { $1 } 

aexp: VAR                          { Var $1 }
    | INTEGER                      { Int $1 }
    | TRUE                         { True }
    | FALSE                        { False }
    | LPAREN exp COMMA exp RPAREN  { Pair($2,$4) }
    | LPAREN exp RPAREN            { $2 }
