type token =
  | INTEGER of (int)
  | VAR of (string)
  | PLUS
  | DASH
  | LPAREN
  | RPAREN
  | COMMA
  | COLON
  | DOT
  | EQUALS
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | FST
  | SND
  | LAMBDA
  | LET
  | REC
  | IN
  | EOF
  | AND
  | INT
  | BOOL
  | ARROW
  | STAR

val exp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.exp
