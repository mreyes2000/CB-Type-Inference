set top=c:\ocaml
set ocamlc=%top%\ocamlc
set ocamllex=%top%\ocamllex
set ocamlyacc=%top%\ocamlyacc

%ocamlc% -c -g ast.ml
%ocamlyacc% -q parser.mly
%ocamlc% -c -g parser.mli
%ocamllex% -q lexer.mll
%ocamlc% -c -g lexer.ml
%ocamlc% -c -g parser.ml
%ocamlc% -c -g pprint.ml
%ocamlc% -c -g helper.ml
%ocamlc% -c -g check.ml
%ocamlc% -c -g poly.ml
%ocamlc% -c -g eval.ml
%ocamlc% -c -g main.ml
%ocamlc% -g -o lam.exe ast.cmo lexer.cmo parser.cmo pprint.cmo helper.cmo check.cmo poly.cmo eval.cmo main.cmo
