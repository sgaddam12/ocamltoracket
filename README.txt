To execute:

ocamlc -o myprog -I +compiler-libs ocamlcommon.cma parseToAST.ml; ./myprog

Parsetree visualization:

ocamlc -dparsetree exampletranslate.ml