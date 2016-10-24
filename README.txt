To execute:

ocamlc -o {name-of-prog} -I +compiler-libs ocamlcommon.cma str.cma parseToAST.ml; ./{name-of-prog} {ocaml-file-to-translate}

Parsetree visualization:

ocamlc -dparsetree {ocaml-file}