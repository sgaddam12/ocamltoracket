If you're using Windows, make sure to use the Cygwin terminal to run the following. The execution and correctness script are for compiling the results
of executing the translation of the programs as well as executing their Racket equivalent to test for correctness.

To execute:

ocamlc -o {name-of-prog} -I +compiler-libs ocamlcommon.cma str.cma parseToAST.ml; ./{name-of-prog} {ocaml-file-to-translate}

Parsetree visualization:

ocamlc -dparsetree {ocaml-file}