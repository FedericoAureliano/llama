module Ll = Llama_lib.Llcore
module C  = Core

let start = Ll.mk_int_nonterminal "start";;
let plus  = Ll.mk_int_func "+" [start; start];;
let x     = Ll.mk_int_func "x" [];;
let y     = Ll.mk_int_func "y" [];;
let zero  = Ll.mk_int_lit 0;;
let one   = Ll.mk_int_lit 1;;

let grammar = C.String.Map.of_alist_exn [
  ("start", [zero; one; x; y; plus])
];;

let depth = 3;;

let ps = Ll.generate grammar depth start;;

print_string ((Ll.pset_to_string ps) ^ "\n");;