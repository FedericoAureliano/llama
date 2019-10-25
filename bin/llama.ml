module Ll = Llama_lib.Llcore
module C  = Core

let start = Ll.mk_int_nonterminal "start";;
let plus  = Ll.mk_int_func "+" [start; start];;
let times = Ll.mk_int_func "*" [start; start];;
let x     = Ll.mk_int_func "x" [];;
let y     = Ll.mk_int_func "y" [];;
let zero  = Ll.mk_int_lit 0;;
let one   = Ll.mk_int_lit 1;;

let grammar = C.String.Map.of_alist_exn [
  ("start", [zero; one; x; y; plus; times])
];;

let depth = 4;;

let ts = Ll.blast grammar depth plus;;

print_string ((Ll.term_set_to_string ts) ^ "\n");;