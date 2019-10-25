module Ll = Llama_lib.Llcore
module C  = Core

let x     = Ll.mk_int_func "x" [];;
let y     = Ll.mk_int_func "y" [];;
let zero  = Ll.mk_int_lit 0;;
let one   = Ll.mk_int_lit 1;;

let start = Ll.mk_int_nonterminal "START";;
let g = Ll.mk_lia_grammar [zero; one] [x; y];;
let depth = 4;;
let ts = Ll.blast_expand g depth start;;
print_string ((Ll.term_set_to_string ts) ^ "\n");;