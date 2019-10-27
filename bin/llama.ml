module Ll = Llama_lib.Llcore

let x     = Ll.mk_int_const "x";;
let y     = Ll.mk_int_const "y";;
let zero  = Ll.mk_int_lit 0;;
let one   = Ll.mk_int_lit 1;;
let g = Ll.default_lia_grammar [zero; one] [x; y];;

let depth = 3;;
let ts = Ll.blast_expand g depth Ll.lia_start;;
print_string ((Ll.term_set_to_string ts) ^ "\n");;