module Ll = Llama_lib.Llcore

let x     = Ll.mk_int_const "x";;
let y     = Ll.mk_int_const "y";;
let g = Ll.default_lia_grammar [x; y];;
let depth = 2;;
print_string ("Print All Default Grammar LIA Derivations Up To Length " ^ string_of_int depth ^ ":\n\n");;
let ts = Ll.blast_expand g depth Ll.lia_start;;
print_string ((Ll.term_set_to_string ts) ^ "\n");;