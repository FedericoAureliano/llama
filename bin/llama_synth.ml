module Ll  = Llama_lib.Llcore
module Lia = Llama_lib.Lia 

let x = Ll.mk_const "x" Ll.Int;;
let y = Ll.mk_const "y" Ll.Int;;
let g = Lia.default_lia_grammar [x; y];;

let depth = 4;;
print_string ("Print All Default Grammar LIA Derivations Up To Depth " ^ string_of_int depth ^ ":\n\n");;
let ts = Ll.blast_expand g depth (Ll.get_start g Ll.Int);;
print_string ((Ll.term_set_to_string ts) ^ "\n");;