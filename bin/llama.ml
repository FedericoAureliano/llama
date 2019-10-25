open Llama_lib

let hole = Llcore.mk_int_hole;;
let plus = Llcore.mk_int_func "+" [hole; hole];;
let x    = Llcore.mk_int_func "x" [];;
let y    = Llcore.mk_int_func "y" [];;
let zero = Llcore.mk_int_lit 0;;
let one  = Llcore.mk_int_lit 1;;

let grammar (t : Llcore.sterm) : (Llcore.sterm list) = 
  match t with 
  | Int Placeholder -> [zero; one; x; y; plus]
  | _ -> [];;

let ps = Llcore.generate grammar 3 hole;;

print_string ((Llcore.pset_to_string ps) ^ "\n")