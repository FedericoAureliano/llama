open Llama_lib.Llcore

let start = mk_int_hole;;
let plus  = mk_int_func "+" [start; start];;
let x     = mk_int_func "x" [];;
let y     = mk_int_func "y" [];;
let zero  = mk_int_lit 0;;
let one   = mk_int_lit 1;;
let depth = 3;;

let grammar (t : sterm) : (sterm list) = 
  match t with 
  | Int Hole -> [zero; one; x; y; plus]
  | _ -> [];;

let ps = generate grammar depth start;;

print_string ((pset_to_string ps) ^ "\n");;