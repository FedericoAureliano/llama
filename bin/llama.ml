open Llama_lib

let int_lits  = ["0"; "1"];;
let int_vars  = ["x"; "y"];;
let bool_vars = ["a"; "b"];;

let iters = 10;;

let rec print_n_ints (t : Lia.term) (n : int): unit = 
  ((print_string (Lia.to_string t ^ "\n")); 
  if (n > 0) then (print_n_ints (Lia.next int_lits int_vars t) (n - 1)));;

let rec print_n_bools (t : Bool.term) (n : int): unit = 
  ((print_string (Bool.to_string t ^ "\n")); 
  if (n > 0) then (print_n_bools (Bool.next bool_vars t) (n - 1)));;

print_string "LIA terms with 0, 1, x, and y\n\n";;
print_n_ints (Lia.Lit "0") iters;;
print_string "\nStart at a bigger term and continue\n\n";;
print_n_ints (Lia.Plus (Lia.Times (Lia.Lit "0", Lia.Var "x"), Lia.Times (Lia.Lit "0", Lia.Lit "0"))) iters;;

print_string "\nNow print boolean terms\n\n";;
print_n_bools Bool.True iters;
