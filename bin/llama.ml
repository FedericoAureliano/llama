let rec print_next_n (ls : (string list)) (vs : (string list)) (t : Lia.term) (n : int): unit = 
  ((print_string (Lia.to_string t ^ "\n")); if (n > 0) then (print_next_n ls vs (Lia.next ls vs t) (n - 1)));;

(* Print first 10 LIA terms
      - with constants 0 and 1
      - with variables x and y
      - with boolean placeholders ("?b") for if-then-else operator *)
let int_lits = ["0"; "1"] in
let int_vars = ["x"; "y"] in
print_next_n int_lits int_vars (Lia.Lit "0") 10;

print_string "\nStart at a bigger term and print the next 10\n\n";
let curr = Lia.Plus (Lia.Times (Lia.Lit "0", Lia.Var "x"), Lia.Times (Lia.Lit "0", Lia.Lit "0")) in
print_next_n int_lits int_vars curr 10;;