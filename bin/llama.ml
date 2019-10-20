let rec print_next_n (t : Lia.term) (n : int): unit = 
  ((print_string (Lia.to_string t ^ "\n")); if (n > 0) then (print_next_n (Lia.next t) (n - 1)));;

(* Print first 51 LIA terms
      - with constants 0 and 1
      - with variables x and y
      - with boolean placeholders ("?b") for if-then-else operator *)
print_next_n Lia.bottom 30;;

(* Start at a bigger term and print the next 20 *)
let curr = Lia.Plus (Lia.Times (Lia.Lit "0", Lia.Var "x"), Lia.Times (Lia.Lit "0", Lia.Lit "0")) in
print_next_n curr 20;;