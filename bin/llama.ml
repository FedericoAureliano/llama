let rec print_next_n (t : Lia.term) (n : int): unit = 
  ((print_string (Lia.to_string t ^ "\n")); if (n > 0) then (print_next_n (Lia.next t) (n - 1)));;

(* Print first 50 LIA terms
      - with constants 0 and 1
      - with variables x and y
      - with boolean placeholders for if-then-else operator*)
print_next_n Lia.first 50;;