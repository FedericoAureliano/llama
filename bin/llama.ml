let rec print_next_n (t : Lia.term) (n : int): unit = 
  ((print_string (Lia.to_string t ^ "\n")); if (n > 0) then (print_next_n (Lia.next t) (n - 1)));;

let curr = Lia.first in 
print_next_n curr 50;;