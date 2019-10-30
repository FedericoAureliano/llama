module Ll  = Llama_lib.Llcore

let one   = Ll.T ("1");;
let x     = Ll.T ("x");;
let start = Ll.N ("Start");;
let plus  = Ll.F ("+", [start; start]);;
let times = Ll.F ("*", [start; start]);;

let p1 = ("Start", [one; x; plus; times]);;
let g = Ll.mk_grammar([p1]);;

List.iter (fun x -> (print_string ((Ll.derivation_to_string x) ^ "\n"))) (Ll.enumerate g 100)