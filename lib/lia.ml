module Ll = Llcore

(* Nonterminals *)
let start   = "START"
let nonzero = "NON-ZERO"
let novar   = "NO-VAR"
let novarnz = "NO-VAR-NON-ZERO"
let var     = "VAR"
let comp    = "COMP"

(* Function declarations *)
let plus  = Ll.Decl ("+",   [Ll.Int;  Ll.Int],         Ll.Int)
let minus = Ll.Decl ("-",   [Ll.Int;  Ll.Int],         Ll.Int)
let times = Ll.Decl ("*",   [Ll.Int;  Ll.Int],         Ll.Int)
let ite   = Ll.Decl ("ite", [Ll.Bool; Ll.Int; Ll.Int], Ll.Int)
let eq    = Ll.Decl ("=",   [Ll.Int;  Ll.Int],         Ll.Bool) 
let lt    = Ll.Decl ("<",   [Ll.Int;  Ll.Int],         Ll.Bool)

(* Terms for production rules *)
let fplus  = (Ll.Int,  Ll.App (plus,  [(Ll.Int,  Ll.Q nonzero); (Ll.Int, Ll.Q nonzero)]))
let cplus  = (Ll.Int,  Ll.App (plus,  [(Ll.Int,  Ll.Q novarnz); (Ll.Int, Ll.Q novarnz)]))
let fminus = (Ll.Int,  Ll.App (minus, [(Ll.Int,  Ll.Q start);   (Ll.Int, Ll.Q nonzero)]))
let cminus = (Ll.Int,  Ll.App (minus, [(Ll.Int,  Ll.Q novar);   (Ll.Int, Ll.Q novarnz)]))
let ftimes = (Ll.Int,  Ll.App (times, [(Ll.Int,  Ll.Q novarnz); (Ll.Int, Ll.Q nonzero)]))
let ctimes = (Ll.Int,  Ll.App (times, [(Ll.Int,  Ll.Q novarnz); (Ll.Int, Ll.Q novarnz)]))
let fite   = (Ll.Int,  Ll.App (ite,   [(Ll.Bool, Ll.Q comp);    (Ll.Int, Ll.Q start); (Ll.Int, Ll.Q start)]))
let feq    = (Ll.Bool, Ll.App (eq,    [(Ll.Int,  Ll.Q start);   (Ll.Int, Ll.Q start)]))
let flt    = (Ll.Bool, Ll.App (lt,    [(Ll.Int,  Ll.Q start);   (Ll.Int, Ll.Q start)]))

(* Literals *)
let zero = (Ll.Int, Ll.Lit "0")
let one  = (Ll.Int, Ll.Lit "1")

let default_lia_grammar (vars : (Ll.term list)) : (Ll.term list Ll.NontermMap.t) = 
  Ll.mk_grammar [
    (start,   [zero; one; (Int, Q var); fplus; fminus; ftimes; fite]);
    (nonzero, [one; (Int, Q var); fplus; fminus; ftimes]);
    (novar,   [zero; one; cplus; cminus; ctimes]);
    (novarnz, [one; cplus; cminus; ctimes]);
    (comp,    [feq; flt]);
    (var,     vars);]