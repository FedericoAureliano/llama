type uterm = 
  | Placeholder
  | Literal     of string
  | Function    of (string * (sterm list))
and sterm = 
  | Int      of uterm
  | Bool     of uterm
  | BitVec   of (int * uterm)
  | Array    of (sterm * sterm * uterm)

type pset = Node of (sterm * (pset list))

val term_to_string : sterm -> string
val pset_to_string : pset  -> string
val size           : sterm -> int
val generate       : (sterm -> (sterm list)) -> int -> sterm -> pset

val mk_int_hole : sterm
val mk_int_func : string -> (sterm list) -> sterm
val mk_int_lit  : int -> sterm