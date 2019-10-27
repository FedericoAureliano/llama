type uterm = 
  | Nonterminal of string
  | Literal     of string
  | Function    of (string * (term list))
and term = 
  | Int    of uterm
  | Bool   of uterm
  | BitVec of (int * uterm)
  | Array  of (term * term * uterm)

type term_set = Node of (term * (term_set list))

val term_to_string     : term -> string
val term_set_to_string : term_set  -> string

module TermMap : sig
  type +'a t 
end

val blast_expand : (term list TermMap.t) -> int -> term -> term_set

val mk_int_nonterminal : string -> term
val mk_int_func        : string -> (term list) -> term
val mk_int_const       : string -> term
val mk_int_lit         : int -> term

val default_lia_grammar : (term list) -> (term list TermMap.t)
val lia_start : term