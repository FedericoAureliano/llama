type terminal    = string
type nonterminal = string

type derivation =
  | T of (terminal)
  | N of (nonterminal)
  | F of (terminal * (derivation list))

type rule = (nonterminal * (derivation list))

val derivation_to_string : derivation -> string

module NTMap : sig
  type +'a t 
end
type grammar = (derivation list NTMap.t)

val mk_grammar     : rule list -> grammar

val enumerate : grammar -> int -> derivation list