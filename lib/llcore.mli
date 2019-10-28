type nonterm = string

type sort = 
  | Array  of (sort * sort)
  | BitVec of int
  | Bool
  | Int
  | String

type term = (sort * uterm)
and uterm = 
  | Q   of nonterm
  | Lit of string
  | App of (func * (term list))
and func = 
  | Defn of string * ((string * sort) list) * sort * term 
  | Decl of string * (sort list) * sort

type command =
  | Declare of func
  | Assert  of term
  | Check

type query = (command list)

val decl_func : string -> (sort list) -> sort -> func
val mk_const  : string -> sort -> term

val query_to_string : query -> string
val term_to_string  : term  -> string
val term_to_name    : term  -> string

module NontermMap : sig
  type +'a t 
  val find : nonterm -> 'a t -> 'a
end

type grammar = (term list NontermMap.t)

val mk_grammar : (nonterm * (term list)) list -> grammar
val get_start :  grammar -> sort -> term

type term_set = Node of (term * (term_set list))
val term_set_to_string : term_set  -> string
val blast_expand : grammar -> int -> term -> term_set