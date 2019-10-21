type term =
  | True
  | False
  | TProp
  | Var   of string
  | Not   of (term)
  | Or    of (term * term)
  | And   of (term * term)

val to_string : term -> string
val next      : (string list) -> term -> term