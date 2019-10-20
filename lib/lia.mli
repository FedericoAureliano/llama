type term =
  | Lit   of string
  | Var   of string
  | Plus  of (term * term)
  | Minus of (term * term)
  | Times of (term * term)
  | ITE   of (term * term)

val to_string : term -> string
val next      : (string list) -> (string list) -> term -> term