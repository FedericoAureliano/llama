type term =
  | Lit   of string
  | Var   of string
  | Plus  of (term * term)
  | Minus of (term * term)
  | Times of (term * term)
  | ITE   of (term * term)

val literals  : (string list)
val variables : (string list)
val to_string : term -> string
val bottom    : term
val next      : term -> term