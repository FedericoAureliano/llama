type term
val literals  : (string list)
val variables : (string list)
val to_string : term -> string
val first     : term
val next      : term -> term