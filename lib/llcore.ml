type uterm = 
  | Placeholder
  | Literal  of string
  | Function of (string * (sterm list))
and sterm = 
  | Int      of uterm
  | Bool     of uterm
  | BitVec   of (int * uterm)
  | Array    of (sterm * sterm * uterm)

let rec term_to_string_u (t : uterm) : string = 
  match t with
  | Placeholder      -> "??"
  | Literal        v -> v
  | Function (f, []) -> f
  | Function (f, x)  -> "(" ^ f ^ " "  ^ (String.concat " " (List.map term_to_string x)) ^ ")"
and term_to_string (s : sterm) : string =
  match s with
  | Int    t         -> term_to_string_u t
  | Bool   t         -> term_to_string_u t
  | BitVec (_, t)    -> term_to_string_u t
  | Array  (_, _, t) -> term_to_string_u t

let rec term_to_name_u (t : uterm) : string = 
  match t with
  | Placeholder      -> "??"
  | Literal        v -> v
  | Function (f, _)  -> f
and term_to_name (s : sterm) : string =
  match s with
  | Int    t         -> term_to_name_u t
  | Bool   t         -> term_to_name_u t
  | BitVec (_, t)    -> term_to_name_u t
  | Array  (_, _, t) -> term_to_name_u t

let rec is_function_u (t : uterm) : bool = 
  match t with
  | Placeholder      -> false
  | Literal        _ -> false
  | Function (_, ls) -> ls <> []
and is_function (s : sterm) : bool =
  match s with
  | Int    t         -> is_function_u t
  | Bool   t         -> is_function_u t
  | BitVec (_, t)    -> is_function_u t
  | Array  (_, _, t) -> is_function_u t

let rec size_u (t : uterm) : int = 
  match t with
  | Placeholder      -> 1
  | Literal        _ -> 1
  | Function (_, []) -> 1
  | Function (_, x)  -> 1 + (List.fold_left (+) 0 (List.map size x))
and size (s : sterm) : int =
  match s with
  | Int    t         -> size_u t
  | Bool   t         -> size_u t
  | BitVec (_, t)    -> size_u t
  | Array  (_, _, t) -> size_u t

type pset = Node of (sterm * (pset list))

let string_repeat s n =
  String.concat "" (Array.to_list (Array.make n s))

let rec pset_to_string_depth (d : int) (p : pset): string =
  let s = 
  (match p with
  | Node (x, []) -> if (is_function x) then "" else (string_repeat "  " d) ^ (term_to_string x)
  | Node (x, ls) -> (string_repeat "  " d) ^ (term_to_name x)  ^ (String.concat " " (List.map (pset_to_string_depth (d+1)) ls)))
  in (if d <> 0 then ("\n" ^ s) else s)

let pset_to_string = pset_to_string_depth 0

let rec generate (g : sterm -> (sterm list)) (i : int) (t: sterm): pset =
  if i > 0 
  then (
    match t with 
    | Int    Placeholder              -> Node (t, List.map (generate g (i-1)) (g t))
    | Int    Literal    (_)           -> Node (t, [])
    | Int    Function   (_, ls)       -> Node (t, List.map (generate g (i-1)) ls)
    | Bool   Placeholder              -> Node (t, List.map (generate g (i-1)) (g t))
    | Bool   Literal    (_)           -> Node (t, [])
    | Bool   Function   (_, ls)       -> Node (t, List.map (generate g (i-1)) ls)
    | BitVec (_, Placeholder)         -> Node (t, List.map (generate g (i-1)) (g t))
    | BitVec (_, Literal (_))         -> Node (t, []) 
    | BitVec (_, Function (_, ls))    -> Node (t, List.map (generate g (i-1)) ls)
    | Array  (_, _, Placeholder)      -> Node (t, List.map (generate g (i-1)) (g t))
    | Array  (_, _, Literal (_))      -> Node (t, []) 
    | Array  (_, _, Function (_, ls)) -> Node (t, List.map (generate g (i-1)) ls))
  else Node (t, [])


(* mk functions *)
let mk_int_hole      = Int Placeholder
let mk_int_func n ls = Int (Function (n, ls))
let mk_int_lit  v    = Int (Literal (string_of_int v))