module C = Core

type uterm = 
  | Nonterminal of string
  | Literal     of string
  | Function    of (string * (sterm list))
and sterm = 
  | Int    of uterm
  | Bool   of uterm
  | BitVec of (int * uterm)
  | Array  of (sterm * sterm * uterm)

type pset = Node of (sterm * (pset list))

let rec term_to_string_u (t : uterm) : string = 
  match t with
  | Nonterminal l       -> "?" ^ l ^ "?"
  | Literal     v       -> v
  | Function    (f, []) -> f
  | Function    (f, x)  -> "(" ^ f ^ " "  ^ (String.concat " " (List.map term_to_string x)) ^ ")"
and term_to_string (s : sterm) : string =
  match s with
  | Int    t         -> term_to_string_u t
  | Bool   t         -> term_to_string_u t
  | BitVec (_, t)    -> term_to_string_u t
  | Array  (_, _, t) -> term_to_string_u t

let term_to_name_u (t : uterm) : string = 
  match t with
  | Nonterminal l      -> l
  | Literal     v      -> v
  | Function    (f, _) -> f

let term_to_name (s : sterm) : string =
  match s with
  | Int    t         -> term_to_name_u t
  | Bool   t         -> term_to_name_u t
  | BitVec (_, t)    -> term_to_name_u t
  | Array  (_, _, t) -> term_to_name_u t

let string_repeat s n =
  String.concat "" (Array.to_list (Array.make n s))

let rec pset_to_string_depth (d : int) (p : pset): string =
  let s = 
  (match p with
  | Node (x, []) -> (string_repeat "  " d) ^ (term_to_string x)
  | Node (x, ls) -> (string_repeat "  " d) ^ (term_to_name x)  ^ (String.concat " " (List.map (pset_to_string_depth (d+1)) ls)))
  in (if d <> 0 then ("\n" ^ s) else s)

let pset_to_string = pset_to_string_depth 0

let expand (grammar : sterm list C.String.Map.t) (label : string) : (sterm list) =
  match C.Map.find grammar label with
    | None -> raise (Failure "Nonterminal not in grammar!")
    | Some x -> x

let rec generate (g : sterm list C.String.Map.t) (i : int) (t: sterm): pset =
  if i > 0 
  then (
    match t with 
    | Int    Nonterminal l            -> Node (t, List.map (generate g (i-1)) (expand g l))
    | Int    Literal    (_)           -> Node (t, [])
    | Int    Function   (_, ls)       -> Node (t, List.map (generate g (i-1)) ls)
    | Bool   Nonterminal l            -> Node (t, List.map (generate g (i-1)) (expand g l))
    | Bool   Literal    (_)           -> Node (t, [])
    | Bool   Function   (_, ls)       -> Node (t, List.map (generate g (i-1)) ls)
    | BitVec (_, Nonterminal l)       -> Node (t, List.map (generate g (i-1)) (expand g l))
    | BitVec (_, Literal (_))         -> Node (t, []) 
    | BitVec (_, Function (_, ls))    -> Node (t, List.map (generate g (i-1)) ls)
    | Array  (_, _, Nonterminal l)    -> Node (t, List.map (generate g (i-1)) (expand g l))
    | Array  (_, _, Literal (_))      -> Node (t, []) 
    | Array  (_, _, Function (_, ls)) -> Node (t, List.map (generate g (i-1)) ls))
  else Node (t, [])

(* mk functions *)
let mk_int_nonterminal l = Int (Nonterminal l)
let mk_int_func n ls     = Int (Function (n, ls))
let mk_int_lit  v        = Int (Literal (string_of_int v))
