module C = Core

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

let rec term_to_string_u (t : uterm) : string = 
  match t with
  | Nonterminal l       -> "?" ^ l ^ "?"
  | Literal     v       -> v
  | Function    (f, []) -> f
  | Function    (f, x)  -> "(" ^ f ^ " "  ^ (String.concat " " (List.map term_to_string x)) ^ ")"
and term_to_string (s : term) : string =
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

let term_to_name (s : term) : string =
  match s with
  | Int    t         -> term_to_name_u t
  | Bool   t         -> term_to_name_u t
  | BitVec (_, t)    -> term_to_name_u t
  | Array  (_, _, t) -> term_to_name_u t

let string_repeat s n =
  String.concat "" (Array.to_list (Array.make n s))

let rec term_set_to_string_depth (d : int) (p : term_set): string =
  let s = 
  (match p with
  | Node (x, []) -> (string_repeat "  " d) ^ (term_to_string x)
  | Node (x, ls) -> (string_repeat "  " d) ^ (term_to_name x)  ^ (String.concat " " (List.map (term_set_to_string_depth (d+1)) ls)))
  in (if d <> 0 then ("\n" ^ s) else s)

let term_set_to_string = term_set_to_string_depth 0

let expand (grammar : term list C.String.Map.t) (label : string) : (term list) =
  match C.Map.find grammar label with
    | None -> raise (Failure "Nonterminal not in grammar!")
    | Some x -> x

let rec blast_expand (g : term list C.String.Map.t) (i : int) (t: term): term_set =
  if (i >= 0 && i < 15)
  then (
    match t with 
    | Int    Nonterminal l            -> Node (t, List.map (blast_expand g (i-1)) (expand g l))
    | Int    Literal    (_)           -> Node (t, [])
    | Int    Function   (_, ls)       -> Node (t, List.map (blast_expand g (i-1)) ls)
    | Bool   Nonterminal l            -> Node (t, List.map (blast_expand g (i-1)) (expand g l))
    | Bool   Literal    (_)           -> Node (t, [])
    | Bool   Function   (_, ls)       -> Node (t, List.map (blast_expand g (i-1)) ls)
    | BitVec (_, Nonterminal l)       -> Node (t, List.map (blast_expand g (i-1)) (expand g l))
    | BitVec (_, Literal (_))         -> Node (t, []) 
    | BitVec (_, Function (_, ls))    -> Node (t, List.map (blast_expand g (i-1)) ls)
    | Array  (_, _, Nonterminal l)    -> Node (t, List.map (blast_expand g (i-1)) (expand g l))
    | Array  (_, _, Literal (_))      -> Node (t, []) 
    | Array  (_, _, Function (_, ls)) -> Node (t, List.map (blast_expand g (i-1)) ls))
  else Node (t, [])

(* mk functions *)
let mk_bool_nonterminal l = Bool (Nonterminal l)
let mk_bool_func n ls     = Bool (Function (n, ls))

let mk_int_nonterminal l = Int (Nonterminal l)
let mk_int_func n ls     = Int (Function (n, ls))
let mk_int_const n       = Int (Function (n, []))
let mk_int_lit  v        = Int (Literal (string_of_int v))

let start = mk_int_nonterminal "START"
let v     = mk_int_nonterminal "VAR"
let l     = mk_int_nonterminal "LIT"
let b     = mk_bool_nonterminal "COMP"
let plus  = mk_int_func "+" [start; start]
let minus = mk_int_func "-" [start; start]
let times = mk_int_func "*" [l; start]
let ite   = mk_int_func "ite" [b; start; start]
let eq    = mk_bool_func "=" [start; start]
let lt    = mk_bool_func "<" [start; start]
let mk_lia_grammar (lits : (term list)) (vars : (term list)) : (term list C.String.Map.t) = 
  C.String.Map.of_alist_exn [
  ("START", [l; v; plus; minus; times; ite]);
  ("LIT", lits);
  ("VAR", vars);
  ("COMP", [eq; lt])
]