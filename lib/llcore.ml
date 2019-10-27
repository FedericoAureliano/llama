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

let nonterminal_compare_u (t : uterm) (s : uterm) : int = 
  match t, s with
  | Nonterminal a, Nonterminal b     -> String.compare a b
  | Nonterminal _, _                 -> -1
  | Literal a, Literal b             -> String.compare a b
  | Literal _, Nonterminal _         -> 1
  | Literal _, Function (_, _)       -> -1
  | Function (a, _), Function (b, _) -> String.compare a b
  | Function (_, _), _               -> 1

let nonterminal_compare (t : term) (s : term) : int =
  match t, s with
  | Int a, Int b                     -> nonterminal_compare_u a b
  | Int _, _                         -> -1
  | Bool a, Bool b                   -> nonterminal_compare_u a b
  | Bool _, Int _                    -> 1
  | Bool _, _                        -> -1
  | BitVec (_, a), BitVec (_, b)     -> nonterminal_compare_u a b
  | BitVec (_, _), Array  (_, _, _)  -> -1
  | BitVec (_, _), _                 -> 1
  | Array (_, _, a), Array (_, _, b) -> nonterminal_compare_u a b
  | Array (_, _, _), _               -> 1; 

module TermMap = Map.Make(struct type t = term let compare = nonterminal_compare end)

let rec blast_expand (g : term list TermMap.t) (i : int) (t: term): term_set =
  if i > 10 then raise (Failure "Blasting that deep is too scary for me. Sorry.") else
  if i >= 0
  then (
    match t with 
    | Int    Nonterminal _            -> Node (t, List.map (blast_expand g (i-1)) (TermMap.find t g))
    | Int    Literal    (_)           -> Node (t, [])
    | Int    Function   (_, ls)       -> Node (t, List.map (blast_expand g (i-1)) ls)
    | Bool   Nonterminal _            -> Node (t, List.map (blast_expand g (i-1)) (TermMap.find t g))
    | Bool   Literal    (_)           -> Node (t, [])
    | Bool   Function   (_, ls)       -> Node (t, List.map (blast_expand g (i-1)) ls)
    | BitVec (_, Nonterminal _)       -> Node (t, List.map (blast_expand g (i-1)) (TermMap.find t g))
    | BitVec (_, Literal (_))         -> Node (t, []) 
    | BitVec (_, Function (_, ls))    -> Node (t, List.map (blast_expand g (i-1)) ls)
    | Array  (_, _, Nonterminal _)    -> Node (t, List.map (blast_expand g (i-1)) (TermMap.find t g))
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

let mk_grammar (ls : (term * term list) list) : (term list TermMap.t) =
  List.fold_left (fun a (x, y) -> TermMap.add x y a) TermMap.empty ls

let lia_start = mk_int_nonterminal  "START"
let vnonterm  = mk_int_nonterminal  "VAR"
let lnonterm  = mk_int_nonterminal  "LIT"
let bnonterm  = mk_bool_nonterminal "COMP"
let plus      = mk_int_func  "+"   [lia_start; lia_start]
let minus     = mk_int_func  "-"   [lia_start; lia_start]
let times     = mk_int_func  "*"   [lnonterm; lia_start]
let ite       = mk_int_func  "ite" [bnonterm; lia_start; lia_start]
let eq        = mk_bool_func "="   [lia_start; lia_start]
let lt        = mk_bool_func "<"   [lia_start; lia_start]

let default_lia_grammar (lits : (term list)) (vars : (term list)) : (term list TermMap.t) = 
  mk_grammar [
    (lia_start, [lnonterm; vnonterm; plus; minus; times; ite]);
    (lnonterm, lits);
    (vnonterm, vars);
    (bnonterm, [eq; lt])]