(* DATA TYPES *)
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

(* TO_STRINGS *)
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

let leaf_u (t : uterm) : bool = 
  match t with
  | Nonterminal _       -> false
  | Literal     _       -> true
  | Function    (_, []) -> true
  | Function    (_, _)  -> false

let leaf (s : term) : bool =
  match s with
  | Int    t         -> leaf_u t
  | Bool   t         -> leaf_u t
  | BitVec (_, t)    -> leaf_u t
  | Array  (_, _, t) -> leaf_u t

let rec realizable (ts : term_set) : bool =
  match ts with
  | Node (t, []) -> leaf t
  | Node (Int (Function (_, gs)), ls)         -> (List.compare_lengths gs (List.filter realizable ls)) = 0
  | Node (Bool (Function (_, gs)), ls)        -> (List.compare_lengths gs (List.filter realizable ls)) = 0
  | Node (BitVec (_, Function (_, gs)), ls)   -> (List.compare_lengths gs (List.filter realizable ls)) = 0
  | Node (Array (_, _, Function (_, gs)), ls) -> (List.compare_lengths gs (List.filter realizable ls)) = 0
  | Node (_, ls) -> List.for_all realizable ls 

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

let rec clean_blast (ts : term_set) : term_set = 
  match ts with 
  | Node (t, ls) -> Node (t, List.filter realizable (List.map clean_blast ls))

let rec blast_expand_helper (g : term list TermMap.t) (i : int) (t: term): term_set =
  if i > 10 then raise (Failure "Blasting that deep is too scary for me. Sorry.") else
  if i >= 0
  then (
    match t with 
    | Int    Nonterminal _            -> Node (t, List.map (blast_expand_helper g (i-1)) (TermMap.find t g))
    | Int    Literal    (_)           -> Node (t, [])
    | Int    Function   (_, ls)       -> Node (t, List.map (blast_expand_helper g (i-1)) ls)
    | Bool   Nonterminal _            -> Node (t, List.map (blast_expand_helper g (i-1)) (TermMap.find t g))
    | Bool   Literal    (_)           -> Node (t, [])
    | Bool   Function   (_, ls)       -> Node (t, List.map (blast_expand_helper g (i-1)) ls)
    | BitVec (_, Nonterminal _)       -> Node (t, List.map (blast_expand_helper g (i-1)) (TermMap.find t g))
    | BitVec (_, Literal (_))         -> Node (t, []) 
    | BitVec (_, Function (_, ls))    -> Node (t, List.map (blast_expand_helper g (i-1)) ls)
    | Array  (_, _, Nonterminal _)    -> Node (t, List.map (blast_expand_helper g (i-1)) (TermMap.find t g))
    | Array  (_, _, Literal (_))      -> Node (t, []) 
    | Array  (_, _, Function (_, ls)) -> Node (t, List.map (blast_expand_helper g (i-1)) ls))
  else Node (t, [])

let blast_expand (g : term list TermMap.t) (i : int) (t: term): term_set = clean_blast (blast_expand_helper g i t)

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
let nonzero   = mk_int_nonterminal  "NON-ZERO"
let novar     = mk_int_nonterminal  "NO-VAR"
let novarnz   = mk_int_nonterminal  "NO-VAR-NON-ZERO"
let var       = mk_int_nonterminal  "VAR"
let comp      = mk_bool_nonterminal ""
let plus      = mk_int_func  "+"   [nonzero; nonzero]
let nplus     = mk_int_func  "+"   [novarnz; novarnz]
let minus     = mk_int_func  "-"   [lia_start; nonzero]
let nminus    = mk_int_func  "-"   [novar; novarnz]
let times     = mk_int_func  "*"   [novar; nonzero]
let ntimes    = mk_int_func  "*"   [novar; novarnz]
let ite       = mk_int_func  "ite" [comp; lia_start; lia_start]
let eq        = mk_bool_func "="   [lia_start; lia_start]
let lt        = mk_bool_func "<"   [lia_start; lia_start]
let zero      = mk_int_lit 0;;
let one       = mk_int_lit 1;;

(* DEFAULT GRAMMARS *)
let default_lia_grammar (vars : (term list)) : (term list TermMap.t) = 
  mk_grammar [
    (lia_start, [zero; one; var; plus; minus; times; ite]);
    (nonzero,   [one; var; plus; minus; times]);
    (novar,     [zero; one; nplus; nminus; ntimes]);
    (novarnz,   [one; nplus; nminus; ntimes]);
    (comp,      [eq; lt]);
    (var,       vars);
    ]