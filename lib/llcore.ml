(* -------------- Basic types --------------- *)
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

(* -------------- Mk Functions --------------- *)
let decl_func (n: string) (ag : (sort list)) (s : sort) = Decl (n, ag, s)
let mk_const (n : string) (s : sort) = (s, App (decl_func n [] s, []))


(* -------------- To Strings --------------- *)
let get_name (f : func) : string =
  match f with
  | Defn (n, _, _, _) -> n
  | Decl (n, _, _)    -> n

let rec sort_to_string (s : sort) : string =
  match s with
  | Array  (i,c) -> "(Array " ^ (sort_to_string i) ^ " " ^ (sort_to_string c) ^ ")"
  | BitVec (w)   -> "(BitVec" ^ (string_of_int w) ^ ")" 
  | Bool         -> "Bool"
  | Int          -> "Int"
  | String       -> "String"
and uterm_to_string (u : uterm) : string = 
  match u with
  | Q n         -> n
  | Lit v       -> v
  | App (f, []) -> get_name f
  | App (f, ls) -> "(" ^ (get_name f) ^ " " ^ (String.concat " " (List.map term_to_string ls)) ^ ")"
and term_to_string (t: term) : string = 
  match t with
  | _, u -> uterm_to_string u

let sig_pair_to_string (p : string * sort) : string = "(" ^ (fst p) ^ " " ^ (sort_to_string (snd p))^ ")" 

let func_to_string (f : func) : string = 
  match f with
  | Defn (n, ar, s, b) -> "(define-fun " ^ n ^ " (" ^ (String.concat " " (List.map sig_pair_to_string ar)) ^ (sort_to_string s) ^ (term_to_string b) ^ ")" 
  | Decl (n, ar, s)    -> "(declare-fun " ^ n ^ " (" ^ (String.concat " " (List.map sort_to_string ar)) ^ (sort_to_string s) ^ ")"

let command_to_string (c : command) : string = 
  match c with
  | Declare f -> func_to_string f
  | Assert b  -> "(assert " ^ (term_to_string b) ^ ")"
  | Check     -> "(check-sat)"

let query_to_string (q : query) : string = (String.concat "\n" (List.map command_to_string q))

let term_to_name_u (u : uterm) : string = 
  match u with
  | Q n         -> n
  | Lit v       -> v
  | App (f, _) -> get_name f

let term_to_name (s : term) : string =
  match s with
  | _, u         -> term_to_name_u u


(* -------------- Grammars --------------- *)
let nonterm_compare (n : nonterm) (m : nonterm) : int = 
  if n = "START" && m = "START" then 0 
  else if n = "START" then -1 
  else if m = "START" then  1 
  else String.compare n m

module NontermMap = Map.Make(struct type t = nonterm let compare = nonterm_compare end)

type grammar = (term list NontermMap.t)

let mk_grammar (ls : (nonterm * (term list)) list) : grammar =
  List.fold_left (fun a (x, y) -> NontermMap.add x y a) NontermMap.empty ls

let get_start (g : grammar) (s : sort) : term = (s, Q (fst (NontermMap.min_binding g)))


(* -------------- Derivations --------------- *)
type term_set = Node of (term * (term_set list))

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
  | Q   _       -> false
  | Lit _       -> true
  | App (_, []) -> true
  | App (_, _)  -> false

let leaf (s : term) : bool =
  match s with
  | _, u -> leaf_u u

let rec realizable (ts : term_set) : bool =
  match ts with
  | Node (t, [])                -> leaf t
  | Node ((_, App (_, gs)), ls) -> (List.compare_lengths gs (List.filter realizable ls)) = 0
  | Node (_, ls)                -> List.for_all realizable ls 

let rec clean_blast (ts : term_set) : term_set = 
  match ts with 
  | Node (t, ls) -> Node (t, List.filter realizable (List.map clean_blast ls))

let rec blast_expand_helper (g : grammar) (i : int) (t: term): term_set =
  if i > 10 then raise (Failure "Blasting that deep is too scary for me. Sorry.") else
  if i >= 0
  then (
    match t with
    | (_, Q n )        -> Node (t, List.map (blast_expand_helper g (i-1)) (NontermMap.find n g))
    | (_, Lit _)       -> Node (t, [])
    | (_, App (_, ls)) -> Node (t, List.map (blast_expand_helper g (i-1)) ls))
  else Node (t, [])

let blast_expand (g : grammar) (i : int) (t: term): term_set = clean_blast (blast_expand_helper g i t)