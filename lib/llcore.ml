(* -------------- Basic types --------------- *)
type terminal    = string
type nonterminal = string

type derivation =
  | T of (terminal)
  | N of (nonterminal)
  | F of (terminal * (derivation list))

type rule = (nonterminal * (derivation list))

(* -------------- Grammars --------------- *)
(* This means that if there is no Start symbol, then the entry point to the
   grammar is the first nonterminal in alphabetical order. *)
let nonterminal_compare (n : nonterminal) (m : nonterminal) : int = 
  if n = "Start" && m = "Start" then 0 
  else if n = "Start" then -1 
  else if m = "Start" then  1 
  else String.compare n m

module NTMap = Map.Make(struct type t = nonterminal let compare = nonterminal_compare end)

(* A grammar is just a map from nonterminals to a list of derivations *)
type grammar = (derivation list NTMap.t)

(* You can make a grammar by passing in a list of rewrite rules *)
let mk_grammar (ls : (rule list)) : grammar =
  List.fold_left (fun a (x, y) -> NTMap.add x y a) NTMap.empty ls

(* -------------- Helper Functions and To Strings --------------- *)
let rec derivation_to_string (d : derivation) : string =
  match d with
  | T (k)     -> k
  | N (e)     -> e
  | F (f, ls) -> "(" ^ f ^ " " ^ (String.concat " " (List.map derivation_to_string ls)) ^ ")"

let rec is_complete (d : derivation) : bool = 
  match d with
  | T ( _)     -> true
  | N ( _)     -> false
  | F ( _, ls) -> List.for_all is_complete ls

let get_start (g : grammar) : nonterminal = 
  fst (NTMap.min_binding g)

let expand (g : grammar) (nt : nonterminal) : derivation list = 
  (NTMap.find nt g)

let rec map_until_some (f : 'a -> 'a option) (ls : 'a list) : 'a list option = 
  match ls with
  | []    -> None
  | y::ys -> match (f y) with
    | Some v -> Some (v :: ys)
    | None   -> (match map_until_some f ys with
        | Some ns -> Some (y :: ns)
        | None    -> None)

(* -------------- Enumeration --------------- *)
let first (g : grammar) : derivation = N (get_start g)

let rec expand_leftmost (g : grammar) (n : int) (d : derivation) : derivation option =
  match d with
  | T (_)     -> None
  | N (nt)    -> List.nth_opt (expand g nt) n
  | F (f, ls) -> (match map_until_some (expand_leftmost g n) ls with
      | Some vs -> Some (F (f, vs))
      | None    -> None)

let rec get_neighbours_helper (g : grammar) (d : derivation) (n : int) : derivation list = 
  match expand_leftmost g n d with 
  | Some v -> v :: get_neighbours_helper g d (n + 1)
  | None -> []
  
let get_neighbours (g : grammar) (d : derivation) : derivation list = get_neighbours_helper g d 0

let enumerate (g : grammar) (n : int) : derivation list =
  let q = Queue.create () in
  Queue.push (first g) q;

  let bfs (x : derivation) =
    if (is_complete x)
    then Some x
    else ((List.iter (fun x -> Queue.add x q) (get_neighbours g x)); None)
  in
  
  let rec build i =
    if i = 0 then [] else 
      match (bfs (Queue.pop q)) with
      | Some v -> (v::build (i - 1))
      | None   -> (build i)
  in

  build n