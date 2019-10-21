exception Tie

let rec next_ls (ls: (string list)) (x : string) : string option = 
  match ls with
    | y::ys -> if ((x = y) && ((List.length ys) > 0)) then Some (List.hd ys) else (next_ls ys x) 
    | _     -> None

type term =
  | True
  | False
  | TFunc
  | Var   of string
  | Not   of (term)
  | Or    of (term * term)
  | And   of (term * term)

let rec to_string (t : term) : string = 
  match t with
  | True         -> "true"
  | False        -> "false"
  | TFunc        -> "?b?"
  | Var    e     -> e
  | Not    e     -> "(not "    ^ (to_string e) ^ ")"
  | Or    (e, f) -> "(or "     ^ (to_string e) ^ " " ^ (to_string f) ^ ")"
  | And   (e, f) -> "(and "    ^ (to_string e) ^ " " ^ (to_string f) ^ ")"

let rec size (t : term) : int =
  match t with
  | Not  e     -> 1 + (size e)
  | Or  (e, f) -> 1 + (size e) + (size f)
  | And (e, f) -> 1 + (size e) + (size f)
  | _            -> 1

let rec ordered (t : term) (e : term) : bool =
  if size t < size e then true else
  if size t > size e then false else
  match t, e with 
  | True, _                        -> true
  | False, True                    -> false
  | False, _                       -> true
  | TFunc, TFunc                   -> true
  | TFunc, True                    -> false
  | TFunc, False                   -> false
  | TFunc, _                       -> true
  | Var   a, Var b                 -> if a = b then raise Tie else a < b
  | Var   _, True                  -> false
  | Var   _, False                 -> false
  | Var   _, TFunc                 -> false
  | Var   _, _                     -> true
  | Not   a, Not b                 -> ordered a b
  | Not   _, And (_, _)            -> true
  | Not   _, Or (_, _)             -> true
  | Not   _, _                     -> false
  | Or (a1, a2), Or (b1, b2)       -> (try ordered a1 b1 with | Tie -> ordered a2 b2) 
  | Or (_, _)  , And (_, _)        -> true
  | Or (_, _), _                   -> false
  | And (a1, a2), And (b1, b2)     -> (try ordered a1 b1 with | Tie -> ordered a2 b2)
  | And (_, _), _                  -> false

let rec prune (t : term) : bool =
  match t with
  | Not   (Not _)    -> true
  | Not   e          -> prune e
  | Or    (True, _)  -> true
  | Or    (_, True)  -> true
  | Or    (False, _) -> true
  | Or    (_, False) -> true
  | Or    (e, f)     -> e = f || prune e  || prune f  || (try not (ordered e f) with | Tie -> false)
  | And   (False, _) -> true
  | And   (_, False) -> true
  | And   (True, _)  -> true
  | And   (_, True)  -> true
  | And   (e, f)     -> e = f || prune e  || prune f  || (try not (ordered e f) with | Tie -> false)
  | _                -> false

let rec leftmost (t : term) : term =
  match t with 
  | True             -> True
  | False            -> True
  | TFunc            -> True
  | Var  _           -> True
  | Or  (e, v)       -> Or (leftmost e, leftmost v)
  | Not  e           -> leftmost e
  | And (e, v)       -> Or (leftmost e, leftmost v)

let next_group (vs : (string list)) (t : term) : term option =
  match t with
  | True             -> Some False
  | False            -> Some TFunc
  | TFunc            -> if ((List.length vs) > 0) then Some (Var (List.hd vs)) else None
  | Var      e       -> (match next_ls vs e with
                         | Some n -> Some (Var (n))
                         | None   -> None)
  | Or       (e, v)  -> Some (Not (Or (leftmost e, leftmost v)))
  | Not  (Or (e, v)) -> Some (And (leftmost e, leftmost v))
  | And      (e, v)  -> Some (Not (And (leftmost e, leftmost v)))
  | Not (And (_, _)) -> None
  | _                -> None

let rec next_column (vs : (string list)) (t : term) : term option =
  match t with 
  | Or (e, v)        -> (match next_column vs e with 
                       | Some n -> Some (Or (n, v))
                       | None   -> 
                         (match next_column vs v with 
                         | Some n -> Some (Or (leftmost e, n))
                         | None   -> next_group vs t))
  | Not (Or (e, v))  -> (match next_column vs e with 
                       | Some n -> Some (Not (Or (n, v)))
                       | None   -> 
                         (match next_column vs v with 
                         | Some n -> Some (Not (Or (leftmost e, n)))
                         | None   -> next_group vs t))
  | And (e, v)       -> (match next_column vs e with 
                       | Some n -> Some (And (n, v))
                       | None   -> 
                         (match next_column vs v with 
                         | Some n -> Some (And (leftmost e, n))
                         | None   -> next_group vs t))
  | Not (And (e, v)) -> (match next_column vs e with 
                       | Some n -> Some (Not (And (n, v)))
                       | None   -> 
                         (match next_column vs v with 
                         | Some n -> Some (Not (And (leftmost e, n)))
                         | None   -> next_group vs t))
  | _                -> next_group vs t

let rec next (vs : (string list)) (t : term) : term =
  (* Var and Not And are rightmost: they jump to next row. 
     Var can be empty which would make TFunc the rightmost*)
  let r = (match t with 
  | TFunc            -> (match next_column vs t with
                        | Some n -> n
                        | None   -> Or (True, True))
  | Var _            -> (match next_column vs t with
                        | Some n -> n
                        | None   -> Or (True, True))
  | Not (And (e, v)) -> (match next_column vs t with
                        | Some n -> n
                        | None   -> if ((size e) <= (size v)) 
                                      then (Or (Or (leftmost e, True), leftmost v))
                                      else (Or (leftmost v, Or (leftmost v, True))))
  | _            -> (match next_column vs t with
                    | Some n -> n
                    | None   -> raise (Failure "Unreachable")))
  in (if prune r then next vs r else r)