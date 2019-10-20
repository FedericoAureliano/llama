exception Tie

let rec next_ls (ls: (string list)) (x : string) : string option = 
  match ls with
    | y::ys -> if ((x = y) && ((List.length ys) > 0)) then Some (List.hd ys) else (next_ls ys x) 
    | _     -> None

type term =
  | Lit   of string
  | Var   of string
  | Plus  of (term * term)
  | Minus of (term * term)
  | Times of (term * term)
  | ITE   of (term * term)

let rec to_string (t : term) : string = 
  match t with
  | Lit    e     -> e
  | Var    e     -> e
  | Plus  (e, f) -> "(+ "      ^ (to_string e) ^ " " ^ (to_string f) ^ ")"
  | Minus (e, f) -> "(- "      ^ (to_string e) ^ " " ^ (to_string f) ^ ")"
  | Times (e, f) -> "(* "      ^ (to_string e) ^ " " ^ (to_string f) ^ ")"
  | ITE   (e, f) -> "(ite ?b " ^ (to_string e) ^ " " ^ (to_string f) ^ ")"

let rec size (t : term) : int =
  match t with
  | Lit    _     -> 1
  | Var    _     -> 1
  | Plus  (e, f) -> 1 + (size e) + (size f)
  | Minus (e, f) -> 1 + (size e) + (size f)
  | Times (e, f) -> 1 + (size e) + (size f)
  | ITE   (e, f) -> 1 + (size e) + (size f)

let rec ordered (t : term) (e : term) : bool =
  if size t < size e then true else
  if size t > size e then false else
  match t, e with 
  | Lit   a, Lit b                 -> if a = b then raise Tie else a < b  
  | Lit   _, _                     -> true
  | Var   _, Lit _                 -> false
  | Var   a, Var b                 -> if a = b then raise Tie else a < b
  | Var   _, _                     -> true
  | Plus  (a1, a2),  Plus (b1, b2) -> (try ordered a1 b1 with | Tie -> ordered a2 b2)
  | Plus  (_, _),  _               -> true
  | Minus (_, _), Plus (_, _)      -> false
  | Minus (a1, a2), Minus (b1, b2) -> (try ordered a1 b1 with | Tie -> ordered a2 b2)
  | Minus (_, _), _                -> true
  | Times (a1, a2), Times (b1, b2) -> (try ordered a1 b1 with | Tie -> ordered a2 b2)
  | Times (_, _), ITE (_, _)       -> true
  | Times (_, _), _                -> false
  | ITE   (a1, a2),   ITE (b1, b2) -> (try ordered a1 b1 with | Tie -> ordered a2 b2)
  | ITE   (_, _), _                -> false

let rec constant (t : term) : bool = 
  match t with
  | Lit    _     -> true
  | Var    _     -> false
  | Plus  (e, f) -> (constant e) && (constant f)
  | Minus (e, f) -> (constant e) && (constant f)
  | Times (e, f) -> (constant e) && (constant f)
  | ITE   (e, f) -> (constant e) && (constant f)

let rec check (t : term) : bool =
  match t with
  | Lit    _         -> true
  | Var    _         -> true
  | Plus  (Lit v, f) -> v <> "0" && check f  && (try ordered (Lit v) f  with | Tie -> true)
  | Plus  (e, Lit v) -> v <> "0" && check e  && (try ordered e (Lit v)  with | Tie -> true)
  | Plus  (e, f)     -> check e  && check f  && (try ordered e f with | Tie -> true)
  | Minus (e, Lit v) -> v <> "0" && check e
  | Minus (e, f)     -> e <> f   && check e  && check f
  | Times (Lit v, f) -> v <> "1" && v <> "0" && check f && (try ordered (Lit v) f with | Tie -> true)
  | Times (e, Lit v) -> v <> "1" && v <> "0" && check e && (try ordered e (Lit v) with | Tie -> true) && constant e
  | Times (e, f)     -> check e  && check f  && (try ordered e f with | Tie -> true) && constant e
  | ITE   (e, f)     -> e <> f   && check e  && check f

let bottom (ls : (string list)) (vs : (string list)) = 
  if List.length ls > 0 then Lit (List.hd ls) else Var (List.hd vs)

let rec leftmost (ls : (string list)) (vs : (string list)) (t : term) : term =
  match t with 
  | Lit    _     -> bottom ls vs
  | Var    _     -> bottom ls vs
  | Plus  (e, v) -> Plus (leftmost ls vs e, leftmost ls vs v)
  | Minus (e, v) -> Plus (leftmost ls vs e, leftmost ls vs v)
  | Times (e, v) -> Plus (leftmost ls vs e, leftmost ls vs v)
  | ITE   (e, v) -> Plus (leftmost ls vs e, leftmost ls vs v)   

let next_group (ls : (string list)) (vs : (string list)) (t : term) : term option =
  match t with
  | Lit    e     -> (match next_ls ls e with
                      | Some n -> Some (Lit (n))
                      | None   -> Some (Var (List.hd vs))) 
  | Var    e     -> (match next_ls vs e with
                      | Some n -> Some (Var (n))
                      | None   -> None)
  | Plus  (e, v) -> Some (Minus (leftmost ls vs e, leftmost ls vs v))
  | Minus (e, v) -> Some (Times (leftmost ls vs e, leftmost ls vs v))
  | Times (e, v) -> Some (ITE (leftmost ls vs e, leftmost ls vs v))
  | _            -> None

let rec next_column (ls : (string list)) (vs : (string list)) (t : term) : term option =
  match t with 
  | Plus (e, v)  -> (match next_column ls vs e with 
                    | Some n -> Some (Plus (n, v))
                    | None   -> 
                      (match next_column ls vs v with 
                      | Some n -> Some (Plus (leftmost ls vs e, n))
                      | None   -> next_group ls vs t))
  | Minus (e, v)  -> (match next_column ls vs e with 
                    | Some n -> Some (Minus (n, v))
                    | None   -> 
                      (match next_column ls vs v with 
                      | Some n -> Some (Minus (leftmost ls vs e, n))
                      | None   -> next_group ls vs t))
  | Times (e, v)  -> (match next_column ls vs e with 
                    | Some n -> Some (Times (n, v))
                    | None   -> 
                      (match next_column ls vs v with 
                      | Some n -> Some (Times (leftmost ls vs e, n))
                      | None   -> next_group ls vs t))
  | ITE (e, v)    -> (match next_column ls vs e with 
                    | Some n -> Some (ITE (n, v))
                    | None   -> 
                      (match next_column ls vs v with 
                      | Some n -> Some (ITE (leftmost ls vs e, n))
                      | None   -> next_group ls vs t))
  | _             -> next_group ls vs t

let rec next (ls : (string list)) (vs : (string list)) (t : term) : term =
  (* Var and ITE are rightmost: they jump to next row. *)
  let r = (match t with 
  | Var _        -> (match next_column ls vs t with
                    | Some n -> n
                    | None   -> Plus (bottom ls vs, bottom ls vs))
  | ITE (e, v)   -> (match next_column ls vs t with
                    | Some n -> n
                    | None   -> if ((size e) <= (size v)) 
                                  then (Plus (Plus(leftmost ls vs e, bottom ls vs), leftmost ls vs v))
                                  else (Plus (leftmost ls vs v, Plus(leftmost ls vs v, bottom ls vs))))
  | _            -> (match next_column ls vs t with
                    | Some n -> n
                    | None   -> raise (Failure "Unreachable")))
  in (if check r then r else next ls vs r)