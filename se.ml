
type comparison =
| Eq
| Lt
| Gt

(** val compare : int -> int -> comparison **)

let rec compare n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Eq)
      (fun _ -> Lt)
      m)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Gt)
      (fun m' -> compare n' m')
      m)
    n

type circuit =
| True
| False
| Var of string
| Not of circuit
| And of circuit * circuit
| Or of circuit * circuit
| Xor of circuit * circuit

(** val circ_ex1 : circuit **)

let circ_ex1 =
  let x = Var "x" in
  let y = Var "y" in
  let z = Var "z" in
  Or ((Or ((And (x, y)), (And (x, (Not z))))), (And (y, (Or ((And ((Not x),
  z)), (Not z))))))

(** val is_atomic : circuit -> bool **)

let rec is_atomic = function
| Not c0 -> (match c0 with
             | Var _ -> true
             | _ -> false)
| And (x, y) -> if is_atomic x then is_atomic y else false
| Or (_, _) -> false
| Xor (_, _) -> false
| _ -> true

(** val prc : circuit -> string **)

let rec prc c =
  let paren = fun c0 -> (^) "(" ((^) (prc c0) ")") in
  let pr = fun c0 -> if is_atomic c0 then prc c0 else paren c0 in
  (match c with
   | True -> "1"
   | False -> "0"
   | Var v -> v
   | Not x -> (^) (pr x) "'"
   | And (x, y) -> (^) (pr x) ((^) "" (pr y))
   | Or (x, y) -> (^) (prc x) ((^) "+" (prc y))
   | Xor (x, y) -> (^) (pr x) ((^) "(+)" (pr y)))

(** val compare_level : int -> int -> bool **)

let compare_level inner out =
  match compare inner out with
  | Lt -> true
  | _ -> false

(** val print : circuit -> int -> string **)

let rec print c last_level =
  match c with
  | True -> "1"
  | False -> "0"
  | Var v -> v
  | Not x ->
    if compare_level (succ (succ (succ (succ 0)))) last_level
    then (^) "(" ((^) (print x (succ (succ (succ (succ 0))))) ((^) "'" ")"))
    else (^) (print x (succ (succ (succ (succ 0))))) "'"
  | And (x, y) ->
    if compare_level (succ (succ (succ 0))) last_level
    then (^) "("
           ((^) (print x (succ (succ (succ 0))))
             ((^) "" ((^) (print y (succ (succ (succ 0)))) ")")))
    else (^) (print x (succ (succ (succ 0))))
           ((^) "" (print y (succ (succ (succ 0)))))
  | Or (x, y) ->
    if compare_level (succ 0) last_level
    then (^) "("
           ((^) (print x (succ 0)) ((^) "+" ((^) (print y (succ 0)) ")")))
    else (^) (print x (succ 0)) ((^) "+" (print y (succ 0)))
  | Xor (x, y) ->
    if compare_level (succ (succ 0)) last_level
    then (^) "("
           ((^) (print x (succ (succ 0)))
             ((^) "(+)" ((^) (print y (succ (succ 0))) ")")))
    else (^) (print x (succ (succ 0))) ((^) "(+)" (print y (succ (succ 0))))

(** val eqc : circuit -> circuit -> bool **)

let rec eqc c1 c2 =
  match c1 with
  | True -> (match c2 with
             | True -> true
             | _ -> false)
  | False -> (match c2 with
              | False -> true
              | _ -> false)
  | Var v -> (match c2 with
              | Var w -> (=) v w
              | _ -> false)
  | Not x -> (match c2 with
              | Not y -> eqc x y
              | _ -> false)
  | And (x1, y1) ->
    (match c2 with
     | And (x2, y2) -> if eqc x1 x2 then eqc y1 y2 else false
     | _ -> false)
  | Or (x1, y1) ->
    (match c2 with
     | Or (x2, y2) -> if eqc x1 x2 then eqc y1 y2 else false
     | _ -> false)
  | Xor (x1, y1) ->
    (match c2 with
     | Xor (x2, y2) -> if eqc x1 x2 then eqc y1 y2 else false
     | _ -> false)

(** val assign : circuit -> string -> circuit -> circuit **)

let rec assign c var val0 =
  let ass = fun c0 -> assign c0 var val0 in
  (match c with
   | Var v -> if (=) v var then val0 else c
   | Not x -> Not (ass x)
   | And (x, y) -> And ((ass x), (ass y))
   | Or (x, y) -> Or ((ass x), (ass y))
   | Xor (x, y) -> Xor ((ass x), (ass y))
   | _ -> c)

(** val simp : circuit -> circuit **)

let rec simp c = match c with
| Not x ->
  (match x with
   | True -> False
   | False -> True
   | Not x0 -> simp x0
   | _ -> Not (simp x))
| And (x, y) ->
  (match x with
   | True -> (match y with
              | False -> False
              | _ -> simp y)
   | False -> False
   | Var _ ->
     (match y with
      | True -> simp x
      | False -> False
      | Not y0 -> if eqc x y0 then False else And ((simp x), (simp y))
      | _ -> And (x, (simp y)))
   | Not x0 ->
     (match y with
      | True -> simp x
      | False -> False
      | Not y0 -> if eqc x y0 then False else And ((simp x), (simp y))
      | _ -> if eqc x0 y then False else And ((simp x), (simp y)))
   | _ ->
     (match y with
      | True -> simp x
      | False -> False
      | Var _ -> And ((simp x), y)
      | Not y0 -> if eqc x y0 then False else And ((simp x), (simp y))
      | _ -> And ((simp x), (simp y))))
| Or (x, y) ->
  (match x with
   | True -> True
   | False -> (match y with
               | True -> True
               | _ -> simp y)
   | Var x0 ->
     (match y with
      | True -> True
      | False -> simp x
      | Not y0 ->
        (match y0 with
         | Var y1 -> if (=) x0 y1 then True else c
         | _ -> Or (x, (simp y)))
      | _ -> Or (x, (simp y)))
   | Not x0 ->
     (match x0 with
      | Var y0 ->
        (match y with
         | True -> True
         | False -> simp x
         | Var x1 -> if (=) x1 y0 then True else c
         | Not y1 -> if eqc x y1 then True else Or ((simp x), (simp y))
         | _ -> if eqc x0 y then True else Or ((simp x), (simp y)))
      | _ ->
        (match y with
         | True -> True
         | False -> simp x
         | Var _ -> Or ((simp x), y)
         | Not y0 -> if eqc x y0 then True else Or ((simp x), (simp y))
         | _ -> if eqc x0 y then True else Or ((simp x), (simp y))))
   | _ ->
     (match y with
      | True -> True
      | False -> simp x
      | Var _ -> Or ((simp x), y)
      | Not y0 -> if eqc x y0 then True else Or ((simp x), (simp y))
      | _ -> Or ((simp x), (simp y))))
| Xor (x, y) ->
  (match x with
   | True -> Not y
   | False -> (match y with
               | True -> Not x
               | _ -> y)
   | _ ->
     (match y with
      | True -> Not x
      | False -> x
      | _ -> if eqc x y then False else Xor ((simp x), (simp y))))
| _ -> c

(** val msimp : circuit -> int -> circuit **)

let rec msimp c n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> c)
    (fun m -> msimp (simp c) m)
    n

(** val cofactor : circuit -> string -> circuit -> circuit **)

let cofactor c x v =
  simp (assign c x v)

(** val cofactor1 : circuit -> string -> circuit **)

let cofactor1 c x =
  cofactor c x True

(** val cofactor0 : circuit -> string -> circuit **)

let cofactor0 c x =
  cofactor c x False

(** val shannonExpanssion : circuit -> string -> circuit **)

let shannonExpanssion c x =
  let c1 = cofactor1 c x in
  let c0 = cofactor0 c x in
  Or ((And ((Var x), c1)), (And ((Not (Var x)), c0)))

(** val sE : circuit -> string -> circuit **)

let sE =
  shannonExpanssion

(** val shannonExpanssions : circuit -> string list -> circuit **)

let rec shannonExpanssions c = function
| [] -> c
| x::tl -> let c' = simp (shannonExpanssion c x) in shannonExpanssions c' tl

(** val sES : circuit -> string list -> circuit **)

let sES =
  shannonExpanssions

(** val prSES : circuit -> string list -> int -> string **)

let prSES c vars n =
  prc (msimp (sES c vars) n)
