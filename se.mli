
type comparison =
| Eq
| Lt
| Gt

val compare : int -> int -> comparison

type circuit =
| True
| False
| Var of string
| Not of circuit
| And of circuit * circuit
| Or of circuit * circuit
| Xor of circuit * circuit

val circ_ex1 : circuit

val is_atomic : circuit -> bool

val prc : circuit -> string

val compare_level : int -> int -> bool

val print : circuit -> int -> string

val eqc : circuit -> circuit -> bool

val assign : circuit -> string -> circuit -> circuit

val simp : circuit -> circuit

val msimp : circuit -> int -> circuit

val cofactor : circuit -> string -> circuit -> circuit

val cofactor1 : circuit -> string -> circuit

val cofactor0 : circuit -> string -> circuit

val shannonExpanssion : circuit -> string -> circuit

val sE : circuit -> string -> circuit

val shannonExpanssions : circuit -> string list -> circuit

val sES : circuit -> string list -> circuit

val prSES : circuit -> string list -> int -> string
