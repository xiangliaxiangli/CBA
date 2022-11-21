open Se
open Printf

let test () =
    printf "%s = %s\n" (prc circ_ex1) (prSES circ_ex1 ["x"; "z"; "y"] 4);