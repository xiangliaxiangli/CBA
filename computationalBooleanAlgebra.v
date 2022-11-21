
Require Import Bool.
Require Import boolAlgebra.
Require Import String.

(* This version add xor to circuit. *)

(* Shannon Expansion
  F(x1,x2,..,xi, ..,xn) =
  F(x1,x2,..,xi=0, ..,xn) + F(x1,x2,..,xi=1, ..,xn)
*)
Close Scope bool_scope.
Open Scope gate_scope.
Lemma shannon_expansion : forall (P:bool->bool) (x:bool),
  P x = ((! x && P false) || (x && P true)). 
intros. destruct x.
+  (* case x = 1 *)
   (* P true = ! true && P false || true && P true *)
simpl. (* P true = P true *)
reflexivity.
+ (* case x = 0 *)
  (* P false = ! false && P false || false && P true *)
  simpl.  (* P false = P false || false *)
  rewrite bounded_false_or. reflexivity.
Qed.

(* Shannon expansion second form. *)
Lemma shannon_expansion_and_or : forall (P:bool->bool) (x:bool),
  P x = ((! x || P true) && (x || P false)). 
intros. destruct x.
+ (* x=1 *) simpl.  rewrite bounded_true_and. reflexivity.
+ (* x=0 *) simpl. reflexivity.
Qed.


(* compute shannnon expansion. *)
Definition se (P:bool->bool) (x:bool) : bool :=
  ((! x && P false) || (x && P true)).

Section Shannon_expansion_example.

Variables x y z : bool.
(* a circuit exanple: F(x,y,z) = xy+xz'+y(x'z+z') *)
Let se_ex1 := x && y || x && !z || y && (!x && z || !z).

Let se_ex1_true :=  true && y || true && ! z || y && (! true && z || ! z).
Lemma se_ex1_true_simp : se_ex1_true =   y ||  ! z || y &&  ! z.
unfold se_ex1_true. rewrite ?bounded_true_and2.
rewrite negation_true. rewrite bounded_false_and2.
rewrite bounded_false_or2. reflexivity. Qed.

(* example of calculating cofactors. *)
Let se_ex2 := fun x => 
   x && y || x && !z || y && (!x && z || !z).

Compute se_ex2 true.  (* unfold too much, get a long if expression *)
(* restrict unfolding 1: use Opaque to disable unfolding *)
Opaque org andg notg. (* disable unfolding of org andg notg *)
Opaque orb andb negb. (* disable unfolding of orb andb negb *)
(* restrict unfolding 2: use Eval cbv in *)
Compute se_ex2 true.  (* unfold too much, get a long if expression *)
Eval cbv in (se_ex2 true).
Eval cbv in (se_ex2 false).

(* refinment towards simplified cofactors. *)
Lemma se_ex2_true : (se_ex2 true) = true && y || true && ! z || y && (! true && z || ! z).
(* reflexivity. *)
 truth_table_tactic2 y z. Qed.
Reset se_ex2_true.

(* refinment *)
Lemma se_ex2_true_aux : (se_ex2 true) =  y ||  ! z || y &&  ! z.
 reflexivity.
Qed.

(* Shannon cofactor (se_ex2 true) *)
Lemma se_ex2_true : (se_ex2 true) =  y ||  ! z .
 truth_table_tactic2 y z. Qed.

(* derive negative cofactor (se_ex2 false) *)
Eval cbv in (se_ex2 false).
Lemma se_ex2_false : (se_ex2 false) = 
false && y || false && ! z || y && (! false && z || ! z).
reflexivity.
Abort.
Lemma se_ex2_false_aux : (se_ex2 false) =  y && (z || ! z).
reflexivity.
Qed.
Lemma se_ex2_false : (se_ex2 false) =  y .
rewrite se_ex2_false_aux. destruct y,z; reflexivity.
Qed.
(* summary: se_ex2 true = y || !z; se_ex2 false = y *)

(** full Shannon Expansion **)

Eval compute in (se se_ex2 x).
Eval cbv delta beta in (se se_ex2 x).
Eval lazy beta delta in (se se_ex2 x).


(** tactic for boolean equality with 1 argument. *)
Ltac truth_table_tactic1 a := 
  intros;  destruct a;  trivial.

(** tactic for boolean equality with 2 arguments. *)
Ltac truth_table_tactic2 a b := 
  intros;  destruct a, b; trivial.

(** tactic for boolean equality with 3 arguments. *)
Ltac truth_table_tactic3 a b c := 
  intros; destruct a, b, c; easy.

Lemma se_ex2_simpl : (se se_ex2 x) =
(! x && org (false && y || false && ! z) (y && (! false && z || ! z))
        || x && org (true && y || true && ! z) (y && (! true && z || ! z))).
reflexivity.
Abort.
Lemma se_ex2_simpl : (se se_ex2 x) =
(! x && (y && ( z || ! z))
        || x && org ( y || ! z) (y && (! true && z || ! z))).
reflexivity.
Abort.
(* result of Shannon expansion of se_ex2. *)
Lemma se_ex2_simpl_aux : (se se_ex2 x) =
   (! x && (y && ( z || ! z))
        || x && (( y || ! z) || (y && ! z))).
reflexivity.
Qed.

Lemma se_ex2_simpl : (se se_ex2 x) =
    (! x && y  || x && (( y || ! z) || (y && ! z))).
rewrite se_ex2_simpl_aux. rewrite orb_neg_b.
rewrite andb_b_true.   reflexivity.
Abort.

(* automatic verify the simplified Shannon Expansion. *)
Lemma se_ex2_simpl : (se se_ex2 x) =
    (! x && y  || x && ( y || ! z)).
truth_table_tactic3 x y z.
Qed.


(* although not very automatic, but it helps refinements and verifies the result. *)


End Shannon_expansion_example.

Section Circuit_structure.

Inductive Circuit :=
  | True  : Circuit
  | False : Circuit
  | Var   : string -> Circuit
  | Not : Circuit -> Circuit
  | And : Circuit -> Circuit -> Circuit
  | Or  : Circuit -> Circuit -> Circuit
  | Xor : Circuit -> Circuit -> Circuit
.

(* x && ! y *)
Example cirt0 := And (Var "x") (Not (Var "y")).

End Circuit_structure.

Declare Scope circ_scope.

Infix "||"  := Or   (at level 50, left associativity)  : circ_scope.
Infix "&&"  := And  (at level 40, left associativity)  : circ_scope.
Infix "(+)" := Xor  (at level 42, left associativity)  : circ_scope.

Notation "@ x" := (Var x) (at level 35, right associativity)  : circ_scope.
Notation "! x" := (Not x) (at level 35, right associativity)  : circ_scope.

Open Scope circ_scope.

(* first version of circuit printing function. *)
Section prc1_sec.

Example cirt0' := (@"x") && !(@"y").
Print cirt0'.

Let x := @"x".
Let y := @"y".
Let z := @"z".

Definition oneOut_cir := Or (Var "a") (And (Var "b") (Var "c")).

Let a := @"a".
Let b := @"b".
Let c := @"c".
Definition oneOut := a || (b && c).

Definition circ_ex1 := x && y || x && !z || y && (!x && z || !z).
Definition circ_ex2 := z && (x (+) y) && (x || y).

(* circuit printer version 1. Let makes the definition local to the section. *)
Let Fixpoint prc (c:Circuit) : string :=
  match c with
  | True  => "1"
  | False => "0"
  | Var v => v
  | Not x =>  (prc x)++"'"
  | And x y => (prc x) ++ "" ++ (prc y)
  | Or  x y => "("++(prc x) ++ "+" ++ (prc y) ++ ")"
  | Xor x y => "("++(prc x) ++ "(+)" ++ (prc y) ++ ")"
end.
(* problem with prc first version: missing required parenthesis: *)

Compute (prc circ_ex1). (* "xy+xz'+yx'z+z'" *)
Compute (prc circ_ex2).
End prc1_sec.

(* second version of prc. *)
Section prc2_sec.

(* return true if the circuit expression does not need parenthesis. *)
Fixpoint is_atomic (c:Circuit) : bool :=
  match c with
  | True  => true
  | False => true
  | Var v => true
  | Not (Var v) => true
  | And x y => is_atomic x && is_atomic y
  | _ => false
end.
 
(* circuit printer version 2. *)
Let Fixpoint prc (c:Circuit) : string :=
  match c with
  | True  => "1"
  | False => "0"
  | Var v => v
  | Not x => if is_atomic x then (prc x)++"'"
     else "("++(prc x)++")'"
  | And x y => if andb (is_atomic x) (is_atomic y)
     then (prc x) ++ "" ++ (prc y)
     else "("++(prc x) ++ "" ++ (prc y)++")"
  | Or  x y  => "("++(prc x) ++ "+" ++ (prc y)++")"
  | Xor  x y => "("++(prc x) ++ "(+)" ++ (prc y)++")"

end.

Compute (prc circ_ex1). (* "(xy+xz'(yx'z+z'))" *)
Compute (prc circ_ex2).

End prc2_sec.


(* final version of prc. *)
Section Circuit_printing.

(* circut printer version 3. *)
(* convert a circuit to a string for readable output. *)
Fixpoint prc (c:Circuit) : string :=
  (* %string should be added here otherwise "" and ++ are not acceptable. *)
  let paren c := ("(" ++ (prc c) ++ ")")%string in
  let pr c := if is_atomic c then prc c else paren c in 
  match c with
  | True  => "1"
  | False => "0"
  | Var v => v
  | Not x => (pr x)++"'"  (* distinguish NOT,AND from Or Xor *)
  | And x y => (pr x) ++ "" ++ (pr y)
  | Or  x y => (prc x) ++ "+" ++ (prc y)
  | Xor x y => (pr x) ++ "(+)" ++ (pr y)
end.
 
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc circ_ex2). (* "(z(x(+)y))(x+y)" *)
(* ok for this example, is it correct for all cases? 
   Left for further investigation, stop here. *) 

End Circuit_printing.

Section Circuit_printing_4.

(* circuit printer version 4 *)
(* Nat.compare : nat -> nat -> comparison 对比两个数字的大小 *)
Definition compare_level (inner:nat) (out:nat) : bool :=
  match (Nat.compare inner out) with
  | Lt => true
  | _ => false
end.

Fixpoint print (c:Circuit) (last_level:nat) : string :=
  match c with
  | True => "1"
  | False => "0"
  | Var v => v
  | Not x => if compare_level 4 last_level then 
             "(" ++ (print x 4) ++ "'" ++ ")"
             else (print x 4) ++ "'"
  | And x y => if compare_level 3 last_level then
             "(" ++ (print x 3) ++ "" ++ (print y 3) ++ ")"
             else (print x 3) ++ "" ++ (print y 3)
  | Or x y => if compare_level 1 last_level then
             "(" ++ (print x 1) ++ "+" ++ (print y 1) ++ ")"
             else (print x 1) ++ "+" ++ (print y 1)
  | Xor x y => if compare_level 2 last_level then
             "(" ++ (print x 2) ++ "(+)" ++ (print y 2) ++ ")"
             else (print x 2) ++ "(+)" ++ (print y 2)
end.

 
Compute (print circ_ex1 0). (* "xy+xz'+y(x'z+z')" *)
Compute (print circ_ex2 0). (* "(z(x(+)y))(x+y)" *)

(* printer_4 test *)
Let x := @"x".
Let y := @"y".
Let z := @"z".
Definition circ_ex3 := x && (y || z).
Compute (print circ_ex3 0).
Definition circ_ex4 := x && y || z.
Compute (print circ_ex4 0).
Definition circ_ex5 := x && y (+) z.
Compute (print circ_ex5 0).
(* 最开始定义Circuit的时候Xor和or的运算关系好像定义的有点问题 *)
Definition circ_ex6 := x && y || x && !z || y && (!x && z || !z) && x (+) y.
Compute (print circ_ex5 0).
(* ok for this example, is it correct for all cases? 
   Left for further investigation, stop here. *) 

End Circuit_printing_4.

(* calculate Shannon Expansion w.r.t. a single variable. *)
Section Shannon_Expansion_on_one_variable.

(** Compute Shannon Expansion on circuit. 
1) eqc: compare the equality of two circutis;
2) assign: substitute a variable by a value in a circuit;
3) simp: simplify a circuit;
4) cofactor: calculate the cofactor of a circuit;
4.1) cofactor0: the cofactor w.r.t 0;
4.2) cofactor1: the cofactor w.r.t 1;
5) ShannonExpansion: the Shannon Expansion of a circuit.
**)
Let c1 := And (Var "x") False.
Let c2 := And (Var "x") False.
Check c1=c2.
Fail Check if c1=c2 then true else false.
Lemma c1eqc2 : c1 = c2.
reflexivity. Qed.

(* equality of two circuits. *)
Fixpoint eqc (c1:Circuit) (c2:Circuit) : bool :=
  match c1,c2 with
  | True,  True  => true
  | False, False => true
  | Var v, Var w => String.eqb v w
  | Not x, Not y => eqc x y
  | And x1 y1, And x2 y2 => andb (eqc x1 x2) (eqc y1 y2)
  | Or  x1 y1, Or x2 y2  => andb  (eqc x1 x2) (eqc y1 y2)
  | Xor x1 y1, Xor x2 y2 => andb  (eqc x1 x2) (eqc y1 y2)
  | _,_ => false
end.
(* Note that this is syntactic equality, not semantic equality, so
   1) Not (True) and False are not equal. 
   2) we can prove "reflect (c1=c2) (eqc c1 c2)"
*)

Open Scope circ_scope.
Open Scope string_scope.

(* There are more than one methods to define assign.
The first implementation contains simplifications, but it 
is hard for property proving.
*)
Fixpoint assign (c:Circuit) (var:string) (val:Circuit) : Circuit :=
 let ass c := assign c var val in
  match c with
  | True  => c
  | False => c
  | Var v => if (String.eqb v var) then val else c
  | Not x => if (eqc x True) 
             then False 
             else if (eqc x False) 
             then True else Not (ass x)
  | And x y => 
     let x1 := ass x in
     let y1 := ass y in
       if eqc x1 False then False else
       if eqc y1 False then False else
       if eqc x1 True then y1 else
       if eqc y1 True then x1
       else And x1 y1

  | Or x y => 
     let x1 := ass x in
     let y1 := ass y in
       if eqc x1 True then True else
       if eqc y1 True then True else
       if eqc x1 False then y1 else
       if eqc y1 False then x1 
       else Or x1 y1

  | Xor x y => 
     let x1 := ass x in
     let y1 := ass y in
       if eqc x1 y1 then False else
       if eqc x1 True then True else
       if eqc y1 True then True else
       if eqc x1 False then y1 else
       if eqc y1 False then x1 
       else Xor x1 y1

end.
(* With this definition, properties like assign_and below will 
   be diffcult to prove, or the proof will be quite lengthy.
   By using a simpler definition below without any simplification,
   the proofs become much simpler. *)
Reset assign.

(* replace a variable with a value. *)
Fixpoint assign (c:Circuit) (var:string) (val:Circuit) : Circuit :=
 let ass c := assign c var val in
  match c with
  | True  => c
  | False => c
  | Var v => if (String.eqb v var) then val else c
  | Not x => Not (ass x)
  | And x y => And (ass x) (ass y)
  | Or x y  => Or (ass x) (ass y)
  | Xor x y => Xor (ass x) (ass y)
end.

Let se_ex1xt := assign circ_ex1 "x" True.
Compute (prc se_ex1xt).
(* "1y+1z'+y((1')z+z')" *)
Let se_ex2xt := assign circ_ex2 "x" True.
Compute (prc se_ex2xt).
(* "(z(1(+)y))(1+y)" *)

(* similar to the situation of assign, property proof for
   the above simp is hard, we try to use a simpler version
   to make property proof easier. We need to prove that
   simp keeps the semantics of the circuit. This can b*)

(* circuit simplification, incomplete. *)
Fixpoint simp (c:Circuit) : Circuit :=
  match c with
  | True  => c
  | False => c
  | Var v => c
  | Not True    => False
  | Not False   => True
  | Not (Not x) => simp x
  | Not x => Not (simp x)
  | And False _ | And _ False => False (* 0*y=y*0=0 *)
  | And True y | And y True => simp y  (* 1*y=y*1=y *)

  | And x ((Not y) as z) => 
     if eqc x y then False else And (simp x) (simp z)
  | And ((Not x) as z) y => 
     if eqc x y then False else And (simp z) (simp y)

  | And ((Var _) as x) y => And x (simp y)  
  | And x ((Var _) as y) => And (simp x) y  

  | And x y => And (simp x) (simp y)

  | Or True _       (* 1+y=1 *)
  | Or _ True  => True        (* x+1=1 *)
  | Or False y => simp y      (* 0+y=y *)
  | Or x False => simp x      (* x+0=x *)

  | Or (Var x) (Not (Var y)) 
  | Or (Not (Var y)) (Var x) => if x =? y then True else c
  | Or ((Var _) as x) y => Or x (simp y)  
  | Or x ((Var _) as y) => Or (simp x) y  
  | Or x ((Not y) as z) => 
     if eqc x y then True else Or (simp x) (simp z)
  | Or ((Not x) as z) y => 
     if eqc x y then True else Or (simp z) (simp y) 
  | Or x y => Or (simp x) (simp y)
  

  | Xor True y  => Not y        (* 1(+)y=y' *)
  | Xor y True  => Not y        (* y(+)1=y' *)
  | Xor False y => y            (* 0(+)y=y *)
  | Xor y False => y            (* y(+)0=y *)

  | Xor x y     => if eqc x y then False 
                   else Xor (simp x) (simp y)
end.


Print simp.

Compute simp (@"x" && !@"x").
Compute simp (@"x" || !@"x").

Compute (prc se_ex1xt). (* = "1y+1z'+y((1')z+z')" *)
Compute (prc (simp se_ex1xt)). 
(* "y+z'+y(0z+z')" *)
Compute (prc (simp (simp se_ex1xt))). 
(*  = "y+z'+y(0+z')" *)
Compute (prc (simp (simp (simp se_ex1xt)))). 
(* "y+z'+yz'" *)

(* multiple pass simplification. *)
Fixpoint msimp (c:Circuit) (n:nat) : Circuit :=
  match n with
    O => c
   | S m => msimp (simp c) m
  end.
Compute (prc (msimp se_ex1xt 3)). (*  "y+z'+yz'" *)

(* calculate cofactor of a circuit c w.r.t. an assignment x=b. *)
Definition cofactor (c:Circuit) (x:string) (v:Circuit) :=
  simp (assign c x v).

Definition cofactor1 (c:Circuit) (x:string) :=
  cofactor c x True.

Definition cofactor0 (c:Circuit) (x:string) :=
  cofactor c x False. 

Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (cofactor1 circ_ex1 "x")). (* "y+z'+y(0z+z')" *)
Compute (prc (cofactor0 circ_ex1 "x")). (* "0+0+y(1z+z')"  *)
Compute (prc (simp (cofactor1 circ_ex1 "x"))). (* "y+z'+y(0z+z')" *)
Compute (prc (simp (cofactor0 circ_ex1 "x"))). (* "0+0+y(1z+z')"  *)
Compute (prc (simp (simp (cofactor1 circ_ex1 "x")))). (* "y+z'+yz'" *)
Compute (prc (simp (simp (cofactor0 circ_ex1 "x")))). (* "y(z+z')" *)
Compute (prc (msimp (cofactor1 circ_ex1 "x") 2)). (* "y+z'+yz'" *)
Compute (prc (msimp (cofactor0 circ_ex1 "x") 3)). (* "y" *)

(* Shannon Expansion on circuit c w.r.t. a variable x. *)
Definition ShannonExpanssion (c:Circuit) (x:string) :=
  let c1 := cofactor1 c x in
  let c0 := cofactor0 c x in
   (@ x && c1 || (!(@ x) && c0)).
Definition SE := ShannonExpanssion. 

Compute (prc circ_ex1). (*  "xy+xz'+y(x'z+z')" *)
Compute (prc (SE circ_ex1 "x")).
(* = "x(y+z'+y(0z+z'))+x'(0+0+y(1z+z'))" *)
Compute (prc (msimp (SE circ_ex1 "x") 3)).
(* "x(y+z'+yz')+x'y" *)

(* The verification of Shannon expansion based on Circuir structure *)

End Shannon_Expansion_on_one_variable.

Require Import List.
Import ListNotations. (* open the notation module in List. *)

Section Shannon_Expansion_multiple_variables.
(*
1) Shannon Expansion on list of variables;
2) extract the list of all variables in a circuit;
3) Shannon Expanssion on all variables of a circuit.
*)

(* version 1.0 of Shannon Expansions on multiple variables, will be replaced. *)
(* 1) Shannon Expanssions w.r.t. a var list. *)
Fixpoint ShannonExpanssions (c:Circuit) (vars:list string) : Circuit :=
  match vars with
  | [ ] => c
  | x::tl =>
    let c1 := cofactor1 c x in
    let c0 := cofactor0 c x in
    let s1 := ShannonExpanssions c1 tl in
    let s0 := ShannonExpanssions c0 tl in
    simp (@ x && s1 || (!(@ x) && s0))
  end.
Definition SES := ShannonExpanssions.


Open Scope string_scope. (* to allow ["x"] *)
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (SE  circ_ex1 "x")). 
(* = "x(y+z'+y(0z+z'))+x'(0+0+y(1z+z'))" *)
Compute (prc (msimp (SE  circ_ex1 "x") 3)). (* "x(y+z'+yz')+x'y" *)
Compute (prc (SES circ_ex1 ["x"])). (* "x(y+z'+y(0+z'))+x'(0+y(z+z'))" *)
Compute (prc (SES circ_ex1 ["y"])). (* "y(x+xz'+x'z+z')+y'xz'" *)
Let c1 := cofactor1 circ_ex1 "x".
Let c0 := cofactor0 circ_ex1 "x". 
Compute (prc c1). (* "y+z'+y(0z+z')" *)
Compute (prc c0). (* "0+0+y(1z+z')"  *)
Compute (prc (cofactor1 c1 "y")). (* "1+0+z'" *)
Compute (prc (cofactor0 c1 "y")). (* "z'+0" *)
Compute (prc (SE c1 "y")).        (* "y(1+0+z')+y'(z'+0)" *)
Compute (prc (cofactor1 c0 "y")). (*  "0+z+z'" *)
Compute (prc (cofactor0 c0 "y")). (* 0+0 *)
Compute (prc (SE c0 "y")).        (* "y(0+z+z')+y'(0+0)" *)
Compute (prc (SES circ_ex1 ["x"; "y"])). (* "x(y+y'z')+x'(y+0)" *)
Compute (prc (SES circ_ex1 ["x"; "y"; "z"])). (* "x(y+y'z')+x'(y+0)" *)
Compute (prc (msimp (SES circ_ex1 ["x"; "y"; "z"]) 2)).
 (* x(y+y'z')+x'y *)

Reset ShannonExpanssions.

(* version 2.0 of Shannon Expansions on multiple variables *)

Fixpoint ShannonExpanssions (c:Circuit) (vars:list string) : Circuit :=
  match vars with
  | [ ] => c
  | x::tl =>
    let c' := simp (ShannonExpanssion c x) in
      ShannonExpanssions c' tl 
  end.
Definition SES := ShannonExpanssions.

Open Scope string_scope. (* to allow ["x"] *)
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (SE  circ_ex1 "x")). 
(* = "x(y+z'+y(0z+z'))+x'(0+0+y(1z+z'))" *)
Compute (prc (msimp (SE  circ_ex1 "x") 3)). (* "x(y+z'+yz')+x'y" *)
Compute (prc (SES circ_ex1 ["x"; "y"])). (* "y(x1+x')+y'(xz'+0)" *)

Definition prSES (c:Circuit) (vars: list string) (n:nat) : string :=
  prc (msimp (SES c vars) n).

Compute prSES circ_ex1 ["x"; "y"] 3. (* "y+y'xz'" *)

Compute (prc (SES circ_ex1 ["x"; "y"; "z"])). (*  "z(y1+y'0)+z'(y1+y'x)" *)
Compute prSES circ_ex1 ["x"; "y"; "z"] 2. (* "zy+z'(y+y'x)" *)

Compute prSES circ_ex1 ["y"; "x"] 3. (* "x(y+y'z')+x'y" *)
Compute prSES circ_ex1 ["z"; "x"] 3. (* "x(zy+z')+x'(zy+z'y)" *)
Compute prSES circ_ex1 ["x"; "z"] 3. (* "z(xy+x'y)+z'(x+x'y)" *)
Compute prSES circ_ex1 ["y"; "z"] 3. (* "zy+z'(y+y'x)" *)

Compute prSES circ_ex1 ["z"; "y"] 3. (* "y+y'z'x" *)

Compute prSES circ_ex1 ["y"] 3. (* "x(y+y'z')+x'y" *)
Compute prSES circ_ex1 ["z"] 3. (* "x(y+y'z')+x'y" *)

Compute prSES circ_ex1 ["x"; "z"; "y"] 4. (* "y+y'z'x" *)
Compute prSES circ_ex1 ["y"; "x"; "z"] 3. (* "z(xy+x'y)+z'(x+x'y)" *)
Compute prSES circ_ex1 ["y"; "z"; "x"] 3. (* "x(zy+z')+x'(zy+z'y)" *)

(* verify x(y+z'+yz')+x'y = y+y'z'x = y+z'x *)
Open Scope gate_scope.
Variables x y z : bool.
(* a circuit exanple: F(x,y,z) = xy+xz'+y(x'z+z') *)
Let se_ex1 := (x && y || x && !z || y && (!x && z || !z)).
(* se_ex2 = (msimp (SEC circ_ex1 ["x";"y"] 3 = "y+y'xz'" *)
Let se_ex2 := y || !y && x && !z.
Let se_ex3 := y || x && !z. (* simpliest form ! *)
Lemma ex1_eq_ex2 : se_ex1 = se_ex2.

truth_table_tactic3 x y z. Qed.

Lemma ex1_eq_ex3 : se_ex1 = se_ex3.
truth_table_tactic3 x y z. Qed.


(* Found a simplified version of se_ex1. *)

(* 2) extract all variables in the circuit. *)

(* return true if an element is a member of a list. *)
Fixpoint mem {A:Set} (eq_dec:A->A->bool) (e:A) (s:list A) : bool :=
  match s with
  | hd::tl => 
      if eq_dec e hd then true else mem eq_dec e tl
  | [] => false
  end.

(* return true if an element is a member of a boolean list. *)
Definition bmem (b:bool) (s:list bool) : bool :=
  mem Bool.eqb b s.

(* return true if an element is a member of a string list. *)
Definition smem (b:string) (s:list string) : bool :=
  mem String.eqb b s.

(* add an element to a string list. *)
Definition add_str_set (e:string) (s:list string) : list string :=
  if smem e s then s else e::s.

(* assistant function to return a list of all variables in a circuit. *)
Fixpoint vic (c:Circuit) (vars : list string) : list string :=
  match c with
  | True  => []
  | False => []
  | Var v => add_str_set v vars
  | Not x => vic x vars 
  | And x y => vic y (vic x vars)
  | Or x y  => vic y (vic x vars)
  | Xor x y => vic y (vic x vars)
end.

(* return a list of all variables in a circuit. *)
Definition varsInCircuit (c:Circuit) : list string :=
  vic c [].

(* 3) Shannon Expansion on all variables of a circuit. *)
Definition ShannonExpansion_all (c:Circuit) : Circuit :=
  let vars := varsInCircuit c in
    ShannonExpanssions c vars.
Definition SEA := ShannonExpansion_all.
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (cofactor1 circ_ex1 "x")). (* "y+z'+yz'" *)
Compute (prc (cofactor0 circ_ex1 "x")). 
Definition sea_circ_ex1 := SEA circ_ex1. 
Compute (prc sea_circ_ex1). (* zy+z'(y+y'x) *)
Compute (prc (msimp sea_circ_ex1 3)). (*  = "x(y+y'z')+x'y" *)
End Shannon_Expansion_multiple_variables.


(** define sum of product. **)
Section Sum_of_product.

(* Problem: recursive mode for sop is not acceptable. *)
Fail Fixpoint sop (c:Circuit) : Circuit :=
  match c with
  | Not (And x y)  => Or  (sop (Not x)) (sop (Not y))
  | Not (Or x y)   => And (sop (Not x)) (sop (Not y))
  | And (Or x y) z => Or (sop (And x z)) (sop (And y z))
  | And x (Or y z) => Or (sop (And x y)) (sop (And x z))
  | Or x y         => Or (sop x) (sop y)
  | _ => c
end.

Fixpoint sop (c:Circuit) (n:nat) {struct n} : Circuit :=
  match n with
   O => c
   | S m => 
      let sop c := sop c m in
      match c with
      | Not (And x y)  => Or  (sop (Not x)) (sop (Not y))
      | Not (Or x y)   => And (sop (Not x)) (sop (Not y))
      | And (Or x y) z => Or (sop (And x z)) (sop (And y z))
      | And x (Or y z) => Or (sop (And x y)) (sop (And x z))
      | Or x y         => Or (sop x) (sop y)
      | _                  => c (* Xor should be added later *)
      end
end.
(* WARNING: correctness not proved yet *)

Open Scope string_scope.
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (sop circ_ex1 2)). 
(* "xy+xz'+yx'z+yz'" *)

Compute (prc (msimp (SE  circ_ex1 "x") 3)). (* "x(y+z'+yz')+x'y" *)
Compute (prc (sop (msimp (SE  circ_ex1 "x") 3) 3)). 
(* = "xy+xz'+xyz'+x'y" *)

Fixpoint pos (c:Circuit) (n:nat) {struct n} : Circuit :=
  match n with
   O => c
   | S m => 
      let pos c := pos c m in
      match c with
      | Not (And x y)  => Or  (pos (Not x)) (pos (Not y))
      | Not (Or x y)   => And (pos (Not x)) (pos (Not y))
      | Or (And x y) z => And (pos (Or x z)) (pos (Or y z))
      | Or x (And y z) => And (pos (Or x y)) (pos (Or x z))
      | And x y         => And (pos x) (pos y)
      | _                  => c (* Xor should be added later *)
      end
end.

(* "x(y+z'+yz')+x'y" *)
Compute (prc (pos (msimp (SE  circ_ex1 "x") 3) 3)). 

End Sum_of_product.


(* Shannon Expanssion second form: F = (x+Fx')(x'+Fx) *)
Section ShannonExpanssion_AndOr.

(* Shannon Expansion on circuit c w.r.t. a variable x. *)
Definition ShannonExpanssion2 (c:Circuit) (x:string) :=
  let c1 := cofactor1 c x in
  let c0 := cofactor0 c x in
   (@ x || c0) && (!(@ x) || c1).
Definition SE2 := ShannonExpanssion2.

(*
  P x = ((! x || P true) && (x || P false)). 
*)
Compute (prc (SE2 circ_ex1 "x")).
(*"(x+0+0+y(1z+z'))(x'+y+z'+y(0z+z'))" *)
Compute (prc (msimp (SE2 circ_ex1 "x") 3)).
(* = "(x+y)(x'+y+z'+yz')" *)

Fixpoint ShannonExpanssions2 (c:Circuit) (vars:list string) : Circuit :=
  match vars with
  | [ ] => c
  | x::tl =>
    let c' := simp (ShannonExpanssion2 c x) in
      ShannonExpanssions2 c' tl 
  end.
Definition SES2 := ShannonExpanssions2.


Open Scope string_scope. (* to allow ["x"] *)
Compute (prc circ_ex1). (* "xy+xz'+y(x'z+z')" *)
Compute (prc (SE2  circ_ex1 "x")). 
(* = "(x+0+0+y(1z+z'))(x'+y+z'+y(0z+z'))" *)
Compute (prc (msimp (SE2  circ_ex1 "x") 3)). (* "(x+y)(x'+y+z'+yz')" *)
Compute (prc (SES2 circ_ex1 ["x"; "y"])). (* "(y+x(x'+z'))(y'+1(x'+1))" *)

Definition goSES2 (c:Circuit) (vars: list string) (n:nat) : Circuit :=
   (pos (msimp (SES2 c vars) n) n).

Definition prSES2 (c:Circuit) (vars: list string) (n:nat) : string :=
   prc (goSES2 c vars n).

Compute prc circ_ex1.
Compute prSES2 circ_ex1 ["x"] 3. (*  "(x+y)(x'+y+z'+yz')" *)

Compute prSES2 circ_ex1 ["x"; "y"] 3. (*  "(y+x)(y+x'+z')" *)

Compute prc (goSES2 circ_ex1 ["x"; "y";"z"] 3). (* "(z+y+x)(z'+y)" *)

End ShannonExpanssion_AndOr.

(** verification by simulation and equivalence checking. **)

Section Circuit_simulation.

Definition tpEnv := string -> bool.

(* circuit simulation against under a stimulus env. *)
Fixpoint Ceval (c:Circuit) (env: tpEnv) : bool :=
  match c with
  | True  => true
  | False => false
  | Var v => env v
  | Not x => notg (Ceval x env)
  | And x y => andg (Ceval x env) (Ceval y env)
  | Or  x y => org (Ceval x env) (Ceval y env)
  | Xor x y => xorg (Ceval x env) (Ceval y env)
end.

Open Scope string_scope. (* define the notation for "x" etc. *)

(* example of an environment. *)
Let envf1 (v:string) : bool :=
  match v with
   | "x" => true
   | "y" => false
   | "z" => true
   | _   => false  (* default value *)
  end.
Import List.ListNotations.
Open Scope list_scope. (* define notations such as :: *)

Definition tpVenv := list (string * bool).
Definition envEx := [("x",true);("y",false);("z",true)].

Fixpoint funEval (env : tpVenv) : tpEnv :=
  match env with
  | ((a,b) as hd)::tl => fun x =>
      if eqb a x then b else funEval tl x
  | nil => fun x => false
end.

Compute (funEval envEx "x").
Compute (funEval envEx "y").
Compute (funEval envEx "z").
Compute (funEval envEx "a").

Check  funEval envEx.

(* circuit evaluation with list environment. *)
Definition Beval (c:Circuit) (venv:tpVenv) : bool :=
  Ceval c (funEval venv).

Compute (prc circ_ex1).          (* xy+xz'+y(x'z+z') *)
Compute (Beval circ_ex1 envEx).
Compute (prc (SEA circ_ex1)).    (* zy+z'(y+y'x)     *)
Compute (Beval (SEA circ_ex1) envEx).
Compute (Beval (msimp (SEA circ_ex1) 2) envEx).


(* simulation against a list of tests. *)
Fixpoint simu (c:Circuit) (tests:list tpVenv) 
   (results:list bool) : list bool :=
  match tests with
    test::tl => simu c tl ((Beval c test)::results)
  | [] => results
  end.

Definition simulation (c:Circuit) (tests:list tpVenv) : list bool :=
  simu c tests [].

(* Boolean laws in circuit form. *)
Lemma circuit_assoc_and : forall (x y z: Circuit) (env:tpEnv),
  Ceval (x && (y && z)) env = Ceval ((x && y) && z)  env.
intros. simpl. truth_table_tactic.
Abort. (* naive automatic proof failed. *)

(* convert Circuit verification problem to boolean verification. *)
Lemma circuit_assoc_and : forall (x y z: Circuit) (env:tpEnv),
  Ceval (x && (y && z)) env = Ceval ((x && y) && z)  env.
intros. simpl.
truth_table_tactic3 (Ceval x env) (Ceval y env) (Ceval z env).
Qed. 
(* truth_table_tactic3 is more powerful than truth_table_tactic. *)

Lemma circuit_assoc_andv : forall (x y z: Circuit) (venv:tpVenv),
  Beval (x && (y && z)) venv = Beval ((x && y) && z)  venv.
intros. unfold Beval. simpl. 
truth_table_tactic3  (Ceval x (funEval venv))
  (Ceval y (funEval venv)) (Ceval z (funEval venv)).
Restart. (* another proof by existing algebra law. *)
intros. unfold Beval. simpl. apply associativity_and.
Qed.

(* SES simulation and equivalence checking. *)
Definition goSES (c:Circuit) (vars: list string) (n:nat) : Circuit :=
   (sop (msimp (SES c vars) n) n).

Compute prc circ_ex1.
Let circ_ex1_simp := goSES circ_ex1 ["x"; "y"] 3.
Compute prc circ_ex1_simp. (* "y+y'xz'" *)

(* formal verification by boolean equivalence checking. *)
Lemma circ_ex1_simp_ok : forall (venv:tpVenv),
  Beval circ_ex1 venv = Beval circ_ex1_simp venv.
intros. unfold Beval. unfold circ_ex1, circ_ex1_simp.
Abort. (* don't know how to proceed, left for future investigation. *)

(* how to compute circ_ex1_simp_explicit during proof ? *)
Let circ_ex1_simp_explicit := Eval cbv in circ_ex1_simp.
Print circ_ex1_simp_explicit.
(* *** [ccs := @ "y" || ! @ "y" && (@ "x" && ! @ "z") : Circuit] *)

Lemma circ_ex1_simp_ok : forall (venv:tpVenv),
  Beval circ_ex1 venv = Beval circ_ex1_simp_explicit venv.
intros. unfold Beval. unfold circ_ex1, circ_ex1_simp_explicit.
simpl.
truth_table_tactic3  (funEval venv "x")
  (funEval venv "y") (funEval venv "z").
Qed.

End Circuit_simulation.


(** OCaml code extraction example. **)

(* simple extraction example. *)
Require Import Extraction.
Recursive Extraction ShannonExpanssion prc.

(* improved extraction with object mapping. *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
(* coq has a special library for string extraction. *)
(* https://coq.inria.fr/library/Coq.extraction.ExtrOcamlNativeString.html *)
Require Import ExtrOcamlNativeString. (* string extraction. *)
(* extract functions ShannonExpanssion and prc. *)
Recursive Extraction ShannonExpanssion prc print.
(* extract listed functions into file. *)
Extraction "se.ml" SE prSES prc print circ_ex1. 


(* for boolean proposition reasoning. *)


(* for classical proposition reasonning. *)
Require Import Classical.
Require Import Classical_Prop.

Require Import FunInd.


Open Scope string_scope.

Section CircuitVerifyInProp.

(* method 2: convert a circuit to a Prop. *)

(* The problem is how to convert a string to a variable.
   For teaching purpose where circuits are small, 
   we get around the problem by introduce a group of
   predefined variables.
*)
Variables X Y Z NoVar : Prop.
Definition str2pvar (v:string) : Prop :=
  match v with
   | "x" => X
   | "y" => Y
   | "z" => Z
   | _   => NoVar
  end.


(* convert a circuit to a booliean expression *)
Fixpoint c2Prop (c:Circuit) : Prop :=
  match c with
  | True  => Logic.True
  | False => Logic.False
  | Var v => str2pvar v
  | Not x =>  ~(c2Prop x)
  | And x y => (c2Prop x) /\ (c2Prop y)
  | Or  x y => (c2Prop x) \/ (c2Prop y)
  | Xor x y => ~((c2Prop x) <-> (c2Prop y))
end.

Compute (c2Prop circ_ex1).
(*
 = (X /\ Y \/ X /\ (Z -> Logic.False)) \/
       Y /\ ((X -> Logic.False) /\ Z \/ (Z -> Logic.False))
*)
Opaque not. (* to keep ~X *)
Compute (c2Prop circ_ex1). (* still unfold to X -> Logic.False *)
Compute (prc circ_ex1).
Eval cbv in (c2Prop circ_ex1).
(*  = (X /\ Y \/ X /\ ~ Z) \/ Y /\ (~ X /\ Z \/ ~ Z) *)
Compute (prc sea_circ_ex1).
Eval cbv in (c2Prop sea_circ_ex1).
(*  = Z /\ Y \/ ~ Z /\ (Y \/ ~ Y /\ X) *)

(*
Tactic classical_left
Tactic classical_right
These tactics are the analog of left and right but using classical 
logic. They can only be used for disjunctions. Use classical_left
 to prove the left part of the disjunction with the assumption that
 the negation of right part holds. Use classical_right to prove 
the right part of the disjunction with the assumption that the 
negation of left part holds.
*)
Lemma circ_ex1_equiv : 
  (c2Prop circ_ex1) <-> (c2Prop sea_circ_ex1).
cbv. (* unfold to a proposition *)
split. 
+ intro. classical_left.  
Admitted. (* exercise *)

End CircuitVerifyInProp.

(* circuit formal equivalence checking. *)
Section CircuitVerifyInBooleanLogic.

Open Scope string_scope.
(* method 1. convert circuit to boolean expression. *)
Variables x y z novar : bool.
Definition str2bvar (s:string) : bool :=
  match s with
   | "x" => x
   | "y" => y
   | "z" => z
   | _   => novar
  end.

(* convert a circuit to a booliean expression *)
Fixpoint c2b (c:Circuit) : bool :=
  match c with
  | True  => true
  | False => false
  | Var v => str2bvar v
  | Not x => notg (c2b x)
  | And x y => andg (c2b x) (c2b y)
  | Or  x y => org (c2b x) (c2b y)
  | Xor x y => xorg (c2b x) (c2b y)
end.

Eval simpl   in (c2b circ_ex1).
(* unfold to the level of and or gates. *)
Eval compute in (c2b sea_circ_ex1).
(* unfold to if, too much *)

Opaque org andg notg xorg.
Opaque orb andb negb.
(* disable unfolding to if for compute. *)

Compute (prc circ_ex1).     (* xy+xz'+y(x'z+z') *)
Compute (prc sea_circ_ex1). (* zy+z'(y+y'x) *)
Eval simpl   in (c2b circ_ex1).
Eval compute in (c2b sea_circ_ex1). (* stuck_error *)

(* Eval simp in (c2b sea_circ_ex1). stuck ! *)

(* equivalence proof of circ_ex1 and its Shannon expansion. *)
Example se_ex1_x_proof : c2b circ_ex1 = c2b sea_circ_ex1. 
compute. truth_table_tactic3 x y z; reflexivity.
Qed. 

Reset x.
Variable var:string->bool.
(* convert a circuit to a booliean expression *)
Fixpoint c2b  (c:Circuit) : bool :=
  match c with
  | True  => true
  | False => false
  | Var v => var v
  | Not x => notg (c2b x)
  | And x y => andg (c2b x) (c2b y)
  | Or  x y => org (c2b x) (c2b y)
  | Xor x y => xorg (c2b x) (c2b y)
end.

Opaque org andg notg xorg.
Opaque orb andb negb.


Compute (prc circ_ex1).     (* xy+xz'+y(x'z+z') *)
Compute (prc sea_circ_ex1). (* zy+z'(y+y'x) *)
Eval simpl   in (c2b circ_ex1).
Eval compute in (c2b sea_circ_ex1).  

(* Eval simp in (c2b sea_circ_ex1). stuck ! *)

(* equivalence proof of circ_ex1 and its Shannon expansion. *)
 Example se_ex1_x_proof : c2b circ_ex1 = c2b sea_circ_ex1. 
compute. truth_table_tactic3 (var "x") (var "y") (var "z"); reflexivity.
Qed.

(*
End CircuitVerifyInBooleanLogic.


Require Import CpdtTactics.

(* properties of assign and simp. *)
Section Assign_Simp_Properties.
Variable var : string->bool. (* c2b implicit argument. *)
Let c2b := c2b var.
*)
Lemma assign_true : forall x v,
  assign True x v = True.
intros. reflexivity.
Qed.

Lemma assign_false : forall x v,
  assign False x v = False.
intros. reflexivity.
Qed.

Lemma if_str_eq : forall (x:string) (c1:Circuit) (c2:Circuit),
  (if x =? x then c1 else c2) = c1.
intros. rewrite eqb_refl. easy.
Qed.

Lemma assign_var_eq : forall x v,
  c2b (assign (Var x) x v) = c2b v.
intros. simpl. rewrite if_str_eq. easy.
Qed.

Lemma assign_var_neq : forall y x v,
  y<>x -> c2b (assign (Var y) x v) = c2b (Var y).
intros. rewrite<- String.eqb_neq in H.
simpl. rewrite H. easy.
Qed.

Lemma assign_var : forall y x v,
  c2b (assign (Var y) x v) = 
  if x=?y then c2b v else c2b (Var y).
intros. case (string_dec x y).
+ intro. rewrite e. rewrite eqb_refl. apply assign_var_eq.
+ intro.  rewrite assign_var_neq. 
rewrite<- String.eqb_neq in n. rewrite n. easy. auto.
Qed.

Lemma assign_not : forall c x v, 
  c2b (assign (! c) x v) = c2b (! (assign c x v)).
intros. induction c; try(reflexivity).
Qed.

Lemma assign_and_true : forall c x v,
  c2b (assign (c && True) x v) = c2b (assign c x v).
intros. simpl. apply bounded_true_and.
Qed.

Lemma c2b_and_true : forall c ,
  c2b (c && True) = c2b c.
intro. simpl; apply bounded_true_and.
Qed.

Lemma assign_and : forall c1 c2 x v, 
  c2b (assign (c1 && c2) x v) = 
  c2b ((assign c1 x v) && (assign c2 x v)).
intros. reflexivity.
Qed.

Lemma assign_or : forall c1 c2 x v, 
  c2b (assign (c1 || c2) x v) = 
  c2b ((assign c1 x v) || (assign c2 x v)).
intros. reflexivity.
Qed.

Lemma assign_xor : forall c1 c2 x v, 
  c2b (assign (c1 (+) c2) x v) = 
  c2b ((assign c1 x v) (+) (assign c2 x v)).
intros. reflexivity.
Qed.

Hint Rewrite assign_var_eq assign_var_neq assign_not
assign_and_true assign_and assign_or assign_xor : assign_base.

(* this is not valid because eqc (! True) False = false. *)
Lemma eqc_not_True : forall c, eqc (! c) True = false.
intros. simpl. easy.
Qed.

Lemma eqc_not_False : forall c, eqc (! c) False = false.
intros. simpl. easy.
Qed.

Lemma eqc_and_True : forall c1 c2, eqc (c1 && c2) True = false.
intros. simpl. easy.
Qed.

Lemma eqc_and_False : forall c1 c2, eqc (c1 && c2) False = false.
intros. simpl. easy.
Qed.

Lemma eqc_or_True : forall c1 c2, eqc (c1 || c2) True = false.
intros. simpl. easy.
Qed.

Lemma eqc_or_False : forall c1 c2, eqc (c1 || c2) False = false.
intros. simpl. easy.
Qed.

Hint Rewrite eqc_not_True eqc_not_False eqc_and_True eqc_and_False
eqc_or_True eqc_or_False : eqc_base.

Lemma c2b_var : forall s, c2b (@ s) = var s.
intro. reflexivity.
Qed.

Lemma c2b_and : forall c1 c2, 
   c2b (c1 && c2) = andg (c2b c1) (c2b c2).
intros. simpl. easy.
Qed.

Lemma c2b_or : forall c1 c2, 
   c2b (c1 || c2) = org (c2b c1) (c2b c2).
intros. simpl. easy.
Qed.

Lemma c2b_xor : forall c1 c2, 
   c2b (c1 (+) c2) = xorg (c2b c1) (c2b c2).
intros. simpl. easy.
Qed.

Lemma c2b_not : forall c, c2b (! c) = notg (c2b c).
intros. simpl. easy.
Qed.
Lemma c2b_not_not : forall c, c2b (! ! c) = c2b c.
intros. repeat rewrite c2b_not. apply involution.
Qed.

Lemma c2b_if : forall (b:bool) (c1 :Circuit) (c2:Circuit),
   c2b c1 = c2b c2 -> c2b (if b then c1 else c2) = c2b c1.
intros. destruct b; easy.
Qed.

Lemma c2b_if2 : forall (b:bool) (c1:Circuit) (c2:Circuit),
  c2b (if b then c1 else c2) = if b then c2b c1 else c2b c2.
intros. destruct b; reflexivity.
Qed.

Lemma if2and_or : forall (b:bool) (b1:bool) (b2:bool),
  (if b then b1 else b2) = ((b && b1) || (negb b && b2))%bool.
intros. truth_table_tactic3 b b1 b2.
Qed.

Hint Rewrite c2b_not_not c2b_not c2b_and c2b_or c2b_var : c2b_base.



Lemma bounded_false_or2 : forall b:bool, (false || b  = b)%bool.
 truth_table_tactic.
Qed.

Lemma bounded_true_or2 : forall b:bool, (true || b  = true)%bool.
 truth_table_tactic.
Qed.

Lemma bounded_false_and2 : forall b:bool, (false && b  = false)%bool.
 truth_table_tactic.
Qed.

Lemma bounded_true_and2 : forall b:bool, (true && b  = b)%bool.
 truth_table_tactic.
Qed.

Lemma str_neq : forall (s:string) (s0:string), s<>s0 -> (s =? s0)=false.
intros s s0 H. rewrite eqb_neq. easy.
Qed.

Lemma eqc_var_spec s s0 : Bool.reflect (@ s = @ s0) (s =? s0).
case (string_dec s s0).
+ intro H; rewrite H. rewrite eqb_refl. constructor. easy. 
+ intro H. rewrite<- eqb_neq in H. rewrite H. constructor.
  rewrite eqb_neq in H.  intro.
(*
H : s <> s0
H0 : @ s = @ s0
______________________________________(1/1)
Logic.False
*)
 inversion H0. easy.
Qed.

Lemma eqc_spec c1 c2 :  Bool.reflect (c1 = c2) (eqc c1 c2).
revert c2. induction c1. 
+ intro c2; destruct c2; try(constructor;easy).
+ intro c2; destruct c2; try(constructor;easy).
+ (* forall c2 : Circuit, reflect (@ s = c2) (eqc (@ s) c2) *)
  intro c2. destruct c2; try(constructor;easy). simpl. 
  (* reflect (@ s = @ s0) (s =? s0) *)
  apply eqc_var_spec.
+ (* forall c2 : Circuit, reflect (! c1 = c2) (eqc (! c1) c2) *)
  intro c2. destruct c2; try(constructor;easy). simpl.
 (* IHc1 : forall c2 : Circuit, reflect (c1 = c2) (eqc c1 c2)
    ----------------------------------
   reflect (! c1 = ! c2) (eqc c1 c2) *)
  destruct (IHc1 c2). 
  - (* reflect (! c1 = ! c2) true *)
    rewrite e. apply ReflectT. easy.
  - (* reflect (! c1 = ! c2) false *)
    constructor. intro. inversion H. contradiction.
+ (* forall c2 : Circuit, reflect (c1_1 && c1_2 = c2) (eqc (c1_1 && c1_2) c2) *)
   intro. destruct c2; try(constructor;easy). simpl.
  destruct (IHc1_1 c2_1); destruct (IHc1_2 c2_2);simpl;constructor.
  - (* c1_1 && c1_2 = c2_1 && c2_2 *) rewrite e,e0; easy.
  - (* c1_1 && c1_2 <> c2_1 && c2_2 *) rewrite e. 
    intro H. assert(c1_2 = c2_2). inversion H. contradiction. contradiction.
  - rewrite e. intro H. assert(c1_1=c2_1). inversion H. easy. contradiction.
  - intro H. inversion H. contradiction.
+ (* forall c2 : Circuit, reflect (c1_1 || c1_2 = c2) (eqc (c1_1 || c1_2) c2) *)  
  (* the proof for || is exactly a copy of the proof for && *)
   intro. destruct c2; try(constructor;easy). simpl.
   destruct (IHc1_1 c2_1); destruct (IHc1_2 c2_2);simpl;constructor.
  - rewrite e,e0; easy.
  - rewrite e. 
    intro H. assert(c1_2 = c2_2). inversion H. contradiction. contradiction.
  - rewrite e. intro H. assert(c1_1=c2_1). inversion H. easy. contradiction.
  - intro H. inversion H. contradiction.
+ (* forall c2 : Circuit, reflect (c1_1 (+) c1_2 = c2) (eqc (c1_1 (+) c1_2) c2) *)  
  (* the proof for (+) is exactly a copy of the proof for && *)
   intro. destruct c2; try(constructor;easy). simpl.
   destruct (IHc1_1 c2_1); destruct (IHc1_2 c2_2);simpl;constructor.
  - rewrite e,e0; easy.
  - rewrite e. 
    intro H. assert(c1_2 = c2_2). inversion H. contradiction. contradiction.
  - rewrite e. intro H. assert(c1_1=c2_1). inversion H. easy. contradiction.
  - intro H. inversion H. contradiction.
Qed.

(* one usage of the above lemma is for case analysis shown below. *)

Lemma eqc_eq : forall c1 c2, eqc c1 c2 = true <-> c1 = c2.
intros. destruct (eqc_spec c1 c2); easy.
Qed. 

Lemma simp_not : forall c,  c2b (simp (! c)) = c2b (! (simp c)).
induction c; try(reflexivity).
+ rewrite c2b_not. rewrite IHc. rewrite c2b_not.
  rewrite involution. 
(* c2b (simp (! ! c)) = c2b (simp c) *)
  reflexivity.
Qed.

Lemma simp_var : forall s, simp (@ s) = @ s.
intro. reflexivity.
Qed.

Lemma and_true : forall x y, andg x y = true -> x = true /\ y = true.
intros. destruct x; destruct y; try (inversion H).
- split; easy.
Qed.

(* it allows the use of functional induction (simp c) in simp_ok proof. *)
Functional Scheme simp_ind := Induction for simp Sort Prop. 
Check simp_ind.
Lemma simp_ok : forall c, c2b (simp c) = c2b c.
intros. (* demonstration the effect of functional induction. *)
functional induction (simp c). 
Restart. (* demonstration of induction followed by c2b* rewriting. *)
intros; functional induction (simp c); try(reflexivity);
try rewrite ?c2b_and,?c2b_not,?c2b_or,?c2b_xor; try rewrite IHc0; auto.
Restart. (* the complete proof. *)
intros; functional induction (simp c); try(reflexivity);
try rewrite ?c2b_and,?c2b_not,?c2b_or,?c2b_xor; try rewrite IHc0;
try rewrite ?bounded_true_and,?bounded_false_and;
try rewrite IHc1;
try rewrite ?notg_notg;
try (simpl; rewrite bounded_true_or); 
try (simpl; rewrite bounded_false_or);
auto;
try rewrite eqc_eq in e2; subst; 
try rewrite ?c2b_and,?c2b_not,?c2b_or.
(* 52 sub-goals *)
- truth_table_tactic1 (c2b x0). 
- truth_table_tactic1 (c2b (@ _x)).
- truth_table_tactic1 (c2b (@ _x)).
- truth_table_tactic1 (c2b x0).
- truth_table_tactic2 (c2b _x) (c2b _x0).
- truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite ?c2b_xor. truth_table_tactic2 (c2b _x) (c2b _x0).
- truth_table_tactic2 (c2b _x) (c2b _x0).
- truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite ?c2b_xor. truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqb_eq in e3. rewrite <- e3. truth_table_tactic1 (c2b (@ x0)).
- rewrite ?c2b_and. rewrite eqc_eq in e3. rewrite <- e3.
  simpl. autorewrite with and_or_neg_simp. reflexivity.
- rewrite eqc_eq in e3. inversion e3.
- rewrite ?c2b_xor. rewrite eqc_eq in e3. inversion e3.
- rewrite eqc_eq in e3. inversion e3.
- rewrite eqb_eq in e3. rewrite e3. truth_table_tactic1 (c2b (@ y0)).
- rewrite eqc_eq in e3. rewrite <- e3. simpl. truth_table_tactic1 (var y0).
- rewrite eqc_eq in e3. rewrite e3. rewrite ?c2b_and. truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqc_eq in e3. rewrite e3. rewrite ?c2b_or. truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqc_eq in e3. rewrite e3. rewrite ?c2b_xor. truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqc_eq in e3. rewrite <- e3. simpl. truth_table_tactic1 (c2b _x).
- rewrite eqc_eq in e3. rewrite <- ?c2b_and. rewrite <- e3.
  simpl. truth_table_tactic1 (c2b _x).
- rewrite eqc_eq in e3. rewrite <- ?c2b_not. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x0) (c2b _x1).
- rewrite eqc_eq in e3. rewrite <- ?c2b_not. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x0) (c2b _x1).
- rewrite eqc_eq in e3. rewrite <- ?c2b_not. rewrite e3. simpl.
  truth_table_tactic1 (c2b y0).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite <- e3. simpl.
  truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqc_eq in e3. rewrite <- ?c2b_or. rewrite e3. rewrite ?c2b_and.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite <- ?c2b_or. rewrite e3. rewrite ?c2b_or.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite <- ?c2b_or. rewrite e3. rewrite ?c2b_xor.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite <- e3. simpl.
  truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite eqc_eq in e3. rewrite e3. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- simpl. truth_table_tactic2 (c2b _x) (c2b _x0).
- simpl. truth_table_tactic2 (c2b _x) (c2b _x0).
- simpl. truth_table_tactic2 (c2b _x) (c2b _x0).
- simpl. truth_table_tactic1 (var _x).
- rewrite <- e2. simpl. rewrite xorb_b_b. reflexivity.
- rewrite <- ?c2b_not. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_and. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_or. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_xor. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- simpl. truth_table_tactic1 (c2b _x).
- rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_not. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_and. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_or. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_xor. rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- simpl. truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite <- e2. simpl. autorewrite with base_bool_simp. reflexivity.
- rewrite <- ?c2b_and, ?c2b_not.  rewrite e2. simpl.
  truth_table_tactic1 (c2b _x1).
- rewrite <- ?c2b_and.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite <- ?c2b_and, ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite <- ?c2b_and, ?c2b_or, ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite<-  ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic1 (var _x1).
- rewrite<-  ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic1 (c2b _x1).
- rewrite<-  ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite<-  ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite<-  ?c2b_or.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- simpl.
  truth_table_tactic2 (c2b _x) (c2b _x0).
- rewrite<-  ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic1 (var _x1).
- rewrite<-  ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic1 (c2b _x1).
- rewrite<-  ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite<-  ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
- rewrite<-  ?c2b_xor.  rewrite e2. simpl.
  truth_table_tactic2 (c2b _x1) (c2b _x2).
Qed.

(*
End CircuitVerifyInBooleanLogic.


Section Cofactor_Properties.
(*
Cofactor of Not is Not of cofactor  (~F)x = ~ F x
Cofactor of And is And of cofactor  (F && G) x = F x  && G x 
Cofactor of Or is Or of cofactor    (F || G) x = F x  || G x 

equality should be 
False = ! True
*)
Variable var : string->bool.
Let c2b := c2b var.
Let c2b_not := c2b_not var.
Let c2b_and := c2b_and var.
Let c2b_or  := c2b_or var.
Let c2b_xor := c2b_xor var.
Let assign_not := assign_not var.
Let simp_ok := simp_ok var.
*)

(* return an assignment function for  x = b. *)
Definition assign_xb (x:string) (b:bool) :=
   fun z => if String.eqb z x then b else false.

(* circuit evaluation w.r.t. a variable x. *)
Definition evalx (c:Circuit) (x:string) (b:bool) : bool :=
  Ceval c (assign_xb x b).

(* (~F)_x = ~ F_x *)
Lemma cofactor_not : forall (c:Circuit) (x:string) (b:Circuit),
  (c2b (cofactor (! c) x b)) =  (c2b (! (cofactor c x b))).
intros. unfold cofactor. 
induction c; try(reflexivity).
+ rewrite c2b_not. repeat (rewrite simp_ok).
  rewrite assign_not. rewrite c2b_not. easy.
+ repeat (rewrite simp_ok in * |- *). rewrite assign_not.
  repeat (rewrite c2b_not). rewrite IHc. rewrite c2b_not.
  repeat (rewrite simp_ok). rewrite assign_not. easy.
Qed.

Compute prc circ_ex1.
 (* "xy+xz'+y(x'z+z')" *)
Compute prc (! circ_ex1).
Compute prc (cofactor (! circ_ex1) "x" True). 
(* "(y+z'+y(0z+z'))'" *)
Compute prc (! (cofactor circ_ex1 "x" True)).
(* "(y+z'+y(0z+z'))'" *)

Lemma cofactor_var_neq : forall (y:string) (x:string) (b:Circuit),
  x<>y -> c2b (cofactor (Var y) x b) = var y.
intros. unfold cofactor. rewrite simp_ok.
rewrite assign_var_neq. rewrite c2b_var. easy. auto.
Qed.

Lemma cofactor_var_eq : forall (x:string) (b:Circuit),
   c2b (cofactor (Var x) x b) = c2b b.
intros. unfold cofactor. rewrite simp_ok.
rewrite assign_var_eq. easy.
Qed.

Lemma cofactor_var : forall (y:string) (x:string) (b:Circuit),
   c2b (cofactor (Var y) x b) = if y=?x then c2b b else var y.
intros. case (string_dec y x).
+ intro H. rewrite H. rewrite eqb_refl. apply cofactor_var_eq.
+ intro H. 
  rewrite<- eqb_neq in H. (* (x =? y)%string = false <-> x <> y. *)
  rewrite H. apply cofactor_var_neq. rewrite eqb_neq in H. auto. 
Qed.

Lemma cofactor1_not : forall (c:Circuit) (x:string),
  (c2b (cofactor1 (! c) x)) =  (c2b (! (cofactor1 c x))).
unfold cofactor1. intros. apply cofactor_not.
Qed.

Lemma cofactor0_not : forall (c:Circuit) (x:string),
  (c2b (cofactor0 (! c) x)) =  (c2b (! (cofactor0 c x))).
unfold cofactor0. intros. apply cofactor_not.
Qed.
 


(* (F && G) x = F x  && G x  *)
Lemma cofactor_and : forall c1 c2 x b,
  c2b (cofactor (c1 && c2) x b) = 
  c2b ((cofactor c1 x b) && (cofactor c2 x b)).
intros. unfold cofactor. induction c1,c2; (reflexivity || 
  (rewrite c2b_and; repeat (rewrite simp_ok);try(reflexivity))).
Qed.

(* (F || G) x = F x  || G x  *)
Lemma cofactor_or : forall c1 c2 x b,
  c2b (cofactor (c1 || c2) x b) = 
  c2b ((cofactor c1 x b) || (cofactor c2 x b)).
intros. unfold cofactor. induction c1,c2; (reflexivity || 
  (rewrite c2b_or; repeat (rewrite simp_ok);try(reflexivity))).
Qed.

(* (F (+) G) x = F x  (+) G x  *)
Lemma cofactor_xor : forall c1 c2 x b,
  c2b (cofactor (c1 (+) c2) x b) = 
  c2b ((cofactor c1 x b) (+) (cofactor c2 x b)).
intros. unfold cofactor. induction c1,c2; (reflexivity || 
  (rewrite c2b_xor; repeat (rewrite simp_ok);try(reflexivity))).
Qed.

Lemma cofactor0_xor : forall c1 c2 x,
  c2b (cofactor0 (c1 (+) c2) x) = 
  c2b ((cofactor0 c1 x) (+) (cofactor0 c2 x)).
intros; unfold cofactor0; apply cofactor_xor.
Qed.

Lemma cofactor1_xor : forall c1 c2 x,
  c2b (cofactor1 (c1 (+) c2) x) = 
  c2b ((cofactor1 c1 x) (+) (cofactor1 c2 x)).
intros; unfold cofactor1; apply cofactor_xor.
Qed.

(* try prove F_xy = F_yx: the variable order independance of cofactors. *)

(* 1st version, intended to be used in bderiv_var_order. *)
Lemma cofactor_cofactor : forall c x y b1 b2,
  c2b (cofactor (cofactor c x b1) y b2) = 
  c2b (cofactor (cofactor c y b2) x b1 ).
intros. unfold cofactor; induction c; try(reflexivity).
+ 
(*
c2b (simp (assign (simp (assign (@ s) x b1)) y b2)) =
c2b (simp (assign (simp (assign (@ s) y b2)) x b1))
*)
rewrite? simp_ok.
(*
c2b (assign (simp (assign (@ s) x b1)) y b2) =
c2b (assign (simp (assign (@ s) y b2)) x b1)
*)
(* require a lemma to deal with c2b (assign ...) *)
Abort.

End CircuitVerifyInBooleanLogic.

Definition tpVarMap := string->bool.

Section Boolean_Derivatives_v1.

(* Boolean derivatives or Boolean difference. *)
Definition bderiv (c:Circuit) (x:string) :=
  (cofactor1 c x) (+) (cofactor0 c x).

(* examples of bderiv. *)
Compute prc circ_ex1. (* "xy+xz'+y(x'z+z')" *)
Compute prc (bderiv circ_ex1 "x").
(* "y+z'+y(0z+z')(+)0+0+y(1z+z')" *)
Compute prc (msimp (bderiv circ_ex1 "x") 3).
(* "y+z'+yz'(+)y" *)
Compute prc (msimp (bderiv circ_ex1 "y") 3).
Compute  (msimp (bderiv circ_ex1 "y") 3).
(* "x+xz'+x'z+z'(+)xz'" *)
Compute prc (msimp (bderiv circ_ex1 "z") 3).
(* "xy+yx'(+)xy+x+y" *)

Let x := @ "x".
Let y := @ "y".
Let f := x && y.
Let fx := bderiv f "x".
Compute prc (simp fx).
(*  "y" -- f will not change when y=1 and x changes. *)

Reset x.
Variable var : tpVarMap.
(* independance of order of variables for derivatives. *)
Lemma bderiv_var_order (c:Circuit) (x:string) (y:string) :
  c2b var (bderiv (bderiv c x) y) = c2b var (bderiv (bderiv c y) x).
induction c; (reflexivity || unfold bderiv).
 unfold cofactor0, cofactor1. Abort.

(* bderiv based on cofactor is not suitable for property
   proving, so we change to cof. *)
Reset bderiv.

End Boolean_Derivatives_v1.

Check c2b.
Print cofactor.

(* proof of F_xy = F_yx: the variable order independance of cofactors. *)
Section c2b_cofactor_cofactor.

(* a key step to prove cof_cof is to remove assign from c2b (assign ...). *)
Lemma c2b_assign : forall c x v (var:string->bool),
  c2b var (assign c x v) = 
  c2b (fun z => if z =? x then (c2b var v) else var z) c.
intros. induction c; simpl; try(reflexivity).
+ rewrite c2b_if2. (* case analysis on s =? x *)
 destruct (eqb_spec s x); reflexivity.
+ f_equal. rewrite IHc. easy.
+ rewrite<- IHc1. rewrite<- IHc2. easy.
+ rewrite<- IHc1. rewrite<- IHc2. easy.
+ rewrite<- IHc1. rewrite<- IHc2. easy.
Qed.

(* conversion from bool to Circuit. *)
Definition b2c (b:bool) : Circuit :=
  match b with
   | true  => True
   | false => False
  end.

Lemma c2b2c var b : c2b var (b2c b) = b.
destruct b; simpl; easy.
Qed.

(* true cofactor with assignment restricted to true/false. *)
Definition cof (c:Circuit) x (b:bool) :=
  cofactor c x (b2c b).

Lemma cof_cof var c x y b1 b2 : x<>y ->
  c2b var (cof (cof c x b1) y b2) =
  c2b var (cof (cof c y b2) x b1).
intros. unfold cof, cofactor, b2c.  repeat (rewrite simp_ok).
repeat (rewrite c2b_assign). (* key step *)
repeat (rewrite simp_ok). induction c; try(reflexivity). 
+ repeat (rewrite c2b_assign). simpl. 
  (* case analysis on s=?x *)
  destruct (eqb_spec s x). 
    - (* s=x  *) destruct (eqb_spec s y). 
      * (* s=y, then x=y contradiction *)
        rewrite e in e0. contradiction. 
      * (* s<>y *) repeat (rewrite c2b_if2);try(reflexivity).
    - (* s<>x *) destruct (eqb_spec s y). 
        * (* s=y  *) repeat (rewrite c2b_if2);try(reflexivity).
        * (* s<>y *) easy.
+ repeat (rewrite assign_not; rewrite c2b_not). f_equal.
  apply IHc.
+ repeat (rewrite assign_and; rewrite c2b_and); f_equal.
  - apply IHc1.
  - apply IHc2.
+ repeat (rewrite assign_or; rewrite c2b_or); f_equal.
  - apply IHc1.
  - apply IHc2.
+ repeat (rewrite assign_xor; rewrite c2b_xor); f_equal.
  - apply IHc1.
  - apply IHc2.
Qed.
   
Lemma cof_xor : forall var c1 c2 x b,
  c2b var (cof (c1 (+) c2) x b) = 
  c2b var ((cof c1 x b) (+) (cof c2 x b)).
intros. unfold cof. apply cofactor_xor.
Qed.

Lemma cof_and : forall var c1 c2 x b,
  c2b var (cof (c1 && c2) x b) = 
  c2b var ((cof c1 x b) && (cof c2 x b)).
intros. unfold cof. apply cofactor_and.
Qed.

Lemma cof_or : forall var c1 c2 x b,
  c2b var (cof (c1 || c2) x b) = 
  c2b var ((cof c1 x b) || (cof c2 x b)).
intros. unfold cof. apply cofactor_or.
Qed.

Lemma cof_not : forall var c x b,
  c2b var (cof (! c) x b) = 
  c2b var (! (cof c x b)).
intros. unfold cof. apply cofactor_not.
Qed.

Lemma cof_var_neq : forall var y x b,
  y<>x -> c2b var (cof (@ y) x b) = var y.
intros. unfold cof. rewrite cofactor_var_neq. easy. auto.
Qed.

Lemma cof_var_eq : forall var  x b,
  c2b var (cof (@ x) x b) = b.
intros. unfold cof. rewrite cofactor_var_eq. apply c2b2c.
Qed.

Lemma cof_var : forall var y x b,
  c2b var (cof (@ y) x b) = if y=?x then b else var y.
intros. case (string_dec y x).
+ intro H; rewrite H. rewrite eqb_refl. apply cof_var_eq.
+ intro H. rewrite<- eqb_neq in H. rewrite H. 
apply cof_var_neq. rewrite eqb_neq in H. easy.
Qed.

Lemma SE_cofactor_ok var c x :
c2b var c =
c2b var
  (@ x && cofactor c x (b2c true) || ! @ x && cofactor c x (b2c false)).
Proof.
 rewrite c2b_or.  rewrite? c2b_and. unfold cofactor.
rewrite? simp_ok. rewrite? c2b_assign. simpl.
induction c; try(reflexivity).
+ simpl; truth_table_tactic1 (var x).
+ simpl; truth_table_tactic1 (var x).
+ simpl. destruct (eqb_spec s x). 
 - rewrite e. truth_table_tactic1 (var x).
 - truth_table_tactic2 (var x) (var s).
+ (* c2b var (! c) = *)
  simpl. rewrite IHc. rewrite deMorgan_or. rewrite deMorgan_and. 
  truth_table_tactic2 
 (c2b (fun z : string => if z =? x then true else var z) c)
 (c2b (fun z : string => if z =? x then false else var z) c).
 - truth_table_tactic1 (var x).
 - truth_table_tactic1 (var x).
 - truth_table_tactic1 (var x).
 - truth_table_tactic1 (var x).
+ (* c2b var (c1 && c2) = *)
  simpl. rewrite IHc1. rewrite IHc2. 
  truth_table_tactic4 
 (c2b (fun z : string => if z =? x then true else var z) c1)
 (c2b (fun z : string => if z =? x then false else var z) c1)
 (c2b (fun z : string => if z =? x then true else var z) c2)
 (c2b (fun z : string => if z =? x then false else var z) c2);
 truth_table_tactic1 (var x).
+ (* c2b var (c1 || c2) = *)
  simpl. rewrite IHc1. rewrite IHc2. 
  truth_table_tactic4 
 (c2b (fun z : string => if z =? x then true else var z) c1)
 (c2b (fun z : string => if z =? x then false else var z) c1)
 (c2b (fun z : string => if z =? x then true else var z) c2)
 (c2b (fun z : string => if z =? x then false else var z) c2);
 truth_table_tactic1 (var x).
+ (* c2b var (c1 (+) c2) = *)
  simpl. rewrite IHc1. rewrite IHc2. 
  truth_table_tactic4 
 (c2b (fun z : string => if z =? x then true else var z) c1)
 (c2b (fun z : string => if z =? x then false else var z) c1)
 (c2b (fun z : string => if z =? x then true else var z) c2)
 (c2b (fun z : string => if z =? x then false else var z) c2);
 truth_table_tactic1 (var x).
Qed.

(* correctness of Shannon Expansion. *)
Lemma SE_ok : forall var c x, c2b var c = c2b var (SE c x).
intros. unfold SE. unfold ShannonExpanssion. 
apply SE_cofactor_ok.
Qed.

(* define Shannon Expansion in terms of cof. *)
Definition cof_se c x := 
  (@ x) && (cof c x true) || (! (@ x)) && (cof c x false).

Lemma cof_SE_ok : forall var c x,
  c2b var c = c2b var (cof_se c x). 
intros. unfold cof_se. unfold cof. apply SE_cofactor_ok.
Qed.
  
End c2b_cofactor_cofactor.


Section Boolean_Derivatives_v2.



Definition bderiv (c:Circuit) (x:string) :=
  (cof c x true) (+) (cof c x false).
Variable var : tpVarMap.
(* independance of order of variables for derivatives. 
   df/dxdy = df/dydx *)
Lemma bderiv_var_order (c:Circuit)(x:string) (y:string) :
  x<>y ->
  c2b var (bderiv (bderiv c x) y) = 
  c2b var (bderiv (bderiv c y) x).
intro; unfold bderiv. rewrite? c2b_xor.
 rewrite? cof_xor. rewrite? c2b_xor.
 rewrite? (cof_cof var c x). (* key step 1 *)
 generalize (cof c y true). generalize (cof c y false).
 intros. 
 (* key step 2 *)
 truth_table_tactic4 (c2b var (cof c1 x true))
 (c2b var (cof c1 x false)) (c2b var (cof c0 x true))
 (c2b var (cof c0 x false)).
 easy. easy. easy. easy. 
Qed.


(* d(f(+)g)/dx = df/dx (+) dg/dx *)
Lemma bderiv_xor (f:Circuit) (g:Circuit) (x:string) : 
  c2b var (bderiv (f (+) g) x) =
  xorg (c2b var (bderiv f x)) (c2b var (bderiv g x)).
unfold bderiv. rewrite? c2b_xor. rewrite? cof_xor.
rewrite? c2b_xor.
truth_table_tactic4 (c2b var (cof f x true))
(c2b var (cof g x true)) (c2b var (cof f x false)) 
(c2b var (cof g x false)). 
Qed.

(* derivatives of constants are 0. *)
Lemma bderiv_true (x:string) :
  c2b var (bderiv True x) = false.
unfold bderiv. simpl. easy.
Qed.

Lemma bderiv_false (x:string) :
  c2b var (bderiv False x) = false.
unfold bderiv. simpl. easy.
Qed.

Lemma bderiv_var_eq (x:string) :
  c2b var (bderiv (Var x) x) = true.
unfold bderiv. rewrite c2b_xor.
rewrite? cof_var_eq. simpl. easy.
Qed.

Lemma bderiv_var_neq (y:string) (x:string) :
  x<>y -> c2b var (bderiv (Var y) x) = false.
intro. unfold bderiv. rewrite c2b_xor.
rewrite? cof_var_neq. apply xorb_b_b. auto. auto.  
Qed.

Lemma bderiv_var (y:string) (x:string) :
  c2b var (bderiv (Var y) x) = (y =? x).
case (string_dec y x); intro.
+ rewrite e. rewrite eqb_refl. apply bderiv_var_eq.
+ rewrite bderiv_var_neq.
rewrite<- eqb_neq in n. auto. auto.
Qed.

(*
Fundamentals of Switching Theory and Logic Design pp 235-267| Cite as

Boolean Difference and Applications in Testing Logic Networks
*)

(* d(!f)/dx = ! df/dx *)
Lemma bderiv_not (f:Circuit) (x:string) :
   c2b var (bderiv (!f) x) = c2b var (bderiv f x).
unfold bderiv. rewrite? c2b_xor. rewrite? cof_not.
rewrite? c2b_not.
truth_table_tactic2 (c2b var (cof f x true))
(c2b var (cof f x false)).
Qed.

(* derivative of && *)
Lemma bderiv_and (f:Circuit) (g:Circuit) (x:string) :
  c2b var (bderiv (f && g) x) =
  c2b var ((f && (bderiv g x)) (+)
           (g && (bderiv f x)) (+)
           ((bderiv f x) && (bderiv g x))).
unfold bderiv. rewrite? c2b_xor.
rewrite? cof_and, c2b_and.
rewrite? cof_xor. simpl. 
(* use SE to expand f to x * (cof f x true) || !x (cof f x false)
   so that we can call truth_table_tactic 4 on (cof f x true) etc. *)
rewrite (cof_SE_ok var f x). rewrite (cof_SE_ok var g x).
unfold cof_se. simpl. 
truth_table_tactic4 (c2b var (cof f x true))
(c2b var (cof g x true)) (c2b var (cof f x false)) 
(c2b var (cof g x false)); simpl; truth_table_tactic1 (var x).
Qed.
 
Lemma bderiv_or (f:Circuit) (g:Circuit) (x:string) :
  c2b var (bderiv (f || g) x) =
  c2b var (((! f) && (bderiv g x)) (+)
           ((! g) && (bderiv f x)) (+)
           ((bderiv f x) && (bderiv g x))).
unfold bderiv. rewrite? c2b_xor.
rewrite? cof_or, c2b_or.
rewrite? cof_and, c2b_and.
rewrite? cof_not, c2b_not.
rewrite? cof_xor, c2b_xor. rewrite? c2b_xor.
rewrite? cof_and, c2b_and.
rewrite? cof_not, c2b_not.
rewrite? cof_xor, c2b_xor. 
 simpl. 
(* use SE to expand f to x * (cof f x true) || !x (cof f x false)
   so that we can call truth_table_tactic 4 on (cof f x true) etc. *)
rewrite (cof_SE_ok var f x). rewrite (cof_SE_ok var g x).
unfold cof_se. simpl. 
truth_table_tactic4 (c2b var (cof f x true))
(c2b var (cof g x true)) (c2b var (cof f x false)) 
(c2b var (cof g x false)); simpl; truth_table_tactic1 (var x).
Qed.


Lemma xor_is_neq : forall (a:bool) (b:bool), (xorg a b) = notg (eqg a b).
  truth_table_tactic.
Qed.

(* Boolean difference usage example. *)

(* df/dx = 1 -> output sensitive to x. *)
Lemma bool_diff : forall var c x, 
  (c2b var (bderiv c x)) = true <-> 
  (c2b var (cofactor1 c x)) <> (c2b var (cofactor0 c x)).
intros. split.
+ (* -> *) intro H. unfold bderiv in H.
rewrite c2b_xor in H; rewrite xor_is_neq in H.
intro. unfold cof in H. unfold cofactor1, cofactor0 in H0.
simpl in H. rewrite H0 in H. rewrite eqb_b_b in H.  simpl in H.
inversion H.
+ (* <- *)  unfold bderiv. 
unfold cofactor1, cofactor0, cofactor.
rewrite? simp_ok.
rewrite c2b_xor; rewrite xor_is_neq.
unfold cof. unfold cofactor. rewrite? simp_ok. simpl.
truth_table_tactic2 (c2b var0 (assign c x True))
(c2b var0 (assign c x False));auto.
Qed.

(* 1 bit adder example. *)

(* work in bool type *)
Open Scope gate_scope.
Let gate_sum a b cin :=  a (+) b (+) cin.
Let gate_cout a b cin :=
  (a && b) || (a || b) && cin.

(** calculate boolean difference for cout step by step. **)

(* verify cout simplification for cin=1. *)
Lemma gate_cout_cin1 : forall a b, 
 gate_cout a b true = a || b.
intros. unfold gate_cout. truth_table_tactic.
Qed.

(* verify cout simplification for cin=0. *)
Lemma gate_cout_cin0 : forall a b, 
  gate_cout a b false = a && b.
intros. unfold gate_cout. truth_table_tactic.
Qed. 

Let gate_cout_derive a b (cin:bool) :=
 (gate_cout a b true) (+) (gate_cout a b false).
(* =       (a || b) (+) (a && b)  *)

Lemma gate_or_xor_and a b :
  (a || b) (+) (a && b) = a (+) b.
truth_table_tactic.
Qed.

Lemma gate_xor_neq a b :
  a (+) b = ! (a == b).
truth_table_tactic.
Qed.


(* verify dcout/dcin *)
Lemma gate_cout_bderiv : forall a b cin,
  gate_cout_derive a b cin = !(a == b).
intros. truth_table_tactic.
Qed.

(* case 1. a<>b => cout changes when cin changes. *)
Compute gate_cout true false true.
Compute gate_cout true false false.
Compute gate_cout false true true.
Compute gate_cout false true false.

(* case 2. a=b => cout keeps unchanged when cin changes. *)
Compute gate_cout true true true.
Compute gate_cout true true false.
Compute gate_cout false false true.
Compute gate_cout false false false.


(* it means that cout=1 iff a<>b, which implies that
   if a<b then the change of cin will bring a change 
   cout *)

Close Scope gate_scope.

Definition bit_sum a b cin := a (+) b (+) cin.

Definition bit_cout a b cin := 
(*  (a && b) || (a || b) && cin. *)
 (@ a && @ b) || (@ a || @ b) && @ cin. 

(* Open problem: how to transfer the result in 
   boolean expression to the property of Circuit. *)

Lemma circ_cout_simp : forall var a b, 
 c2b var ((a && b) || (a || b)) = c2b var (a || b).
intros. rewrite? c2b_or, c2b_and.
truth_table_tactic2 (c2b var0 a) (c2b var0 b).
Qed.

(* d cout/d cin *)
Definition cout_cin a b cin := bderiv (bit_cout a b cin) cin.

Lemma cout_cin_bd a b cin : 
   c2b var (cout_cin a b cin) =
   notg (eqg (c2b var (@ a)) (c2b var (@ b))).
unfold cout_cin. 
unfold bderiv. unfold cof, cofactor.
rewrite? c2b_xor, simp_ok. unfold bit_cout.
(*
repeat rewrite ?c2b_assign, ?c2b_or, ?c2b_and, ?simp_ok, eqb_refl;
simpl.


truth_table_tactic4
(if a =? cin then true else var a)
(if b =? cin then true else var b)
(if a =? cin then false else var a)
(if b =? cin then false else var b);
simpl.
truth_table_tactic2 (var a) (var b).
*)
rewrite? c2b_assign.
rewrite? c2b_or, c2b_and.
rewrite? simp_ok, c2b_assign.
rewrite? c2b_or, c2b_and.
rewrite? c2b_and, c2b_or.
 simpl. rewrite? eqb_refl.
(*
destruct (eqb_spec a cin); destruct (eqb_spec b cin);simpl.
+ rewrite e,e0.  truth_table_tactic1 (var cin).
+ rewrite e. truth_table_tactic2 (var cin) (var b).

truth_table_tactic2 (var a) (var b).

truth_table_tactic4
(if a =? cin then true else var a)
(if b =? cin then true else var b)
(if a =? cin then false else var a)
(if b =? cin then false else var b);
simpl.
truth_table_tactic2 (var a) (var b).



simpl. rewrite e,e0. 
truth_table_tactic2 (a =? cin) (b =? cin).
+  simp.
*)
Abort.
End Boolean_Derivatives_v2.

Section QuantificationOperators.

(* Universal Quantification or concensus = F_x && F_x' *)
Definition UniversalQuantification c x :=
  cofactor0 c x && cofactor1 c x.
Definition UQ := UniversalQuantification.
(* all other vars but x can make UQ true for
   all values of x. *)

(* Existential Quantification or smoothing = F_x || F_x'. *)
Definition ExistentialQuantification c x :=
  cofactor0 c x || cofactor1 c x.
Definition EQ := ExistentialQuantification.
(* there exists a value of x that makes the
   EQ true. *)

Definition cof2 c x y (b1:bool) (b2:bool) :=
  cof (cof c x b1) y b2.

(* (forall x y, F)=Fxy * Fx'y * Fxy' * Fx'y' *)
Lemma uq2 : forall var x y c,
  c2b var (UQ (UQ c x) y) = 
  (c2b var ((cof2 c x y true true) &&  
            (cof2 c x y true false) &&
            (cof2 c x y false true) && (* had an error here. *)
            (cof2 c x y false false))).
intros. 
unfold UQ, UniversalQuantification, cofactor0, cofactor1.
unfold cof2, cof, cofactor, b2c.
repeat(rewrite? c2b_and, simp_ok).
repeat(rewrite? c2b_assign, simp_ok).
repeat(rewrite? c2b_and, simp_ok).
simpl.
repeat(rewrite? c2b_assign; simpl).
truth_table_tactic4
(c2b (fun z : string => if z =? x then false else if z =? y then false else var z) c)
(c2b (fun z : string => if z =? x then true  else if z =? y then false else var z) c)
(c2b (fun z : string => if z =? x then false else if z =? y then true  else var z) c)
(c2b (fun z : string => if z =? x then true  else if z =? y then true  else var z) c)
.
Qed.

(* (exists x y, F)=Fxy || Fx'y || Fxy' || Fx'y' *)
Lemma eq2 : forall var x y c,
  c2b var (EQ (EQ c x) y) = 
  (c2b var ((cof2 c x y true true)  ||
            (cof2 c x y true false) ||
            (cof2 c x y false true) || 
            (cof2 c x y false false))).
intros. 
unfold EQ, ExistentialQuantification, cofactor0, cofactor1.
unfold cof2, cof, cofactor, b2c.
repeat(rewrite? c2b_or, simp_ok).
repeat(rewrite? c2b_assign, simp_ok).
repeat(rewrite? c2b_or, simp_ok).
simpl.
repeat(rewrite? c2b_assign; simpl).
truth_table_tactic4
(c2b (fun z : string => if z =? x then false else if z =? y then false else var z) c)
(c2b (fun z : string => if z =? x then true  else if z =? y then false else var z) c)
(c2b (fun z : string => if z =? x then false else if z =? y then true  else var z) c)
(c2b (fun z : string => if z =? x then true  else if z =? y then true  else var z) c)
.
Qed.

End QuantificationOperators.

(* example for the usage of universal and existential quantification. *)
Section TwoBitsAdder.
Open Scope gate_scope.
(*
Let gate_sum a b cin :=  a (+) b (+) cin.
Let gate_cout a b cin :=
  (a && b) || (a || b) && cin.
*)
Let gate_adder1 a b cin :=
  let sum  := a (+) b (+) cin in
  let cout := (a && b) || (a || b) && cin in
    (sum, cout).

(* (a1,b1)+(a0,b0)+cin => (sum1,cout1) *)
Let gate_adder2 a0 b0 a1 b1 cin :=
  let (sum0,cout0) := gate_adder1 a0 b0 cin in
  let (sum1,cout1) := gate_adder1 a1 b1 cout0 in
    (sum1,cout1).

Opaque andg org xorg notg.
Opaque andb orb xorb negb.

(* C = (A1,0)+(A0,X)+D => S, (forall A1 A0,C)[X,D] *)
Let cout1 A0 A1 X D := gate_adder2 A0 X A1 false D.
Eval cbv in fun A0 A1 X D => cout1 A0 A1 X D.
(*
 = (A1 (+) false (+) org (A0 && X) ((A0 || X) && D),
    A1 && false || (A1 || false) && org (A0 && X) ((A0 || X) && D))
*)

(* circuit of cout direct.    C = A1A0X + A1(A0+X)D*)
Lemma gate_adder2_cout' A0 A1 X D : 
 snd (cout1 A0 A1 X D) = 
 (A1 && ((A0 && X) || (A0 || X) && D)).
truth_table_tactic.
Qed.

(* circuit of cout simplified. *)
Lemma gate_adder2_cout A0 A1 X D : 
 snd (cout1 A0 A1 X D) = 
 (A1 && A0 && X) || (A1 && (A0 || X) && D).
truth_table_tactic.
Qed.

(* 
  forall A1 A0, cout[X,D] is a function of X and D, makes
  C=1 for all values of operand input A1A0.
  From C = A1A0X + A1(A0+X)D 
  Derive 
   forall A1 A0, cout[X,D] =
   C_A1A0 || C_A1'A0 || C_A1A0' || C_A1'A0' *)
Let gate_adder2_cout_forall2_original X D := 
  let A1A0   := X || D in
  let A1'A0  := false in
  let A1A0'  := X && D in
  let A1'A0' := false in
    A1A0 && A1'A0 && A1A0' && A1'A0'.
Variables X D : bool.
Eval cbv in gate_adder2_cout_forall2_original X D.
(* = org X D && false && andg X D && false *)
Lemma adder2_forall2 :
 gate_adder2_cout_forall2_original X D = false.
unfold gate_adder2_cout_forall2_original.
truth_table_tactic2 X D.
Qed.


(* No values of X,D that makes Cout=1 independent of A1,A0. *)

(* simplified univiersal quantification for cout2. *)
Let gate_adder2_cout_forall2 (X:bool) (D:bool) :=
    false. (* A1A0 && A1'A0 && A1A0' && A1'A0' *)

Let gate_adder2_cout_exist2_original X D := 
  let A1A0   := X || D in
  let A1'A0  := false in
  let A1A0'  := X && D in
  let A1'A0' := false in
    A1A0 || A1'A0 || A1A0' || A1'A0'. 
(* At least one X,D makes Cout=1 independent of A1,A0. *)

(* simplified univiersal quantification for cout2 independent of A1,A0. *) 
Let gate_adder2_cout_exist2 X D := 
  (X || D). (* X || D || (X && D) *)

(* if X=D=0, the carry will always be 0. *)
End TwoBitsAdder.

Section Network_Repair_Example.
(* Given a partial expression f(a,b) = a && b || !b *)

Open Scope gate_scope.

Let f a b := a && b || ! b.

Let g (h:bool->bool->bool) a b := h (!b) (a && b) . 

(* truth table definition of mux2. *)
Definition mux2 s0 s1 d0 d1 d2 d3 : bool :=
  match (s1,s0) with
  | (false,false) => d0
  | (false,true)  => d1
  | (true,false)  => d2
  | (true,true)   => d3
  end.

Lemma mux2_and : forall x y, 
  mux2 x y false false false true = x && y.
truth_table_tactic.
Qed.

Lemma mux2_xor : forall x y, 
  mux2 x y false true true false = x (+) y.
truth_table_tactic.
Qed.

Lemma mux2_or : forall x y, 
  mux2 x y false true true true = x || y.
truth_table_tactic.
Qed.

Lemma mux2_eq : forall x y, 
  mux2 x y true false false true = x == y.
truth_table_tactic.
Qed.

(* netlist definition of mux2. *)
Definition mux2' s0 s1 d0 d1 d2 d3 : bool :=
 d0 && !s1 && !s0 || d1 && !s1 && s0 ||
 d2 && s1  && !s0 || d3 && s1 && s0.

(* equivalence of mux2 and mux2'. *)
Lemma mux2_eq_mux2' : forall s0 s1 d0 d1 d2 d3,
  mux2 s0 s1 d0 d1 d2 d3 = mux2' s0 s1 d0 d1 d2 d3.
truth_table_tactic. Qed.

(** calculation of forall a b, Z . **)

(* G is intended to simulate f by configuring mux2'. *)
Let G a b d0 d1 d2 d3 :=
  g (fun a b => mux2' a b d0 d1 d2 d3) a b.

Lemma Gsimpl : forall a b d0 d1 d2 d3,
  G a b d0 d1 d2 d3 = mux2' (! b) (a && b)  d0 d1 d2 d3.
intros. reflexivity. 
(* unfold G. intros. unfold g. easy. *)
Qed.

(*
   mux2' s0 s1 = 
   d0 && !s0 && !s1 || d1 && s0 && !s1 ||
   d2 && !s0 && s1  || d3 && s0 && s1.
   mux2' s0 s1 d0 d1 d2 d3 : bool :=
   d0 && !s1 && !s0 || d1 && !s1 && s0 ||
   d2 && s1  && !s0 || d3 && s1 && s0.
   s0 = a && b, s1 = !b
*)
Lemma Gsimp2 : forall a b d0 d1 d2 d3,
  mux2' (!b) (a && b) d0 d1 d2 d3 = 
   d0 && !(a && b) && !!b || d1 && !(a && b) && !b ||
   d2 && (a && b)  && !!b || d3 && (a && b) && !b.
truth_table_tactic. Qed.

Lemma Gsimp3 : forall a b d0 d1 d2 d3,
  mux2' (!b) (a && b) d0 d1 d2 d3 = 
   d0 && !(a && b) && b || d1 && !(a && b) && !b ||
   d2 && (a && b) && !!b.
truth_table_tactic. Qed.

Lemma Gsimp4 : forall a b d0 d1 d2 d3,
  mux2' (!b) (a && b) d0 d1 d2 d3 = 
   d0 && !(a && b) && b || d1 && !(a && b) && !b ||
   d2 && a && b.
truth_table_tactic. Qed.

Lemma Gsimp5 : forall a b d0 d1 d2 d3,
  mux2' (!b) (a && b) d0 d1 d2 d3 = 
   d0 && !a && b || d1 && ! b || d2 && a && b.
truth_table_tactic. Qed.


Lemma Gsimp7 : forall a b d0 d1 d2 d3,
  G a b d0 d1 d2 d3 = 
   d0 && !a && b || d1 && ! b || d2 && a && b.
intros. unfold G,g. rewrite Gsimp5. easy.
Qed.

(*
Lemma eqb_eq_and_or : forall a b : bool, 
  (a==b) = (a && b) || (!a && !b).
*)
Check eqb_eq_and_or.

(* build a circuit to compare f and g. *)
Let Z a b d0 d1 d2 d3 := f a b == G a b d0 d1 d2 d3.

Lemma Z_and_or : forall a b d0 d1 d2 d3,
  let F0 := f a b in
  let G0 := G a b d0 d1 d2 d3 in
  let Z0 := Z a b d0 d1 d2 d3 in
   Z0 = (F0 && G0) || (! F0 && ! G0).
intros. unfold F0,G0,Z0, Z. apply eqb_eq_and_or.
Qed.  

(* universal quantification ∀a b, Z denotes the
   circuit to make G equals to f. 
   ∀a b,Z = 1 iff f = G
   ∀a b,Z = Z_a'b' && Z_a'b && Z_ab' && Z_ab
   Z_a'b' = f_a'b' == G_a'b'  
   f  = (a && b) || !b.
   G  = d0 && !a && b || d1 && ! b || d2 && a && b.
*)
Let Ga'b' d0 d1 d2 d3 := G false false d0 d1 d2 d3.
(* Ga'b' = d1 *)
Lemma Ga'b'_val d0 d1 d2 d3 : Ga'b' d0 d1 d2 d3 = d1.
unfold Ga'b'. rewrite Gsimp7.  truth_table_tactic. 
Qed.

Let Za'b' d0 d1 d2 d3 := Z false false d0 d1 d2 d3.
Lemma Za'b'_val d0 d1 d2 d3 : Za'b' d0 d1 d2 d3 = d1.
unfold Za'b',Z,Ga'b'. truth_table_tactic. Qed.

Let Ga'b d0 d1 d2 d3 := G false true d0 d1 d2 d3.
(* Ga'b = d0 *)
Lemma Ga'b_val d0 d1 d2 d3 : Ga'b d0 d1 d2 d3 = d0.
unfold Ga'b. rewrite Gsimp7.  truth_table_tactic. 
Qed.

Let Za'b d0 d1 d2 d3 := Z false true d0 d1 d2 d3.
Lemma Za'b_val d0 d1 d2 d3 : Za'b d0 d1 d2 d3 = ! d0.
truth_table_tactic. Qed.

Let Zab' d0 d1 d2 d3 := Z true false d0 d1 d2 d3.
Lemma Zab'_val d0 d1 d2 d3 : Zab' d0 d1 d2 d3 = d1.
truth_table_tactic. Qed.

Let Zab d0 d1 d2 d3 := Z true true d0 d1 d2 d3.
Lemma Zab_val d0 d1 d2 d3 : Zab d0 d1 d2 d3 = d2.
truth_table_tactic. Qed.

Let forallZab d0 d1 d2 d3 :=
  Za'b' d0 d1 d2 d3 && Za'b d0 d1 d2 d3 &&
  Zab'  d0 d1 d2 d3 && Zab  d0 d1 d2 d3.

(* \forall a b, Z = !d0 d1 d2. *)
Lemma forallZab_val d0 d1 d2 d3 :
 forallZab d0 d1 d2 d3 = !d0 && d1 &&  d2.
truth_table_tactic. Qed.

(* so the repair gate is *)
Let repair_gate (a:bool) (b:bool) : bool 
  := mux2' a b false true true true. (* or gate *)

(* recall that g (h:bool->bool->bool) a b := h (!b) (a && b) . 
   the repaired circuit is *)
Let g' :=  g repair_gate.
 
(*  verify that the repair gate solves the problem. *)
Lemma feqg' : forall a b, f a b = g' a b.
truth_table_tactic. Qed.

(* another repair. *)
Let repair_gate2 (a:bool) (b:bool) : bool 
  := mux2' a b false true true false. (* xor gate *)

Let g'' :=  g repair_gate2.
 
(* verify that the xor gate solves the problem too. *)
Lemma feqg'' : forall a b, f a b = g'' a b.
truth_table_tactic. Qed.

(* we could select the one with best performance! 
  it gives us choices of multiple implementations! 
  and all of them are verified correct.
*)

End Network_Repair_Example.
