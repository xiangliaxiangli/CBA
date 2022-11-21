(** 
   Title:      Boolean Logic.
   Author:     Gang Chen
   Date:       Jan 2022
   Reference:  http://en.wikipedia.org/wiki/Boolean_logic

   Type:       bool.
   Constants:  true,false
   Functions:  negb,andb,orb,xorb,eqb,implb,ifb.
   Symbols:    !,   &&,  ||, (+),  ==, ==>

   Contents:
      1. Boolean function truth tables;
      2. Lemmas that boolean functions satisfy the truth tables;
      3. Boolean algebra properties;
      4. bit vectors (bv1) and bit pair vectors (bc2);
      5. conversion from bv1 to nat;
      6. properties of bit vectors;
      7. equality proof related lemmas.
*)

Require Export Bool.

(** Truth Tables of Bool Functions. *)

Definition not_tbl (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
(*
Compute (not_tbl true).
Compute (not_tbl false).
*)
Definition and_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false
  end.
(*
Compute (and_tbl true true).
Compute (and_tbl true false).
*)

Definition or_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Definition nor_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Definition xor_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Definition impl_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => true
  | false, false => true
  end.

Definition eq_tbl (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.


Definition if_tbl (b1 b2 b3:bool) : bool :=
  match b1,b2,b3 with
  | true,true,true   => true
  | true,true,false  => true
  | true,false,true  => false
  | true,false,false => false

  | false,true,true   => true
  | false,true,false  => false
  | false,false,true  => true
  | false,false,false => false
  end.

(** define the primary gate mux as ifb. **)
(* ifb is already defined in Bool
Definition ifb (b1 b2 b3:bool) : bool :=
  match b1 with
    | true => b2
    | false => b3
  end.
*)
Definition mux := ifb.


(* derived gates. *)
Definition org (b1 b2:bool)   := mux b1 true b2.
Definition andg (b1 b2:bool)  := mux b1 b2 false.
Definition notg (b:bool)      := mux b false true.
Definition norg (b1 b2:bool)  := notg (org b1 b2).
Definition nandg (b1 b2:bool) := notg (andg b1 b2).
Definition eqg   (b1 b2:bool) := mux b1 b2 (notg b2).
Definition xorg  (b1 b2:bool) := mux b1 (notg b2) b2.
Definition implg (b1 b2:bool) := mux b1 b2 true.

(* find out defined functions and notations. *)
(* Locate orb. *)
(* output: Constant Coq.Init.Datatypes.orb *)
(* Print orb. *)
(*
orb = 
fun b1 b2 : bool => if b1 then true else b2
     : bool -> bool -> bool
*)
(*
Locate "||".
Print "||".
Print andb.
Print "&&".
*)
Declare Scope gate_scope.

(* notations for logical operators. *)

Infix "||"  := org   (at level 50, left associativity)  : gate_scope.
Infix "=="  := eqg   (at level 42, left associativity)  : gate_scope.
Infix "(+)" := xorg  (at level 42, left associativity)  : gate_scope.
Infix "(-)" := norg  (at level 42, left associativity)  : gate_scope.
Infix "&&"  := andg  (at level 40, left associativity)  : gate_scope.
Infix "==>" := implg (at level 36, right associativity) : gate_scope.

Notation "! x" := (notg x) (at level 35, right associativity)  : gate_scope.

Open Scope gate_scope.

Lemma implb_def : forall x y : bool, x ==> y = !x || y.
  intros; destruct x, y. 
 + trivial. 
 + trivial. 
 + trivial. 
 + trivial.
(* proof succeeded, but we want to find a simpler proof. *)
Abort.

Lemma implb_def : forall x y : bool, x ==> y = !x || y.
  intros; destruct x, y; trivial.
Abort.

Lemma implb_def : forall x y : bool, x ==> y = !x || y.
  intros; destruct_all bool; trivial.
Abort.

(* a general purpose tactic for proving boolean equalities. *)
Ltac truth_table_tactic := 
  intros;  destruct_all bool;  trivial.

Lemma implb_def : forall x y : bool, x ==> y = !x || y.
  truth_table_tactic.
Qed.

(* verify xorb, eqb, norb satisfy truth table. *)
Lemma xorg_def : forall x y : bool, x (+) y = (x || y) && !(x && y).
  truth_table_tactic. 
Qed.

Lemma eqg_def : forall x y : bool, x == y = !(x (+) y).
  truth_table_tactic.
Qed.

Lemma norg_def : forall x y : bool, x (-) y = !(x || y).
  truth_table_tactic.
Qed.

(** Boolean functions satisfy truth table definitions. *)
Lemma notg_satisfy_not_tbl : forall a : bool, !a = (not_tbl a).
Proof.
  truth_table_tactic.
Qed.

Lemma andg_satisfy_and_tbl : forall a b : bool, a && b = (and_tbl a b).
  truth_table_tactic.
Qed.

Lemma org_satisfy_or_tbl : forall a b : bool, a || b = (or_tbl a b).
  truth_table_tactic.
Qed.

Lemma implg_satisfy_impl_tbl : forall a b : bool, a ==> b = (impl_tbl a b).
  truth_table_tactic.
Qed.

Lemma xorg_satisfy_xor_tbl : forall a b : bool, (a (+) b) = (xor_tbl a b).
  truth_table_tactic.
Qed.

Lemma norg_satisfy_nor_tbl : forall a b : bool, (a (-) b) = (nor_tbl a b).
  truth_table_tactic.
Qed.

Lemma eqg_satisfy_eqb : forall a b : bool, (a == b) = (eq_tbl a b).
  truth_table_tactic.
Qed.

Lemma ifb_satisfy_if_tbl : forall a b c : bool, (ifb a b c) = (if_tbl a b c).
  truth_table_tactic.
Qed.



(** boolean function properties. 
  Reference: http://en.wikipedia.org/wiki/Boolean_logic
*)

Lemma associativity_or : forall a b c:bool, a || (b || c) = a || b || c.
  apply orb_assoc.
Qed.

Lemma associativity_and : forall a b c:bool, a && (b && c) = a && b && c.
  apply andb_assoc.  
Qed.

Lemma commutativity_or : forall a b :bool, a || b = b || a.
  apply orb_comm.
Qed.

Lemma commutativity_and : forall a b :bool, a && b = b && a. 
  apply andb_comm.  
Qed.

Lemma absorption_or : forall a b :bool, a || (a && b) = a.
  apply absoption_orb. 
Qed.

Lemma absorption_and : forall a b :bool,a && (a || b) = a.
  apply absoption_andb. 
Qed.

(** The above 6 properties define a lattice. *)

Lemma distributivity_or : forall a b c:bool, a || b && c = (a || b) && (a || c).
  apply demorgan3.
Qed.

Lemma distributivity_and : forall a b c:bool, a && (b || c) = a && b || a && c. 
  apply demorgan1.
Qed.

Lemma complements_or : forall a:bool, a || ! a = true.
  apply orb_neg_b. (* can not be proved by truth_table_tactic. *)
Qed.

Lemma complements_and : forall a:bool, a && ! a = false.
  apply andb_neg_b.
Qed.


(** The above 10 properties define a boolean algebra, or a distributive complemented lattice. *)

Lemma idempotancy_or : forall a:bool, a || a = a.
  truth_table_tactic.
Qed.

Lemma idempotancy_and : forall a:bool, a &&  a = a.
  truth_table_tactic.
Qed.

Lemma bounded_false_or : forall b:bool, b || false = b.
  apply orb_b_false.
Qed.

Lemma bounded_true_or : forall b:bool, b || true = true.
  apply orb_b_true.
Qed.

Lemma bounded_false_and : forall b:bool, b && false = false.
  apply andb_b_false.
Qed. 

Lemma bounded_true_and : forall b:bool, b && true = b.
 truth_table_tactic.
Qed.

Lemma bounded_false_or2 : forall b:bool, false || b  = b.
 truth_table_tactic.
Qed.

Lemma bounded_true_or2 : forall b:bool, true || b  = true.
 truth_table_tactic.
Qed.

Lemma bounded_false_and2 : forall b:bool, false && b  = false.
 truth_table_tactic.
Qed.
Lemma bounded_true_and2 : forall b:bool, true && b  = b.
 truth_table_tactic.
Qed.
Lemma negation_false : ! false = true.
  reflexivity.  
Qed.

Lemma negation_true : ! true = false.
  reflexivity.
Qed.

Lemma deMorgan_or : forall a b:bool, ! (a || b) = ! a && ! b.
  apply negb_orb.
Qed.

Lemma deMorgan_and : forall a b:bool, ! (a && b) = ! a || ! b.
  apply negb_andb.
Qed.

Lemma involution : forall b:bool, negb (negb b) = b.
  apply negb_elim.
Qed.


(** 5 basic properties of xor 
  Reference: http://www.cs.umd.edu/class/sum2003/cmsc311/Notes/BitOp/xor.html
*)

Lemma xorb_b_false : forall b : bool, b (+) false = b.
  truth_table_tactic.
Qed. 

Lemma xorb_b_true : forall b : bool, b (+) true = ! b.
  truth_table_tactic.
Qed. 

Lemma xorb_b_b : forall b : bool, b (+) b = false.
  truth_table_tactic.
Qed. 

Lemma associativity_xor : forall a b c:bool, a (+) (b (+) c) = a (+) b (+) c.
  truth_table_tactic.
Qed.

Lemma commutativity_xor : forall a b :bool, a (+) b = b (+) a.
  truth_table_tactic.
Qed.

(** properties of nor (-) *)
Lemma norb_b_false : forall b : bool, b (-) false = ! b.
  truth_table_tactic.
Qed. 

Lemma norb_b_true : forall b : bool, b (-) true = false.
  truth_table_tactic.
Qed. 

Lemma norb_b_b : forall b : bool, b (-) b = ! b.
  truth_table_tactic.
Qed. 

(*
Lemma associativity_nor : forall a b c:bool, a (-) (b (-) c) = a (-) b (-) c.
  truth_table_tactic3 a b c.
Qed.
*)

Lemma commutativity_nor : forall a b :bool, a (-) b = b (-) a.
  truth_table_tactic.
Qed.

(** represent and,or,xor,not by nor. *)
Lemma and_nor : forall a b : bool, a && b = !a (-) !b.
  truth_table_tactic.
Qed.

Lemma or_nor : forall a b : bool, a || b = ! (a (-) b).
  truth_table_tactic.
Qed.

Lemma xor_nor : forall a b : bool, a (+) b = (!a (-) !b) (-) (a (-) b).
  truth_table_tactic.
Qed.

(** properties of beq (==) *)

Lemma eqb_b_b : forall b : bool, b == b = true.
  truth_table_tactic.
Qed. 

Lemma eqb_b_negb : forall b : bool, b == ! b = false.
  truth_table_tactic.
Qed. 

Lemma associativity_beq : forall a b c:bool, a == (b == c) = a == b == c.
  truth_table_tactic.
Qed.

Lemma commutativity_beq : forall a b :bool, a == b = b == a.
  truth_table_tactic.
Qed.

(** relation between xor and other operators. *)
Lemma eqb_eq_neg_xorb : forall a b : bool, (a==b) = ! (a(+)b).
  truth_table_tactic.
Qed.

Lemma eqb_eq_and_or : forall a b : bool, 
  (a==b) = (a && b) || (!a && !b).
  truth_table_tactic.
Qed.

(** another equivalent definition of xor. *)
Lemma xor_and_neg : forall a b, a (+) b = a && ! b || ! a && b.
  truth_table_tactic.
Qed.

Lemma xor_is_neq : forall a b, a (+) b = !(a == b).
  truth_table_tactic.
Qed.


(** tactic for boolean equality with 1 argument. *)
Ltac truth_table_tactic1 a := 
  intros;  destruct a;
  trivial.

(** tactic for boolean equality with 2 arguments. *)
Ltac truth_table_tactic2 a b := 
  intros;
  destruct a; destruct b;
  trivial.

(** tactic for boolean equality with 3 arguments. *)
Ltac truth_table_tactic3 a b c := 
  intros;
  destruct a; destruct b; destruct c;
  trivial.

(** tactic for boolean equality with 4 arguments. *)
Ltac truth_table_tactic4 a b c d := 
  intros;
  destruct a; destruct b; destruct c; destruct d;
  trivial.

Ltac truth_table_tactic5 a b c d e := 
  intros;
  destruct a; destruct b; destruct c; 
  destruct d; destruct e;
  trivial.

Ltac truth_table_tactic6 a b c d e f:= 
  intros;
  destruct a; destruct b; destruct c; destruct d;
  destruct e; destruct f;
  trivial.

(* relation between eqb and eqg. *)
Lemma eqg_eq_eqb : forall (b1 b2:bool),
 ((eqg b1 b2) = true) = ((eqb b1 b2) = true).
  truth_table_tactic2 b1 b2; simpl; easy.
Qed.

Lemma eqg_subst :
  forall (P:bool -> Prop) (b1 b2:bool), eqg b1 b2 = true -> P b1 -> P b2.
intros P b1 b2. rewrite eqg_eq_eqb. apply eqb_subst.
Qed.

Lemma eqg_reflx : forall b:bool, eqg b b = true.
intro; truth_table_tactic.
Qed.

Lemma eqg_prop : forall a b:bool, eqg a b = true -> a = b.
intros a b.  rewrite eqg_eq_eqb. apply eqb_prop.
Qed.

Lemma eqg_true_iff : forall a b:bool, eqg a b = true <-> a = b.
intros a b.  rewrite eqg_eq_eqb. apply eqb_true_iff.
Qed.

Lemma eqg_false_iff : forall a b:bool, eqg a b = false <-> a <> b.
intros a b. truth_table_tactic2 a b;simpl; easy.
Qed.

(** bit vectors. *)

(** vector of bool. (cons1 n a b) iff b has n elements. *)
Inductive bv1  : nat -> Set :=
  | nil1  : bv1 0
  | cons1 : forall n:nat, bool -> bv1 n -> bv1 (S n).

(** vector of bool * bool. *)
Inductive bv2  : nat -> Set :=
  | nil2  : bv2 0
  | cons2 : forall n:nat, (bool*bool) -> bv2 n -> bv2 (S n).

(** 2^n = 1 shift left n. *)
Fixpoint sftl (n:nat) : nat :=
  match n with
    | 0 => 1
    | (S n) => let m := sftl n in m+m
  end.

(** split one (bv2 n) to (bv1 n) * (bv1 n). *)
Fixpoint split2 (n:nat) (ab:(bv2 n)) {struct ab} : (bv1 n) * (bv1 n) :=
  match ab in bv2 n return (bv1 n) * (bv1 n) with
    | nil2 => (nil1,nil1)
    | (cons2 n' (a,b) tl) => 
      let (tl1,tl2) := split2 n' tl in
	((cons1 n' a tl1),(cons1 n' b tl2))
  end.

(** map fst on (bv2 n). *)
Fixpoint fstn (n:nat) (ab:(bv2 n)) {struct ab} : (bv1 n) :=
  match ab in bv2 n return (bv1 n) with
    | nil2 => nil1
    | (cons2 n' p tl) => (cons1 n' (fst p) (fstn n' tl))
  end.

(** map snd on (bv2 n). *)
Fixpoint sndn (n:nat) (ab:(bv2 n)) {struct ab} : (bv1 n) :=
  match ab in bv2 n return (bv1 n) with
    | nil2 => nil1
    | (cons2 n' p tl) => (cons1 n' (snd p) (sndn n' tl))
  end.

Lemma rc_fstn_cons2 : forall (abn : bool * bool) (n:nat) (ab : (bv2 n)),
  (fstn (S n) (cons2 n abn ab)) = (cons1 n (fst abn) (fstn n ab)).
Proof.
  intro a; intro b.     (* move a,b to hypothesis. *)
  induction ab.
  simpl; trivial.       (* base case solved. *)
  simpl fstn in |- *.   (* break (fstn (S (S n)) ... *)
  trivial.
Qed.

Lemma rc_sndn_cons2 : forall (abn : bool * bool) (n:nat) (ab : (bv2 n)),
  (sndn (S n) (cons2 n abn ab)) = (cons1 n (snd abn) (sndn n ab)).
Proof.
  intro; induction ab.
  simpl in |- *; reflexivity.
  simpl in |- *; reflexivity.
Qed.

(** conversion from bool, bool vector to nat. *)

Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Notation "# x" := (bool_to_nat x) (at level 30, right associativity)  : gate_scope.

(** conversion from bool (bv1 n) to natural number. *)
Fixpoint bv2n (n:nat) (bl : (bv1 n)) {struct bl} : nat :=
  match bl in (bv1 n) return nat with
    | nil1 => 0
    | (cons1 n' hd tl) => #hd * (sftl n')+(bv2n n' tl)
  end.

Hint Rewrite xorb_true_r xorb_true_l andb_true_r andb_true_l orb_false_r orb_false_l
   andb_false_r andb_false_l orb_true_r orb_true_l 
   negb_involutive orb_negb_r andb_negb_r idempotancy_or idempotancy_and
   : and_or_neg_simp.

Hint Rewrite
   xorb_b_false xorb_b_true xorb_b_b 
  : xor_simp.
   

Hint Rewrite complements_or complements_and idempotancy_or idempotancy_and 
 bounded_false_or bounded_true_or bounded_false_and bounded_true_and
 negation_false negation_true involution
 xorb_b_false xorb_b_true xorb_b_b eqb_b_b eqb_b_negb
 absorption_or absorption_and
 : base_bool_simp.

Hint Rewrite associativity_and associativity_or associativity_xor associativity_beq
 distributivity_or  deMorgan_and deMorgan_or
 : base_bool_norm.

