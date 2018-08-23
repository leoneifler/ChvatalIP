Require Import SparseMatrix.
Require Import Coq.ZArith.Znat.
Require Import Coq.ZArith.ZArith_base.
From mathcomp Require Import all_ssreflect.

(* Compute 2^n - 1 *)
Definition pow2_min1 (n : nat)  :=
  ( Z.to_nat((2%Z)^(Z.of_nat n)+(-1)%Z) ).

(* Compute 2^n *)
Definition pow2 (n : nat)  := 
  Z.to_nat((2%Z)^(Z.of_nat n)).

(* Given a binary number and 0 as currpos, returns the set-representation of the binary number
   if p = 2^a_1 + 2^a_2 + ... returns \{a_1,a_2,...\} as a list*)
Fixpoint list_rep (p : positive ) (currpos : nat) : seq nat :=
  match p with
  | xH => currpos :: nil
  | xI n' => (list_rep  n' (currpos + 1)) ++ (currpos :: nil)
  | xO n' => list_rep  n' (currpos + 1)
  end.

(* Returns the list-representation of a binary representation of n *)
Fixpoint list_nat (n : nat) : list nat :=
  list_rep (Pos.of_nat n) 0.

(* Generate the powerset of the set \{1,...,n\} *)
Definition gen_powerset (n : nat) : list (list nat ) :=
  let s := iota 1 (pow2_min1 n) in
  map list_nat s.

(* Returns true, if l1 and l2 share at least one element *)
Fixpoint intersect (l1 l2 : seq  nat) : bool :=
  match l1 with
  | nil => false
  | h :: t => if  h \in  l2 then true
             else intersect t l2
  end.

(* Relation definition for less than *)
Definition ltb : (rel nat) := (fun n => (fun m => m < n)).

(* returns true if all elements of l1 exist in l2*)
Definition subset (l1 l2 : seq nat) : bool :=
  if l1 == l2 then false else
    subseq (sort ltb l1)(sort ltb l2).

Definition subseteq (l1 l2 : seq nat) :=
  subseq (sort ltb l1)(sort ltb l2).
