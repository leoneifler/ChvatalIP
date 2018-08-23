Require Import SparseMatrix.
Require Import SeqSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Numbers.BinNums.
Require Import Coq.MSets.MSetRBT.

Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.BinInt.

Set Implicit Arguments.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.all_ssreflect.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export ListNotations.

Import ListNotations.

(* Create ideal inequalities for one fixed set n2, for all sets 1,..,setA*)
Definition ideal_ineq_helper (n1 n2 : nat) : smat :=
  let s := rev(iota 1 n1.+1) in
  filter (predC1 []) (map (fun l  => if SeqSet.subset (list_nat l)(list_nat n2) then [::(0,0%Z);(l,(-1)%Z);(n2,1%Z)]
             else []) s).
(**Create ideal inequalities for all combinations of sets in [n] *)
Definition ideal_ineq (n : nat) : smat :=
  let theset := pow2_min1 n in
  let s:= rev(iota 1 theset.+1) in
  flatten (map (ideal_ineq_helper theset) s).

(**Creat intersection inequalities for fixed n2 and all elements in [n1]*)
Definition inter_ineq_helper (nps n1 n2: nat) : smat :=
  let s := rev( iota 1 (pow2_min1 n1)) in
  filter (predC1 []) (map (fun l => if  intersect (list_nat l) (list_nat n2) then []
                     else [(0, (1)%Z);(l + nps,1%Z);(n2 + nps,1%Z)]) s).

(**Create inter inequalities for all combinations of sets in [n]*)
Definition inter_ineq  (n : nat) : smat :=
  let theset := pow2_min1 n in
  let s := rev (iota 1 theset) in
  flatten (map (inter_ineq_helper theset n) s).

(*Create contrainment inequalitites for all elements in [n]*)
Definition containment_ineq (n : nat) : smat :=
  let cardinality := pow2_min1 n in
  let s := rev(iota 1 cardinality) in
  map (fun (l : nat) => [(0,0%Z); (l + cardinality, 1%Z); (l, (-1)%Z)] ) s.

(*Create all star inequalities for one element of [n]*)
Fixpoint star_ineq_helper (n i : nat) : svec :=
  let nps := pow2_min1 n in
  let s := rev (iota 1 nps) in
  (0, (-1)%Z) :: flatten (map (fun l => if i \in list_nat l then [(l,1%Z);(l + nps, (-1)%Z)]
      else  [(l + nps, (-1)%Z)]) s).

(*Create all star inequalitites*)
Definition star_ineq (n : nat)  : smat :=
  let cardinality := pow2_min1 n in
  let s := rev (iota 0 n) in
  map (star_ineq_helper n) s.

(*Create bounding inequalitites *)
Fixpoint bounds (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota 1 cPower) in
  flatten(  map (fun (l : nat) => [[(0, 1%Z); (l , 1%Z)];  [(0, 1%Z); (l + cPower , 1%Z)];  [(0, 0%Z); (l, (-1)%Z)];  [(0, 0%Z); (l + cPower , (-1)%Z)]]) s).

(*Concatenate all sparse matrices for a specifif n *)
Definition create_mat (n : nat ) : smat :=
  let mat :=           (inter_ineq  n) ++
                       (ideal_ineq  n) ++
                       (star_ineq   n)  ++
                       (containment_ineq n) ++
                       (bounds n) in
  [seq ordervec s | s <- mat].


