
Require Import SparseMatrix.
Require Import GenChvatalMatrix.
Require Import SeqSet.
(*Require Import sort_powerset.*)
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
Definition ideal_inter_ineq_helper (n1 n2 : nat) : smat :=
  let s := rev(iota 1 n1) in
  filter (predC1 []) (map (fun l  => if SeqSet.subseteq (list_nat l)(list_nat n2)
                                  then [::(0,0%Z);(l,(-1)%Z);(n2 +  n1,1%Z)]
                                  else []) s).
(**Create ideal inequalities for all combinations of sets in [n] *)
Definition ideal_inter_ineq (n : nat) : smat :=
  let theset := pow2_min1 n in
  let s:= rev(iota 1 theset.+1) in
  flatten (map (ideal_inter_ineq_helper theset) s).

(*Create all star inequalities for one element of [n]*)
Fixpoint maxstar_ineq_helper (n i : nat) : svec :=
  let nps := pow2_min1 n in
  let s := rev (iota 1 nps) in
  (0,0%Z) :: (2 * nps + 1, (-1)%Z) :: flatten (map (fun l => if i \in list_nat l then [(l,1%Z)]
      else  []) s).

(*Create all star inequalitites*)
Definition maxstar_ineq (n : nat)  : smat :=
  let cardinality := pow2_min1 n in
  let s := rev (iota 0 n) in
  map (maxstar_ineq_helper n) s.

(*Create bounding inequalitites *)
Fixpoint bounds (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota 1 cPower) in
  [(0,0%Z); (2 * pow2_min1 n + 1, (-1)%Z)] :: flatten(  map (fun (l : nat) => [[(0, 1%Z); (l , 1%Z)];  [(0, 1%Z); (l + cPower , 1%Z)];  [(0, 0%Z); (l, (-1)%Z)];  [(0, 0%Z); (l + cPower , (-1)%Z)]]) s).


Definition boundsrev (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota 1 cPower) in
  let f := (fun l : nat => if size (list_nat l) == 1
                      then [[(0,1%Z);(l,1%Z)];[(0,(-1)%Z);(l,(-1)%Z)]]
                      else [[(0,1%Z);(l,1%Z)];[(0,0%Z);(l,(-1)%Z)]] ) in
  let f' := (fun l : nat => if size (list_nat l) <= 2
                      then [[(0,0%Z);(l + cPower,1%Z)];[(0,0%Z);(l + cPower,(-1)%Z)]]
                       else [[(0,1%Z);(l + cPower,1%Z)];[(0,0%Z);(l + cPower,(-1)%Z)]] ) in
  [(0,0%Z); (2 * pow2_min1 n + 1, (-1)%Z)] :: flatten [seq f x | x <- s] ++ flatten [seq f' x | x <- s].


Definition setZero (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota cPower.+1 (cPower)) in
  let s' := [seq x <- s| size (list_nat (x - cPower)) <= 2 ] in
  [seq [(0,0%Z);(x,1%Z)]| x <- s'].

Definition setOne (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota 1 cPower) in
  let s' := [seq x <- s | size (list_nat x) == 1 ] in
        [seq [(0,1%Z);(x,(-1)%Z)] | x <- s'].



(*Concatenate all sparse matrices for a specifif n *)
Definition create_mat_rev (n : nat ) : smat :=
  let mat :=           (inter_ineq  n) ++
                       (ideal_inter_ineq  n) ++
                       (maxstar_ineq   n)  ++
                       (boundsrev n) in
  [seq ordervec s | s <- mat].


