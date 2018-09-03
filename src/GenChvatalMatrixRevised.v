
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
Definition generation_ineq_helper (n1 n2 : nat) : smat :=
  let s := rev(iota 1 n1) in
  filter (predC1 []) (map (fun l  => if SeqSet.subseteq (list_nat l)(list_nat n2)
                                  then [::(0,0%Z);(l,(-1)%Z);(n2 +  n1,1%Z)]
                                  else []) s).

(**Create ideal inequalities for all combinations of sets in [n] *)
Definition generation_ineq (n : nat) : smat :=
  let theset := pow2_min1 n in
  let s:= rev(iota 1 theset.+1) in
  flatten (map (generation_ineq_helper theset) s).

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

(* fixings *)
Definition setXOne (l : nat) : bool :=
  (size (list_nat l) == 1) || (subseteq (list_nat l) (rev (iota 0 4)) ).

(*)Compute list_nat 14.
Compute (iota 0 4).
Compute subseteq (list_nat 14) (iota 0 4).*)

Definition setYZero (n l : nat) : bool :=
  (size (list_nat l) <= 2) || (size (list_nat l) == n).

(* Create bounding inequalities (incorporate fixings)*)
Definition boundsrev (n : nat) : smat :=
  let cPower := pow2_min1 n in
  let s := rev(iota 1 cPower) in
  let f := (fun l : nat => if setXOne l
                      then [[(0,1%Z);(l,1%Z)];[(0,(-1)%Z);(l,(-1)%Z)]] (* fixed to 1 *)
                      else [[(0,1%Z);(l,1%Z)];[(0,0%Z);(l,(-1)%Z)]] ) in
  let f' := (fun l : nat => if setYZero n l
                      then [[(0,0%Z);(l + cPower,1%Z)];[(0,0%Z);(l + cPower,(-1)%Z)]] (* fixed to 0 *)
                       else [[(0,1%Z);(l + cPower,1%Z)];[(0,0%Z);(l + cPower,(-1)%Z)]] ) in
  [(0,0%Z); (2 * pow2_min1 n + 1, (-1)%Z)] :: flatten [seq f x | x <- s] ++ flatten [seq f' x | x <- s].

(* Create berge-inequality *)
Definition berge (n : nat) : svec :=
  let nps := pow2_min1 n in
  let s := rev (iota 1 nps) in
  (0,0%Z) :: (flatten (map (fun l => [(l,(-1)%Z)]) s)) ++ (flatten (map (fun l => [(l + nps,2%Z)]) s)).


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


Definition create_mat ( n : nat) : smat :=
  let mat := (inter_ineq n) ++
             (maxstar_ineq n) ++
             (containment_ineq n) ++
             (ideal_ineq n) ++
             (bounds n) in
  [seq ordervec s | s <- mat].

(*Concatenate all sparse matrices for a specifif n *)
Definition create_mat_rev (n : nat ) : smat :=
  let mat :=           (inter_ineq  n) ++
                       (generation_ineq  n) ++
                       (maxstar_ineq   n)  ++
                       (boundsrev n) ++
                       [(berge n)] in
  [seq ordervec s | s <- mat].
