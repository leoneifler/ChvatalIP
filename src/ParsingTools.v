Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.
Require Import ZArith.Znat.

Set Implicit Arguments.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.all_ssreflect.

Require Import ListString.All.
Require Import ListString.Conversion.
Require Import ListString.Char.

Require Import SparseMatrix.
Import LString.
Import ListNotations.

Local Open Scope char_scope.

(** Convert nat <= 9 to ascii*)
Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

(** Helper to convert nat to string *)
Fixpoint writeNatAux (time n : nat) : LString.t :=
  let char := (natToDigit (n mod 10)) in
  match time with
    | 0 => [::char]
    | S time' =>
      match n / 10 with
        | 0 => [::char]
        | n' => char :: writeNatAux time' n'
      end
  end.

(** Convert nat to string *)
Definition writeNat (n : nat) : LString.t :=
  rev (writeNatAux n n).

(** Convert Integer to String *)
Definition writeZ (z : Z) : LString.t :=
  if (z <? 0)%Z then  "-"  :: (writeNat (Z.abs_nat z))
  else  "+" :: (writeNat (Z.to_nat z)).

Definition writeE ( a : (prod nat  Z) )  : LString.t  :=
  let (n,z) := a in
  "(" :: (writeNat n) ++ [","] ++ (writeZ z) ++ [")"].

Definition writeE' ( a : (prod nat  Z) )  : LString.t  :=
  let (n,z) := a in
  if n == 0 then [" "; "<"; "="; " "] ++ writeZ z 
  else (writeZ z) ++  [" ";"x";"_";" "] ++ (writeNat n) ++ [" "]. 

(**  Convert sparse vector to string *)
Definition toStringSvec ( v : svec)  : LString.t  :=
  foldr cat nil [seq (writeE x) | x <- v].

(** Convert sparse vector to inequality with x_index-variables *)
Definition toStringIneqSvec ( v : svec ) : LString.t :=
  foldr cat nil [seq (writeE' x) | x <- v].

(** Convert sparse matrix to LString *)
Definition  toString (m : smat) : LString.t :=
  join  ([Char.n])  [seq (toStringIneqSvec h) | h <- m].


Section AsciiEqType.
  Lemma eqasciiP : Equality.axiom Char.eqb.
  Proof.
    rewrite /Equality.axiom /Char.eqb /Char.compare /=  => x y.
    remember (N_of_ascii x) as a.
    remember (N_of_ascii y) as b.
    rewrite -(N.eqb_compare a b).
    apply: (iffP idP) => H; inversion H.
    move: H1; rewrite N.eqb_eq => H1.
      by rewrite -(ascii_N_embedding x) -Heqa H1  Heqb (ascii_N_embedding y).
        by rewrite Heqa Heqb H N.eqb_refl.
  Qed.

Definition ascii_eqMixin := Equality.Mixin eqasciiP.
Canonical AsciieqType := Equality.Pack ascii_eqMixin ascii .

End AsciiEqType.


Import ListNotations.
Local Open Scope char_scope.

Definition isWhite (c : ascii) : bool :=
  ListString.Char.is_white_space c.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    (97 <=? n) && (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    ((65 <=? n) && (n <=? 90)) || (isLowerAlpha c).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     (48 <=? n) && (n <=? 57).

Definition isSign (c : ascii ) : bool :=
   c == "-".

Inductive chartype := white | alpha | digit | sign | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    digit
  else if isDigit c then
    digit
  else if isSign c then
    digit
  else
    digit.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Close Scope char_scope.