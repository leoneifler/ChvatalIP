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
Import ListNotations.

Require Import SparseMatrix.
Require Import ParsingTools.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : LString.t)
                       : seq (LString.t) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : LString.t) : seq LString.t :=
  (tokenize_helper white [] ( s)).


Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.

Arguments SomeE {X} _.
Arguments NoneE {X} _.

(** Some syntactic sugar to make writing nested match-expressions on
    optionE more convenient. *)

Notation "'DO' ( x , y ) <== e1 ; e2"
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => NoneE err
       end)
   (right associativity, at level 60).

Notation "'DO' ( x , y ) <-- e1 ; e2 'OR' e3"
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => e3
       end)
   (right associativity, at level 60, e2 at next level).

(* ----------------------------------------------------------------- *)
(** *** Generic Combinators for Building Parsers *)

Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t::acc) steps' xs'
  end.

(** A (step-indexed) parser that expects zero or more [p]s: *)

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(** A parser that expects a given token, followed by [p]: *)

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

(** A parser that expects a particular token: *)

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE(tt, xs)).

(** Numbers: *)

(** Convert string to nat, 0 default *)
Definition extractNumber (x : LString.t) : nat :=
    if all isDigit x then
       (foldl (fun n d => 10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
               0 x )
    else 0.

Local Open Scope char_scope.
(**Convert string to int, 0 default*)
Definition extractInt (l : LString.t) : Z :=
  if all isDigit l then Z.of_nat (extractNumber l)
  else if head " " l == "-" then Zneg (Pos.of_nat ( extractNumber (behead l)))
       else Z0.

(** Takes a list of strings and converts each of them to an int (0 if not convertible) *)
Fixpoint parse (l :  seq LString.t) : seq Z :=
  [seq extractInt x | x <- l].

(** Remove the first 4 elements in a list (not need in this case)*)
Definition trim_to_rel (l : seq Z) : seq Z :=
  drop 4 l.

Fixpoint group (T : Type) (s : seq T) : seq (T * T) :=
  match s with
  | [] => nil
  | h1 :: h2 :: t => (h1,h2) :: group t
  | _ => []
  end.

(** Convert a list of integers into a sparse vector, the booelean flips all the values if it is false*)
Fixpoint convert2sparsevec  (ln : list Z)(vartable : list nat)(isG : bool ) : svec :=
  let ln2 := group ln in
  let idx := (fun x => 1 + nth 0  vartable  (Z.abs_nat x)) in
  let elem := (fun b p => if b then (idx p.1, p.2) else (idx p.1, Z.mul p.2 (-1)%Z) ) in
  [seq (elem isG) x | x <- ln2].

Definition a := of_string "C207 L 1 2 18 1 16 1".
Check a.

(** Takes a vipr-line as input and creates the corresponding sparse vector*)
Definition parseline (vartable : list nat) (line : LString.t) : svec :=
  let s := tokenize  line in
  let isLower := ["L"] == nth [" "] s 1 in
  let rhs := if isLower then (0, extractInt (nth [" "] s 2))
             else (0, Z.mul (-1)%Z (extractInt (nth [" "]  s 2))) in
  rhs :: convert2sparsevec (trim_to_rel (parse s)) vartable isLower .


Compute parseline (iota 1 23) a.