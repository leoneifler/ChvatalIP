Require Import Coq.Arith.Arith_base.
Require Import Coq.omega.Omega.

Set Implicit Arguments.
From mathcomp Require Import all_ssreflect.

(** Proof equality type for Z, to make comparison easier *)
Section ZeqType.
  Variable z1 z2 : Z.

  Lemma inj_eqb_neg: forall p q : positive, (p =? q)%positive = (Z.neg p =? Z.neg q)%Z.
  Proof.
    move => p q.
    elim: p; elim q; by []. Qed.

  Lemma eqzP : Equality.axiom Z.eqb.
  Proof.
    rewrite /Equality.axiom; move=> n m; apply: (iffP idP) => [|<-].
    elim: n; elim  m; try by []; 
      move => p p' H;
               try rewrite -Zpos_eq_iff;
               try rewrite Pos2Z.inj_neg_iff;
               try rewrite -Pos2Z.inj_eqb in H;
               try rewrite -inj_eqb_neg in H;
                 by apply : Peqb_true_eq.
    elim n; try by []; move => p; try rewrite -Pos2Z.inj_eqb; try rewrite  -inj_eqb_neg; by elim p.
    Qed. 

Definition z_eqMixin := Equality.Mixin eqzP.
Canonical ZeqType := Equality.Pack z_eqMixin Z.

End ZeqType.


Definition svec := seq (nat * Z).
Definition smat := seq (svec).

Definition lexlarger (a b : nat * Z) : bool  :=
  (fst(a) < fst(b)) || ( (fst(a) ==  fst(b)) && (snd(b) <? snd(a))%Z ).

Inductive lexlarger_rel : (nat*Z) -> (nat * Z) -> Prop :=
| lex_ind : forall a b, fst a < fst b -> lexlarger_rel a b
| lex_val : forall x y z, (z < y)%Z -> lexlarger_rel (x,y) (x,z).

Notation "a ?>l b" := (lexlarger a b) (at level 0).

Fixpoint lexlarger_seq (v1 v2 : svec) : bool :=
  if (v1,v2) is (h1 :: t1, h2 :: t2) then
    (h1 ?>l h2) || ((h1 == h2) && lexlarger_seq t1 t2 )
  else v2 == nil.

Notation "v1 ?>ls v2" := (lexlarger_seq v1 v2) (at level 0).

Inductive lexlarger_seq_rel :  svec -> svec -> Prop :=
| lexlarger_nil : forall al, lexlarger_seq_rel al nil
| lexlarger_ind : forall x y al bl, lexlarger_rel x y -> lexlarger_seq_rel( x :: al) (y :: bl)
| lexlarger_cons : forall x al bl, lexlarger_seq_rel al bl -> lexlarger_seq_rel (x :: al) (x :: bl).

Notation "v1 >ls v2" := (lexlarger_seq_rel v1 v2) (at level 0).
Notation "a >l b" := (lexlarger_rel a b) (at level 0).


Lemma lexlarger_ref_false : forall (x : (nat * Z)),  x ?>l x = false.
Proof.
  move => x. rewrite  /lexlarger /=. elim x => /=.
  move => n z. by rewrite eq_refl Z.ltb_irrefl /= ltnn. 
Qed.


Lemma lex_reflect: forall x y, reflect (lexlarger_rel x y) (lexlarger x y).
Proof.
  move => x y; rewrite /lexlarger;  apply: (iffP idP); last first.
  - move => H; elim H; move => a b H2 /=. apply/idP/orP. by left. 
    move => H3; apply/idP/orP; right. apply /idP/andP. split. by [].
    move: H3. by rewrite -(Z.ltb_lt H2 b). 
  - elim: x => n1 z1; elim: y=> n2 z2 /= /Bool.orb_true_iff. case => [H2 | ].
    apply lex_ind. by [].
    rewrite Bool.andb_true_iff Z.ltb_lt Nat.eqb_eq => H. destruct H.
    rewrite H. by apply lex_val. Qed.


Lemma not_greater_eq : forall a b,  ~ ( lexlarger_rel a b ) -> ~ (lexlarger_rel b a) -> b = a.
Proof.
  move => a p.
  elim a => n1 z1; elim p => n2 z2 /=.
  case: (n1 < n2) /ltP => H. move => H1 H2; exfalso. by apply: H1; apply: lex_ind; apply /ltP. 
  case: (n2 < n1) /ltP => H'.  move => H1 H2. exfalso;  by apply H2; apply lex_ind; apply /ltP.
  case: (n1 == n2) /eqP. move => ->.  
  case: (z1 <? z2)%Z /Z.ltb_spec0 => t4. move => H1 H2; exfalso; apply H2; by apply lex_val.
  case: (z2 <? z1)%Z /Z.ltb_spec0 => t5.  move => H1; exfalso; apply H1; by apply lex_val.
  case: (z1 == z2) /eqzP. move => ->. by []. move => t6; omega.
  move => t1; exfalso; omega. Qed.

Lemma lex_reflect_seq: forall x y, reflect (lexlarger_seq_rel x y) (lexlarger_seq x y).
Proof.
  move => x y; apply: (iffP idP). move: x.
  elim y => [x H| p l IHx x]; first by apply lexlarger_nil.
  case x => [H| p2 l2]; first by exfalso; move: H.
  - rewrite /lexlarger_seq. case: (p2 == p) /eqP. rewrite -/lexlarger_seq.  move => ->.
    rewrite lexlarger_ref_false /= => H. apply: lexlarger_cons.
    apply: (IHx l2 H).
    rewrite -/lexlarger_seq . move => c /Bool.orb_true_iff H. destruct H. apply lexlarger_ind. by apply: lex_reflect.
    move: H => /=. by [].
  - move => H; elim H.
      by move => al; case: al.
      move => x0 y0 al bl H2. rewrite /lexlarger_seq. apply /idP/orP. left.
        by apply: (introT (lex_reflect x0 y0)).
  - move => x0 al bl H1 /=. move ->.   apply /idP/orP; right. by  rewrite (eq_refl x0).
    Qed.

Definition rellex : (rel svec) := (fun n => (fun m => m ?>ls n)).
Definition order (base : smat) := sort rellex base.
Definition ordervec (inp : svec) := sort (fun n => (fun m => m ?>l n)) inp.

Fixpoint diffvec (m1 m2 : smat) :  smat :=
  if m1 is (h1 :: t1) then
    if m2 is (h2 :: t2) then
      if h1 == h2 then diffvec t1 t2
      else h1 :: [::h2]
    else [::h1]
  else m2.
         
    