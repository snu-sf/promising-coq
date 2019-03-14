Require Import Orders.

Require Import sflib.
From Paco Require Import paco.

Require Import DataStructure.
Require Import DenseOrder.
Require Import Basic.

Set Implicit Arguments.


Module Time := DenseOrder.
Module TimeFacts := DenseOrderFacts.

Ltac timetac :=
  repeat
    (try match goal with
         | [H: Some _ = None |- _] => inv H
         | [H: None = Some _ |- _] => inv H
         | [H: ?x <> ?x |- _] => by contradict H
         | [H: Time.lt ?x ?x |- _] =>
           apply Time.lt_strorder in H; by inv H
         | [H1: Time.lt ?a ?b, H2: Time.le ?b ?a |- _] =>
           exploit (@TimeFacts.lt_le_lt a b a); eauto;
           let H := fresh "H" in
           intro H; apply Time.lt_strorder in H; by inv H

         | [H: Some _ = Some _ |- _] => inv H

         | [H: context[Time.eq_dec ?a ?b] |- _] =>
           destruct (Time.eq_dec a b)
         | [H: context[TimeFacts.le_lt_dec ?a ?b] |- _] =>
           destruct (TimeFacts.le_lt_dec a b)
         | [|- context[Time.eq_dec ?a ?b]] =>
           destruct (Time.eq_dec a b)
         | [|- context[TimeFacts.le_lt_dec ?a ?b]] =>
           destruct (TimeFacts.le_lt_dec a b)
         end;
     ss; subst; auto).

Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Inductive mem (interval:t) (x:Time.t): Prop :=
  | mem_intro
      (FROM: Time.lt interval.(fst) x)
      (TO: Time.le x interval.(snd))
  .

  Lemma mem_dec i x: {mem i x} + {~ mem i x}.
  Proof.
    destruct i as [lb ub].
    destruct (TimeFacts.le_lt_dec x lb).
    - right. intro X. inv X. ss. timetac.
    - destruct (TimeFacts.le_lt_dec x ub).
      + left. econs; s; auto.
      + right. intro X. inv X. ss. timetac.
  Defined.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (FROM: Time.le rhs.(fst) lhs.(fst))
      (TO: Time.le lhs.(snd) rhs.(snd))
  .

  Lemma le_mem lhs rhs x
        (LE: le lhs rhs)
        (LHS: mem lhs x):
    mem rhs x.
  Proof.
    inv LE. inv LHS. econs.
    - eapply TimeFacts.le_lt_lt; eauto.
    - etrans; eauto.
  Qed.

  Lemma mem_ub
        lb ub (LT: Time.lt lb ub):
    mem (lb, ub) ub.
  Proof.
    econs; s; auto. refl.
  Qed.

  Definition disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: mem lhs x)
      (RHS: mem rhs x),
      False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eapply H; eauto.
  Qed.

  Lemma disjoint_imm a b c:
    disjoint (a, b) (b, c).
  Proof.
    ii. inv LHS. inv RHS. ss.
    eapply DenseOrder.lt_strorder.
    eapply TimeFacts.le_lt_lt; [apply TO|apply FROM0].
  Qed.

  Lemma le_disjoint
        a b c
        (DISJOINT: disjoint b c)
        (LE: le a b):
    disjoint a c.
  Proof.
    ii. eapply DISJOINT; eauto. eapply le_mem; eauto.
  Qed.
End Interval.
