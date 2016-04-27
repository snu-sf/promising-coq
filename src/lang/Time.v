Require Import Orders.

Require Import sflib.
Require Import paco.

Require Import DataStructure.
Require Import DenseOrder.
Require Import Basic.
Require Import Event.

Set Implicit Arguments.

Module Time.
  Include DenseOrder.

  Lemma lt_le_lt a b c
        (AB: lt a b)
        (BC: le b c):
    lt a c.
  Proof.
    apply le_lteq in BC. des; subst; auto.
    etransitivity; eauto.
  Qed.

  Lemma le_lt_lt a b c
        (AB: le a b)
        (BC: lt b c):
    lt a c.
  Proof.
    apply le_lteq in AB. des; subst; auto.
    etransitivity; eauto.
  Qed.

  Lemma le_lt_dec (lhs rhs:t): {le lhs rhs} + {lt rhs lhs}.
  Proof.
    generalize (compare_spec lhs rhs).
    destruct (compare lhs rhs).
    - left. inv H. reflexivity.
    - left. inv H. apply Time.le_lteq. auto.
    - right. inv H. auto.
  Defined.

  Definition max (lhs rhs:t): t :=
    if le_lt_dec lhs rhs
    then rhs
    else lhs.

  Lemma max_comm lhs rhs: max lhs rhs = max rhs lhs.
  Proof.
    unfold max.
    destruct (le_lt_dec lhs rhs), (le_lt_dec rhs lhs); auto.
    - apply le_lteq in l. apply le_lteq in l0.
      des; auto.
      rewrite l0 in l. apply lt_strorder in l. done.
    - rewrite l0 in l. apply lt_strorder in l. done.
  Qed.

  Lemma max_l lhs rhs:
    le lhs (max lhs rhs).
  Proof.
    unfold max. destruct (le_lt_dec lhs rhs); auto.
    apply le_lteq. auto.
  Qed.

  Lemma max_r lhs rhs:
    le rhs (max lhs rhs).
  Proof.
    rewrite max_comm. apply max_l.
  Qed.

  Lemma max_spec_le lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (max lhs rhs) o.
  Proof.
    unfold max. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Lemma max_spec_lt lhs rhs o
        (LHS: lt lhs o)
        (RHS: lt rhs o):
    lt (max lhs rhs) o.
  Proof.
    unfold max. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Lemma max_cases lhs rhs:
    max lhs rhs = lhs \/ max lhs rhs = rhs.
  Proof.
    unfold max. destruct (le_lt_dec lhs rhs); auto.
  Qed.
End Time.

Ltac timetac :=
  repeat
    (try match goal with
         | [H: Some _ = None |- _] => inv H
         | [H: None = Some _ |- _] => inv H
         | [H: ?x <> ?x |- _] => by contradict H
         | [H: Time.lt ?x ?x |- _] =>
           apply Time.lt_strorder in H; by inv H
         | [H1: Time.lt ?a ?b, H2: Time.le ?b ?c |- _] =>
           exploit (@Time.lt_le_lt a b c); eauto;
           let H := fresh "H" in
           intro H; apply Time.lt_strorder in H; by inv H

         | [H: Some _ = Some _ |- _] => inv H

         | [H: context[Time.eq_dec ?a ?b] |- _] =>
           destruct (Time.eq_dec a b)
         | [H: context[Time.le_lt_dec ?a ?b] |- _] =>
           destruct (Time.le_lt_dec a b)
         | [|- context[Time.eq_dec ?a ?b]] =>
           destruct (Time.eq_dec a b)
         | [|- context[Time.le_lt_dec ?a ?b]] =>
           destruct (Time.le_lt_dec a b)
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
    destruct (Time.le_lt_dec x lb).
    - right. intro X. inv X. ss. timetac.
    - destruct (Time.le_lt_dec x ub).
      + left. econs; s; auto.
      + right. intro X. inv X. ss. timetac.
  Defined.

  Definition disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: mem lhs x)
      (RHS: mem rhs x),
      False.

  Lemma mem_ub
        lb ub (LT: Time.lt lb ub):
    mem (lb, ub) ub.
  Proof.
    econs; s; auto. reflexivity.
  Qed.
End Interval.
