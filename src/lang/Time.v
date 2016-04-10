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
End Time.

Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Inductive mem (interval:t) (x:Time.t): Prop :=
  | mem_intro
      (FROM: Time.lt interval.(fst) x)
      (TO: Time.le x interval.(snd))
  .

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
