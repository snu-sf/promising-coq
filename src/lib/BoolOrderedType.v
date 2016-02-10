Require Import Orders.
Require Import List.

Set Implicit Arguments.
Import ListNotations.

Module Type S.
  Parameter (t:Type).
  Parameter (eq_dec: forall (lhs rhs:t), {lhs = rhs} + {lhs <> rhs}).

  Parameter (ltb: forall (lhs rhs:t), bool).
  Parameter (ltb_trans: forall (x y z:t) (XY: ltb x y = true) (YZ: ltb y z = true), ltb x z = true).
  Parameter (ltb_irrefl: forall x, ltb x x = false).
  Parameter (ltb_eq: forall (lhs rhs:t) (LR: ltb lhs rhs = false) (RL: ltb rhs lhs = false), lhs = rhs).
End S.

Module Make (O:S).
  Definition eq := @eq O.t.
  Program Instance eq_equiv: Equivalence eq.
  Lemma eq_leibniz (x y: O.t): eq x y -> x = y.
  Proof. auto. Qed.

  Definition lt (lhs rhs:O.t): Prop := O.ltb lhs rhs = true.

  Program Instance lt_strorder: StrictOrder lt.
  Next Obligation.
    repeat intro. unfold lt in H.
    rewrite O.ltb_irrefl in H. congruence.
  Qed.
  Next Obligation.
    repeat intro. unfold lt in *.
    apply O.ltb_trans with y; auto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    repeat intro. unfold eq in *. subst. constructor; auto.
  Qed.

  Definition compare (lhs rhs:O.t): comparison :=
    if O.ltb lhs rhs
    then Lt
    else if O.ltb rhs lhs
         then Gt
         else Eq.

  Lemma compare_spec (x y: O.t):
    CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    unfold lt, compare.
    destruct (O.ltb x y) eqn:XY.
    { constructor. auto. }
    destruct (O.ltb y x) eqn:YX.
    { constructor. auto. }
    constructor. apply O.ltb_eq; auto.
  Qed.

  Ltac ltb_tac :=
    match goal with
    | [H: compare ?x1 ?x2 = _ |- _] =>
      generalize (compare_spec x1 x2); rewrite H; clear H;
      intro H; inversion H; subst; clear H
    | [H: lt ?x ?x |- _] =>
      destruct lt_strorder; congruence
    | [H: lt ?x ?y |- _] =>
      rewrite H in *; clear H
    | [H: eq ?x ?y |- _] =>
      rewrite H in *; clear H
    end.
End Make.

Fixpoint compose_comparisons (l: list comparison): bool :=
  match l with
  | nil => false
  | Lt::_ => true
  | Gt::_ => false
  | Eq::l => compose_comparisons l
  end.

Ltac ltb_des :=
  match goal with
  | [H: context[match ?c with | Eq => _ | Lt => _ | Gt => _ end] |- _] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  | [|- context[match ?c with | Eq => _ | Lt => _ | Gt => _ end]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.
