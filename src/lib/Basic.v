Require String.
Require Import RelationClasses.
Require Import List.
Require Import PArith.
Require Import UsualFMapPositive.
Require Import FMapFacts.
Require Import MSetList.

Require Import sflib.
Require Import paco.

Require Import DataStructure.

Set Implicit Arguments.

Module Ident <: OrderedTypeWithLeibniz.
  Include Pos.

  Lemma eq_leibniz (x y: t): eq x y -> x = y.
  Proof. auto. Qed.

  Parameter of_string: String.string -> t.
  Hypothesis of_string_inject:
    forall s1 s2 (H12: s1 <> s2), of_string s1 <> of_string s2.

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

  Lemma eq_dec_eq A i (a1 a2:A):
    (if eq_dec i i then a1 else a2) = a1.
  Proof.
    destruct (eq_dec i i); [|congruence]. auto.
  Qed.

  Lemma eq_dec_neq A i1 i2 (a1 a2:A)
        (NEQ: i1 <> i2):
    (if eq_dec i1 i2 then a1 else a2) = a2.
  Proof.
    destruct (eq_dec i1 i2); [congruence|]. auto.
  Qed.
End Ident.

Module IdentFun := UsualFun (Ident).
Module IdentSet := UsualSet (Ident).
Module IdentMap := UsualPositiveMap.

Notation rtc := (clos_refl_trans_1n _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt1n_refl rt1n_trans t_step.

Program Instance rtc_PreOrder A (R:A -> A -> Prop): PreOrder (rtc R).
Next Obligation.
  ii. revert H0. induction H; auto. i.
  exploit IHclos_refl_trans_1n; eauto. i.
  econs 2; eauto.
Qed.

Lemma rtc_tail A R
      (a1 a3:A)
      (REL: rtc R a1 a3):
  (exists a2, rtc R a1 a2 /\ R a2 a3) \/
  (a1 = a3).
Proof.
  induction REL; auto. des; subst.
  - left. eexists. splits; [|eauto].
    econs; eauto.
  - left. eexists. splits; eauto.
Qed.

Lemma rtc_implies A (R1 R2: A -> A -> Prop)
      (IMPL: R1 <2= R2):
  rtc R1 <2= rtc R2.
Proof.
  i. induction PR; eauto.
  etransitivity; [|eauto]. econs 2; [|econs 1].
  apply IMPL. auto.
Qed.

Lemma fapp A (B:A->Type) (a:A) (P Q:forall (a:A), B a)
      (EQ: P = Q):
  P a = Q a.
Proof. rewrite EQ. auto. Qed.

Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.

Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.
