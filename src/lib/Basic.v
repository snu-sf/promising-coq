Require String.
Require Import RelationClasses.
Require Import List.
Require Import PArith.
Require Import Omega.
Require Import UsualFMapPositive.
Require Import FMapFacts.
Require Import MSetList.

Require Import sflib.
Require Import paco.

Require Import DataStructure.

Set Implicit Arguments.


Ltac refl := reflexivity.
Ltac etrans := etransitivity.
Ltac congr := congruence.

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
  etrans; [|eauto]. econs 2; [|econs 1].
  apply IMPL. auto.
Qed.

Lemma rtc_refl
      A R (a b:A)
      (EQ: a = b):
  rtc R a b.
Proof. subst. econs. Qed.

Lemma rtc_n1
      A R (a b c:A)
      (AB: rtc R a b)
      (BC: R b c):
  rtc R a c.
Proof.
  etrans; eauto. econs 2; eauto.
Qed.

Lemma fapp A (B:A->Type) (a:A) (P Q:forall (a:A), B a)
      (EQ: P = Q):
  P a = Q a.
Proof. rewrite EQ. auto. Qed.

Inductive rtcn A (R: A -> A -> Prop): forall (n:nat) (a1 a2:A), Prop :=
| rtcn_nil
    a:
    rtcn R 0 a a
| rtcn_cons
    a1 a2 a3 n
    (A12: R a1 a2)
    (A23: rtcn R n a2 a3):
    rtcn R (S n) a1 a3
.
Hint Constructors rtcn.

Lemma rtcn_rtc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtc R a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma rtc_rtcn A (R: A -> A -> Prop) a1 a2
      (RTC: rtc R a1 a2):
  exists n, rtcn R n a1 a2.
Proof.
  induction RTC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma rtcn_imply
      A (R1 R2: A -> A -> Prop) n a1 a2
      (LE: R1 <2= R2)
      (RTCN: rtcn R1 n a1 a2):
  rtcn R2 n a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma strong_induction
      (P : nat -> Prop)
      (IH: forall (n:nat) (IH: forall k (LT: k < n), P k), P n):
  forall n : nat, P n.
Proof.
  i. cut (forall m k, k < m -> P k); [by eauto|].
  induction m.
  - i. omega.
  - i. apply lt_le_S in H. inv H; eauto.
Qed.

Definition option_app {A} (a b: option A) : option A :=
  if a then a else b.

Lemma strengthen
      (A B: Prop)
      (H: A /\ (A -> B)):
  A /\ B.
Proof. intuition. Qed.

Lemma option_map_map
      A B C (f: B -> C) (g: A -> B) (a: option A):
  option_map f (option_map g a) = option_map (fun x => f (g x)) a.
Proof.
  destruct a; eauto.
Qed.

Definition is_some {A} (o:option A): bool :=
  match o with
  | Some _ => true
  | None => false
  end.
Coercion is_some: option >-> bool.

Ltac condtac :=
  match goal with
  | [|- context[if ?c then _ else _]] =>
    let COND := fresh "COND" in
    destruct c eqn:COND
  end.
