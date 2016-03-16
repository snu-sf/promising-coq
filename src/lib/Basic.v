Require String.
Require Import List.
Require Import PArith.
Require Import UsualFMapPositive.
Require Import FMapFacts.
Require Import MSetList.
Require Import FunctionalExtensionality.

Require Import sflib.

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
End Ident.

Module IdentSet := UsualSet (Ident).
Module IdentMap := UsualPositiveMap.
Module IdentFun := UsualFun (Ident).
