Require String.
Require Import List.
Require Import PArith.
Require Import FMapPositive.
Require Import FMapFacts.
Require Import MSetList.

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

Module IdentFun := UsualFun (Ident).
Module IdentSet := UsualSet (Ident).

Module IdentMap.
  Include PositiveMap.
  Module Facts := FMapFacts.Facts (PositiveMap).
  Module Properties := FMapFacts.Properties (PositiveMap).

  Definition get_max V (pred: V -> nat) (m:t V): nat :=
    fold
      (fun _ v res => max (pred v) res)
      m
      0.

  Lemma get_max_spec V (pred: V -> nat) m:
    forall i v (FIND: find i m = Some v), pred v <= get_max pred m.
  Proof.
    unfold find, get_max.
    rewrite fold_1, <- fold_left_rev_right.
    intros.
    apply elements_correct in FIND.
    apply in_rev in FIND.
    revert FIND. generalize (rev (elements m)).
    induction l; intros; inversion FIND; subst; simpl.
    - apply Max.le_max_l.
    - rewrite <- Max.le_max_r. apply IHl. auto.
  Qed.
End IdentMap.


Definition option_eq_dec
           A (eq_dec: forall (l r:A), {l = r} + {l <> r})
           (l r: option A): {l = r} + {l <> r}.
Proof.
  refine
    (match l, r with
     | Some l, Some r => _
     | None, None => _
     | _, _ => _
     end);
    try (left; auto; fail);
    try (right; congruence; fail).
  destruct (eq_dec l r).
  - subst. left. auto.
  - right. contradict n. inversion n. auto.
Defined.

Notation rtc := (clos_refl_trans _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt_step rt_refl t_step.


Inductive lift_rel2 A B (rel:forall (a:A) (b:B), Prop): forall (a:option A) (b:option B), Prop :=
| lift_rel2_None:
    lift_rel2 rel None None
| lift_rel2_Some
    a b (REL: rel a b):
    lift_rel2 rel (Some a) (Some b)
.
