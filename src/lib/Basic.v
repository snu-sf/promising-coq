Require String.
Require Import List.
Require Import PArith.
Require Import FMapPositive.
Require Import FMapFacts.
Require Import MSetList.

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

Module IdentFun := UsualFun (Ident).
Module IdentSet := UsualSet (Ident).

Module IdentMap.
  Include PositiveMap.
  Module Facts := FMapFacts.Facts (PositiveMap).
  Module Properties := FMapFacts.Properties (PositiveMap).

  Inductive lift_rel2 A B (rel:forall (a:A) (b:B), Prop): forall (a:option A) (b:option B), Prop :=
  | lift_rel2_None:
      lift_rel2 rel None None
  | lift_rel2_Some
      a b (REL: rel a b):
      lift_rel2 rel (Some a) (Some b)
  .

  Definition rel2
             A B (rel: forall (a:A) (b:B), Prop)
             (ma:t A) (mb:t B): Prop :=
    forall i, lift_rel2 rel (find i ma) (find i mb).

  Lemma rel2_elim
        A B C
        (ab: forall (a:A) (b:B), Prop)
        (bc: forall (b:B) (c:C), Prop)
        (ma:t A) (mb:t B) (mc:t C)
        (AB: rel2 ab ma mb)
        (BC: rel2 bc mb mc):
    rel2 (fun a c => exists b, ab a b /\ bc b c) ma mc.
  Proof.
    intro. specialize (AB i). specialize (BC i).
    inv AB; inv BC; try congruence; constructor.
    rewrite <- H2 in H. inv H.
    eexists. split; eauto.
  Qed.

  Lemma rel2_converse
        A B
        (ab: forall (a:A) (b:B), Prop)
        (ma:t A) (mb:t B)
        (AB: rel2 ab ma mb):
    rel2 (fun b a => ab a b) mb ma.
  Proof.
    intro i. specialize (AB i).
    inv AB; constructor; auto.
  Qed.

  Lemma rel2_leaf
        A B
        (ab: forall (a:A) (b:B), Prop)
        (mb:t B)
        (AB: rel2 ab (Leaf _) mb):
    is_empty mb.
  Proof.
    revert AB. induction mb; intros; simpl; auto.
    destruct o.
    { specialize (AB xH). inv AB. }
    rewrite IHmb1, IHmb2; auto.
    - intro i. specialize (AB (xI i)). inv AB.
      rewrite gempty. constructor.
    - intro i. specialize (AB (xO i)). inv AB.
      rewrite gempty. constructor.
  Qed.

  Lemma rel2_intro
        A B C
        (ab: forall (a:A) (b:B), Prop)
        (bc: forall (b:B) (c:C), Prop)
        (ma:t A) (mc:t C)
        (AC: rel2 (fun a c => exists b, ab a b /\ bc b c) ma mc):
    exists mb,
      <<AB: rel2 ab ma mb>> /\
      <<BC: rel2 bc mb mc>>.
  Proof.
    revert mc AC.
    induction ma; destruct mc; intros.
    - exists (Leaf _). split; intro; rewrite ? gempty; constructor.
    - exists (Leaf _). split; intro; rewrite ? gempty.
      1: constructor.
      apply rel2_leaf in AC. apply PositiveMap.is_empty_2 in AC.
      rewrite PositiveMap.Empty_alt in AC. rewrite AC.
      constructor.
    - exists (Leaf _). split; intro; rewrite ? gempty.
      2: constructor.
      apply rel2_converse, rel2_leaf in AC. apply PositiveMap.is_empty_2 in AC.
      rewrite PositiveMap.Empty_alt in AC. rewrite AC.
      constructor.
    - exploit IHma1.
      { intro i. specialize (AC (xO i)).
        inv AC; rewrite <- H; constructor; auto.
      }
      exploit IHma2.
      { intro i. specialize (AC (xI i)).
        inv AC; rewrite <- H; constructor; auto.
      }
      intros [mb2 MB2] [mb1 MB1]. des.
      specialize (AC xH). inv AC.
      + eexists (Node mb1 None mb2).
        simpl in *. subst.
        split; intro; destruct i; simpl;
          try apply AB0; try apply BC0;
          try apply AB; try apply BC;
          constructor.
      + des. eexists (Node mb1 (Some b0) mb2).
        simpl in *. subst.
        split; intro; destruct i; simpl;
          try apply AB0; try apply BC0;
          try apply AB; try apply BC;
          constructor; auto.
  Qed.

  Lemma rel2_implies
        A B
        (ab1 ab2: forall (a:A) (b:B), Prop)
        (IMPLIES: forall a b, ab1 a b -> ab2 a b)
        (ma:t A) (mb:t B)
        (AB: rel2 ab1 ma mb):
    rel2 ab2 ma mb.
  Proof.
    intro i. specialize (AB i).
    inv AB; constructor; auto.
  Qed.

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
