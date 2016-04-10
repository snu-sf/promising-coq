Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import MSetList.
Require Import MSetFacts.

Require Import sflib.

Set Implicit Arguments.


Module UsualOrderedTypeWithLeibniz (S: UsualOrderedType) <: OrderedTypeWithLeibniz.
  Include S.

  Lemma eq_leibniz : forall x y : t, eq x y -> x = y.
  Proof.
    i. unfold eq in *. auto.
  Qed.
End UsualOrderedTypeWithLeibniz.


Module UsualProd (A B:UsualOrderedType) <: UsualOrderedType.
  Definition t := (A.t * B.t)%type.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.

  Inductive lt_ (lhs rhs:t): Prop :=
  | lt_hd
      (HD: A.lt lhs.(fst) rhs.(fst))
  | lt_tl
      (HD: lhs.(fst) = rhs.(fst))
      (TL: B.lt lhs.(snd) rhs.(snd))
  .
  Definition lt := lt_.
  Global Program Instance lt_strorder: StrictOrder lt.
  Next Obligation.
    ii. inv H.
    - eapply A.lt_strorder; eauto.
    - eapply B.lt_strorder; eauto.
  Qed.
  Next Obligation.
    ii. inv H; inv H0.
    - econs 1. etransitivity; eauto.
    - econs 1. rewrite <- HD0. eauto.
    - econs 1. rewrite HD. eauto.
    - econs 2; etransitivity; eauto.
  Qed.
  Global Program Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. subst. auto.
  Qed.
  Definition compare (lhs rhs:t): comparison :=
    match A.compare lhs.(fst) rhs.(fst) with
    | Eq =>
      B.compare lhs.(snd) rhs.(snd)
    | Lt => Lt
    | Gt => Gt
    end.
   Lemma compare_spec :
     forall x y : t,
       CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
   Proof.
     i. destruct x, y. unfold compare. s.
     destruct (A.compare_spec t0 t2);
       try (econs; econs 1; eauto).
     destruct (B.compare_spec t1 t3); subst; econs; auto.
     - econs 2; auto.
     - econs 2; auto.
   Qed.

   Lemma eq_dec: forall x y : t, {x = y} + {x <> y}.
   Proof.
     i. destruct x, y.
     destruct (A.eq_dec t0 t2).
     - destruct (B.eq_dec t1 t3).
       + left. subst. auto.
       + right. contradict n. inv n. auto.
     - right. contradict n. inv n. auto.
   Qed.
End UsualProd.


Module UsualFun (A:UsualDecidableType).
  Polymorphic Definition t (B:Type) := forall (a:A.t), B.

  Section UsualFun.
    Variable (B:Type).

    Definition init (b:B): t B := fun _ => b.

    Definition find (a:A.t) (f:t B): B := f a.

    Definition add (a:A.t) (b:B) (f:t B): t B :=
      fun a' =>
        if A.eq_dec a' a
        then b
        else find a' f.

    Definition init_spec a b:
      find a (init b) = b.
    Proof. auto. Qed.

    Definition add_spec a' a b f:
      find a' (add a b f) =
      if A.eq_dec a' a
      then b
      else find a' f.
    Proof. auto. Qed.

    Lemma add_spec_eq a b f:
      find a (add a b f) = b.
    Proof.
      rewrite add_spec.
      destruct (A.eq_dec a a); auto.
      congruence.
    Qed.

    Lemma add_spec_neq a' a b f (NEQ: a' <> a):
      find a' (add a b f) = find a' f.
    Proof.
      rewrite add_spec.
      destruct (A.eq_dec a' a); auto.
      congruence.
    Qed.

    Lemma extensionality lhs rhs
          (EQ: forall i, find i lhs = find i rhs):
      lhs = rhs.
    Proof. extensionality i. apply EQ. Qed.

    Lemma add_add a1 a2 b1 b2 f
          (DIFF: a1 <> a2):
      add a1 b1 (add a2 b2 f) = add a2 b2 (add a1 b1 f).
    Proof.
      apply extensionality. i.
      rewrite ? add_spec.
      destruct (A.eq_dec i a1), (A.eq_dec i a2); auto.
      congruence.
    Qed.

    Lemma add_init a b:
      add a b (init b) = init b.
    Proof.
      apply extensionality. i.
      rewrite add_spec.
      destruct (A.eq_dec i a); auto.
    Qed.
  End UsualFun.
End UsualFun.


Module UsualSet (S: UsualOrderedType).
  Module S' := UsualOrderedTypeWithLeibniz (S).
  Module Self := MSetList.MakeWithLeibniz (S').
  Module Facts := MSetFacts.Facts (Self).
  Include Self.

  Definition disjoint (lhs rhs:t): Prop :=
    forall s
      (LHS: mem s lhs)
      (RHS: mem s rhs),
      False.

  Lemma ext lhs rhs
        (EXT: forall i, mem i lhs = mem i rhs):
    lhs = rhs.
  Proof.
    apply eq_leibniz. intro i.
    rewrite ? Facts.mem_iff. rewrite EXT.
    constructor; auto.
  Qed.

  Definition remove_if_exists i s :=
    if mem i s
    then Some (remove i s)
    else None.

  Lemma remove_if_exists_spec i s s'
        (REMOVE: remove_if_exists i s = Some s'):
    forall i', mem i' s' = mem i' s && if S.eq_dec i i' then false else true.
  Proof.
    i. unfold remove_if_exists in *.
    destruct (mem i s) eqn:IS; inv REMOVE.
    rewrite Facts.remove_b. destruct (mem i' s); auto.
    unfold Facts.eqb, Self.E.eq_dec. destruct (S.eq_dec i i'); auto.
  Qed.
End UsualSet.
