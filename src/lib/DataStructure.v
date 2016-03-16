Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import MSetList.
Require Import MSetFacts.

Require Import sflib.

Set Implicit Arguments.

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


Module UsualSet (S: OrderedTypeWithLeibniz).
  Module Self := MSetList.MakeWithLeibniz (S).
  Module Facts := MSetFacts.Facts (Self).
  Include Self.

  Definition disjoint (lhs rhs:t): Prop :=
    forall s, <<DISJ: ~ (mem s lhs && mem s rhs)>>.

  Inductive disjoint_add lhs a rhs: Prop :=
  | disjoint_add_intro
      (DISJ: disjoint lhs (singleton a))
      (ADD: add a lhs = rhs)
  .

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
