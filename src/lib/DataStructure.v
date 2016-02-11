Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import MSetList.
Require Import MSetFacts.

Require Import sflib.

Set Implicit Arguments.

Module UsualFun (A:UsualDecidableType).
  Section UsualFun.
    Variable (B:Type).

    Definition t := forall (a:A.t), B.

    Definition init (b:B): t := fun _ => b.

    Definition find (a:A.t) (f:t): B := f a.

    Definition add (a:A.t) (b:B) (f:t): t :=
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

    Lemma add_twice a1 a2 b1 b2 f
          (DIFF: a1 <> a2):
      add a1 b1 (add a2 b2 f) = add a2 b2 (add a1 b1 f).
    Proof.
      extensionality i. unfold add, find.
      destruct (A.eq_dec i a1), (A.eq_dec i a2); auto.
      congruence.
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

  Lemma disjoint_spec lhs rhs
        (DISJ: disjoint lhs rhs):
    lhs = diff (union lhs rhs) rhs.
  Proof.
    apply eq_leibniz. intro i. specialize (DISJ i).
    rewrite ? Facts.mem_iff.
    rewrite Facts.diff_b, Facts.union_b.
    destruct (mem i lhs), (mem i rhs); simpl in *;
      constructor; intro; auto.
  Qed.

  Lemma disjoint_add_spec lhs a rhs
        (DISJ: disjoint_add lhs a rhs):
    lhs = remove a rhs.
  Proof.
    apply eq_leibniz. intro i.
    inversion DISJ. subst. clear DISJ. specialize (DISJ0 i).
    rewrite ? Facts.mem_iff.
    rewrite Facts.singleton_b, Facts.remove_b, Facts.add_b in *.
    rewrite andb_true_iff in *.
    destruct (Facts.eqb a i); simpl in *; intuition.
    rewrite H in DISJ0. auto.
  Qed.
End UsualSet.
