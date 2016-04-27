Require Import Orders.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import DataStructure.

Module Type IsDense (Import T:EqLtLe).
  Parameter elt: t.

  Parameter decr: t -> t.
  Axiom decr_spec: forall x, lt (decr x) x.

  Parameter incr: t -> t.
  Axiom incr_spec: forall x, lt x (incr x).

  Parameter middle: forall (lhs rhs:t), t.
  Axiom middle_spec:
    forall (lhs rhs:t)
      (LT: lt lhs rhs),
      lt lhs (middle lhs rhs) /\
      lt (middle lhs rhs) rhs.
End IsDense.

Module Type DenseOrderType := UsualOrderedTypeFull <+ IsDense <+ HasCaseJoin.

Module DenseOrder: DenseOrderType.
  Definition t := list bool.
  Definition elt: t := nil.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.

  Inductive lt_: forall (lhs rhs:t), Prop :=
  | lt_false lhs:
      lt_ (false::lhs) []
  | lt_true rhs:
      lt_ [] (true::rhs)
  | lt_false_true lhs rhs:
      lt_ (false::lhs) (true::rhs)
  | lt_cons
      hd lhs rhs
      (LT: lt_ lhs rhs):
      lt_ (hd::lhs) (hd::rhs)
  .
  Definition lt := lt_.
  Global Program Instance lt_strorder: StrictOrder lt.
  Next Obligation.
    intro x. induction x; intro X; inv X.
    apply IHx. auto.
  Qed.
  Next Obligation.
    intros x y z XY. revert z.
    induction XY; i; inv H; econs.
    apply IHXY. auto.
  Qed.
  Global Program Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. subst. auto.
  Qed.
  Fixpoint compare (lhs rhs:t): comparison :=
    match lhs, rhs with
    | [], [] =>
      Eq
    | false::_, true::_
    | [], true::_
    | false::_, [] =>
      Lt
    | true::_, false::_
    | [], false::_
    | true::_, [] =>
      Gt
    | false::ltl, false::rtl
    | true::ltl, true::rtl =>
      compare ltl rtl
    end.
   Lemma compare_spec :
     forall x y : t,
       CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
   Proof.
     induction x; i; destruct y;
       try (destruct a);
       try (destruct b);
       repeat (try econs; s).
     - destruct (IHx y); subst; repeat econs; auto.
     - destruct (IHx y); subst; repeat econs; auto.
   Qed.

   Lemma eq_dec: forall x y : t, {x = y} + {x <> y}.
   Proof.
     induction x; destruct y.
     - left. auto.
     - right. congruence.
     - right. congruence.
     - destruct (IHx y).
       + subst. destruct (Bool.eqb a b) eqn:HD.
         * destruct a, b; auto.
         * right. destruct a, b; inv HD; congruence.
       + right. congruence.
   Qed.

   Definition le := lt \2/ eq.
   Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ x = y.
   Proof. auto. Qed.

  Definition decr (x:t) := x ++ [false].
  Lemma decr_spec: forall x, lt (decr x) x.
    induction x; econs. auto.
  Qed.

  Definition incr (x:t) := x ++ [true].
  Lemma incr_spec: forall x, lt x (incr x).
    induction x; econs. auto.
  Qed.

  Fixpoint middle (lhs rhs:t): t :=
    match lhs, rhs with
    | [], rhs => rhs ++ [false]
    | lhs, [] => lhs ++ [true]
    | false::ltl, true::rtl => []
    | lhd::ltl, rhd::rtl => lhd::(middle ltl rtl)
    end.

  Lemma middle_spec:
    forall (lhs rhs:t)
      (LT: lt lhs rhs),
      lt lhs (middle lhs rhs) /\
      lt (middle lhs rhs) rhs.
  Proof.
    induction lhs; i; inv LT; splits; try econs; s.
    - induction rhs0; econs.
      apply IHrhs0.
    - clear IHlhs. induction lhs; econs.
      apply IHlhs.
    - exploit IHlhs; eauto. i. des.
      destruct a; econs; auto.
    - exploit IHlhs; eauto. i. des.
      destruct a; econs; auto.
  Qed.

  Lemma le_lt_dec (lhs rhs:t): {le lhs rhs} + {lt rhs lhs}.
  Proof.
    generalize (compare_spec lhs rhs).
    destruct (compare lhs rhs).
    - left. inv H. right. ss.
    - left. inv H. apply le_lteq. auto.
    - right. inv H. auto.
  Defined.

  Definition join (lhs rhs:t): t :=
    if le_lt_dec lhs rhs
    then rhs
    else lhs.

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join.
    destruct (le_lt_dec lhs rhs), (le_lt_dec rhs lhs); auto.
    - unfold le in *. des; auto.
      rewrite l0 in l. apply lt_strorder in l. done.
    - rewrite l0 in l. apply lt_strorder in l. done.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join.
    repeat
      (try match goal with
           | [|- context[le_lt_dec ?a ?b]] =>
             destruct (le_lt_dec a b)
           | [H: context[le_lt_dec ?a ?b] |- _] =>
             destruct (le_lt_dec a b)
           | [H1: lt ?a ?b, H2: lt ?b ?a |- _] =>
             rewrite H2 in H1; apply lt_strorder in H1; inv H1
           end; unfold le, eq in *; try subst; des; ss).
    - rewrite l in l2. rewrite l0 in l2.
      apply lt_strorder in l2. inv l2.
    - rewrite l in l2. rewrite l1 in l2.
      apply lt_strorder in l2. inv l2.
  Qed.

  Lemma join_l lhs rhs:
    le lhs (join lhs rhs).
  Proof.
    unfold join. destruct (le_lt_dec lhs rhs); auto.
    apply le_lteq. auto.
  Qed.

  Lemma join_r lhs rhs:
    le rhs (join lhs rhs).
  Proof.
    rewrite join_comm. apply join_l.
  Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    unfold join. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Lemma join_spec_lt lhs rhs o
        (LHS: lt lhs o)
        (RHS: lt rhs o):
    lt (join lhs rhs) o.
  Proof.
    unfold join. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Lemma join_cases lhs rhs:
    join lhs rhs = lhs \/ join lhs rhs = rhs.
  Proof.
    unfold join. destruct (le_lt_dec lhs rhs); auto.
  Qed.
End DenseOrder.

Program Instance DenseOrder_le_PreOrder: PreOrder DenseOrder.le.
Next Obligation.
  ii. apply DenseOrder.le_lteq. right. auto.
Qed.
Next Obligation.
  ii. apply DenseOrder.le_lteq.
  apply DenseOrder.le_lteq in H.
  apply DenseOrder.le_lteq in H0.
  des; subst; auto.
  left. rewrite H. auto.
Qed.
