Require Import Orders.
Require Import OrdersFacts.
Require Import RelationClasses.
Require Import PArith.

Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import DataStructure.
Require Import UsualFMapPositive.

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

Module DenseOrder <: DenseOrderType.
  Definition t := positive.
  Definition elt: t := xH.

  Definition eq := @eq t.
  Global Program Instance eq_equiv : Equivalence eq.

  Inductive lt_: forall (lhs rhs:t), Prop :=
  | lt_xO_xH lhs:
      lt_ (xO lhs) xH
  | lt_xH_xI rhs:
      lt_ xH (xI rhs)
  | lt_xO_xI lhs rhs:
      lt_ (xO lhs) (xI rhs)
  | lt_xO
      lhs rhs
      (LT: lt_ lhs rhs):
      lt_ (xO lhs) (xO rhs)
  | lt_xI
      lhs rhs
      (LT: lt_ lhs rhs):
      lt_ (xI lhs) (xI rhs)
  .
  Definition lt := lt_.
  Global Program Instance lt_strorder: StrictOrder lt.
  Next Obligation.
    intro x. induction x; intro X; inv X; eauto.
  Qed.
  Next Obligation.
    intros x y z XY. revert z.
    induction XY; i; inv H; econs.
    - apply IHXY. auto.
    - apply IHXY. auto.
  Qed.
  Global Program Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. subst. auto.
  Qed.
  Fixpoint compare (lhs rhs:t): comparison :=
    match lhs, rhs with
    | xH, xH =>
      Eq
    | xO _, xI _
    | xH, xI _
    | xO _, xH =>
      Lt
    | xI _, xO _
    | xH, xO _
    | xI _, xH =>
      Gt
    | xO ltl, xO rtl
    | xI ltl, xI rtl =>
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
     apply Pos.eq_dec.
   Defined.
   Global Opaque eq_dec.

   Definition le := lt \2/ eq.
   Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ x = y.
   Proof. auto. Qed.
   Global Opaque le.

   Fixpoint decr (x:t) :=
     match x with
     | xH => xO xH
     | xO x => xO (decr x)
     | xI x => xI (decr x)
     end.

  Lemma decr_spec: forall x, lt (decr x) x.
    induction x; ss; econs; eauto.
  Qed.

   Fixpoint incr (x:t) :=
     match x with
     | xH => xI xH
     | xO x => xO (incr x)
     | xI x => xI (incr x)
     end.

  Lemma incr_spec: forall x, lt x (incr x).
    induction x; ss; econs; eauto.
  Qed.

  Fixpoint middle (lhs rhs:t): t :=
    match lhs, rhs with
    | xH, rhs => decr rhs
    | lhs, xH => incr lhs
    | xO ltl, xO rtl => xO (middle ltl rtl)
    | xO ltl, xI rtl => xO (incr ltl)
    | xI ltl, xO rtl => xI (middle ltl rtl)
    | xI ltl, xI rtl => xI (middle ltl rtl)
    end.

  Lemma middle_spec:
    forall (lhs rhs:t)
      (LT: lt lhs rhs),
      lt lhs (middle lhs rhs) /\
      lt (middle lhs rhs) rhs.
  Proof.
    induction lhs; s; i; inv LT; splits; econs;
      (try by apply IHlhs; auto);
      (try by apply incr_spec; auto);
      (try by apply decr_spec; auto).
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
    - apply le_lteq in l. apply le_lteq in l0.
      des; auto. rewrite l in l0. apply lt_strorder in l0. done.
    - rewrite l in l0. apply lt_strorder in l0. done.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join.
    repeat
      (try match goal with
           | [H: le _ _ |- _] =>
             apply le_lteq in H
           | [|- context[le_lt_dec ?a ?b]] =>
             destruct (le_lt_dec a b)
           | [H: context[le_lt_dec ?a ?b] |- _] =>
             destruct (le_lt_dec a b)
           | [H1: lt ?a ?b, H2: lt ?b ?a |- _] =>
             rewrite H2 in H1; apply lt_strorder in H1; inv H1
           end; unfold eq in *; try subst; des; ss).
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

  Lemma join_cases lhs rhs:
    join lhs rhs = lhs \/ join lhs rhs = rhs.
  Proof.
    unfold join. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Definition meet (lhs rhs:t): t :=
    if le_lt_dec lhs rhs
    then lhs
    else rhs.

  Lemma meet_comm lhs rhs: meet lhs rhs = meet rhs lhs.
  Proof.
    unfold meet.
    destruct (le_lt_dec lhs rhs), (le_lt_dec rhs lhs); auto.
    - apply le_lteq in l. apply le_lteq in l0.
      des; auto. rewrite l in l0. apply lt_strorder in l0. done.
    - rewrite l in l0. apply lt_strorder in l0. done.
  Qed.

  Lemma meet_assoc a b c: meet (meet a b) c = meet a (meet b c).
  Proof.
    unfold meet.
    repeat
      (try match goal with
           | [H: le _ _ |- _] =>
             apply le_lteq in H
           | [|- context[le_lt_dec ?a ?b]] =>
             destruct (le_lt_dec a b)
           | [H: context[le_lt_dec ?a ?b] |- _] =>
             destruct (le_lt_dec a b)
           | [H1: lt ?a ?b, H2: lt ?b ?a |- _] =>
             rewrite H2 in H1; apply lt_strorder in H1; inv H1
           end; unfold eq in *; try subst; des; ss).
    - rewrite l2 in l. rewrite l1 in l.
      apply lt_strorder in l. inv l.
    - rewrite l2 in l. rewrite l0 in l.
      apply lt_strorder in l. inv l.
  Qed.

  Lemma meet_l lhs rhs:
    le (meet lhs rhs) lhs.
  Proof.
    unfold meet. destruct (le_lt_dec lhs rhs); auto.
    - apply le_lteq. auto.
    - apply le_lteq. auto.
  Qed.

  Lemma meet_r lhs rhs:
    le (meet lhs rhs) rhs.
  Proof.
    rewrite meet_comm. apply meet_l.
  Qed.

  Lemma meet_spec lhs rhs o
        (LHS: le o lhs)
        (RHS: le o rhs):
    le o (meet lhs rhs).
  Proof.
    unfold meet. destruct (le_lt_dec lhs rhs); auto.
  Qed.

  Lemma meet_cases lhs rhs:
    meet lhs rhs = lhs \/ meet lhs rhs = rhs.
  Proof.
    unfold meet. destruct (le_lt_dec lhs rhs); auto.
  Qed.

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

  Lemma le_xI
        lhs rhs
        (LE: le lhs rhs):
    le (xI lhs) (xI rhs).
  Proof.
    inv LE.
    - left. econs. auto.
    - inv H. right. refl.
  Qed.

  Lemma le_xO
        lhs rhs
        (LE: le lhs rhs):
    le (xO lhs) (xO rhs).
  Proof.
    inv LE.
    - left. econs. auto.
    - inv H. right. refl.
  Qed.
End DenseOrder.

Global Program Instance DenseOrder_le_PreOrder: PreOrder DenseOrder.le.
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

Module DOSet := UsualSet DenseOrder.

Module DOMap.
  Include UsualPositiveMap.

  Fixpoint raw_max_key A (m:Raw.t A): option DenseOrder.t :=
    match m with
    | Raw.Leaf _ => None
    | Raw.Node l o r =>
      match raw_max_key _ r, o, raw_max_key _ l with
      | Some k, _, _ => Some (xI k)
      | None, Some _, _ => Some xH
      | None, None, Some k => Some (xO k)
      | None, None, None => None
      end
    end.

  Lemma raw_max_key_spec1 A (m:Raw.t A)
        (KEY: raw_max_key _ m = None):
    forall k', Raw.find k' m = None.
  Proof.
    revert KEY. induction m; s; i.
    { apply Raw.gleaf. }
    destruct (raw_max_key A m2) eqn:K2; [congr|].
    destruct o eqn:O; [congr|].
    destruct (raw_max_key A m1) eqn:K1; [congr|].
    destruct k'; eauto.
  Qed.

  Lemma raw_max_key_spec2 A (m:Raw.t A) k
        (KEY: raw_max_key _ m = Some k):
    <<FIND: Raw.find k m <> None>> /\
    <<MAX: forall k' (FIND': Raw.find k' m <> None), DenseOrder.le k' k>>.
  Proof.
    revert k KEY. induction m; s; [congr|].
    destruct (raw_max_key A m2) eqn:K2.
    { i. inv KEY. s. exploit IHm2; eauto. i. des.
      splits; eauto. i. destruct k'; ss.
      - apply DenseOrder.le_xI. auto.
      - left. econs.
      - left. econs.
    }
    destruct o.
    { i. inv KEY. s. splits; [congr|].
      i. destruct k'; ss.
      - erewrite raw_max_key_spec1 in FIND'; eauto. congr.
      - left. econs.
      - refl.
    }
    destruct (raw_max_key A m1) eqn:K1.
    { i. inv KEY. s. exploit IHm1; eauto. i. des.
      splits; eauto. i. destruct k'; ss.
      - erewrite raw_max_key_spec1 in FIND'; eauto. congr.
      - apply DenseOrder.le_xO. auto.
      - congr.
    }
    i. congr.
  Qed.

  Definition max_key A (m:t A): DenseOrder.t :=
    match raw_max_key A (proj1_sig m)  with
    | Some k => k
    | None => DenseOrder.elt
    end.

  Lemma max_key_spec A (m:t A):
    <<FIND: find DenseOrder.elt m <> None -> find (max_key _ m) m <> None>> /\
    <<MAX: forall k' (FIND': find k' m <> None), DenseOrder.le k' (max_key _ m)>>.
  Proof.
    unfold max_key. destruct (raw_max_key A (proj1_sig m)) eqn:X.
    - exploit raw_max_key_spec2; eauto. i. des. splits; i.
      + unfold find. auto.
      + apply MAX. auto.
    - splits; i.
      + unfold find in H. erewrite raw_max_key_spec1 in H; eauto.
      + unfold find in FIND'. erewrite raw_max_key_spec1 in FIND'; eauto. congr.
  Qed.
End DOMap.

Module DenseOrderFacts.
  Include (OrderedTypeFacts DenseOrder).
  Include (OrderedTypeTest DenseOrder).

  Lemma lt_le_lt a b c
        (AB: DenseOrder.lt a b)
        (BC: DenseOrder.le b c):
    DenseOrder.lt a c.
  Proof.
    apply DenseOrder.le_lteq in BC. des; subst; auto.
    etrans; eauto.
  Qed.

  Lemma le_lt_lt a b c
        (AB: DenseOrder.le a b)
        (BC: DenseOrder.lt b c):
    DenseOrder.lt a c.
  Proof.
    apply DenseOrder.le_lteq in AB. des; subst; auto.
    etrans; eauto.
  Qed.

  Lemma antisym a b
        (AB: DenseOrder.le a b)
        (BA: DenseOrder.le b a):
    a = b.
  Proof.
    apply le_antisym; ii.
    - eapply DenseOrder.lt_strorder. eapply lt_le_lt; eauto.
    - eapply DenseOrder.lt_strorder. eapply lt_le_lt; eauto.
  Qed.

  Lemma le_lt_dec (lhs rhs:DenseOrder.t): {DenseOrder.le lhs rhs} + {DenseOrder.lt rhs lhs}.
  Proof.
    generalize (DenseOrder.compare_spec lhs rhs).
    destruct (DenseOrder.compare lhs rhs).
    - left. inv H. refl.
    - left. inv H. apply DenseOrder.le_lteq. auto.
    - right. inv H. auto.
  Defined.

  Lemma join_spec_lt lhs rhs o
        (LHS: DenseOrder.lt lhs o)
        (RHS: DenseOrder.lt rhs o):
    DenseOrder.lt (DenseOrder.join lhs rhs) o.
  Proof.
    exploit DenseOrder.join_spec.
    - apply DenseOrder.le_lteq. left. apply LHS.
    - apply DenseOrder.le_lteq. left. apply RHS.
    - i. apply DenseOrder.le_lteq in x0. des; auto. subst.
      generalize (DenseOrder.join_cases lhs rhs). i. des.
      + rewrite H at 1. auto.
      + rewrite H at 1. auto.
  Qed.
End DenseOrderFacts.
