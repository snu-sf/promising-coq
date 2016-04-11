Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.

Set Implicit Arguments.


Module Times.
  Definition t := LocFun.t Time.t.
  Definition init: t := LocFun.init Time.elt.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (LocFun.find loc lhs) (LocFun.find loc rhs).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. reflexivity. Qed.
  Next Obligation. ii. etransitivity; eauto. Qed.

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Times.

Module Snapshot.
  Structure t := mk {
    reads: Times.t;
    writes: Times.t;
  }.

  Definition init: t := mk Times.init Times.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (READS: Times.le lhs.(reads) rhs.(reads))
      (WRITES: Times.le lhs.(writes) rhs.(writes))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etransitivity; eauto.
  Qed.

  Inductive readable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | readable_intro
      (* (CoRR: Time.le (Times.get loc history.(Snapshot.reads)) ts) *)
      (CoWR: Time.le (Times.get loc history.(Snapshot.writes)) ts)
  .

  Inductive writable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | writable_intro
      (CoRW: Time.lt (Times.get loc history.(Snapshot.reads)) ts)
      (CoWW: Time.lt (Times.get loc history.(Snapshot.writes)) ts)
  .
End Snapshot.

Module Message.
  Structure t := mk {
    val: Const.t;
    released: Snapshot.t;
  }.
  Definition elt: t := mk 0 Snapshot.init.
End Message.

Module Cell.
  Structure t := mk {
    messages: Time.t -> (option (Time.t * Message.t));

    VOLUME:
      forall to from msg
        (MESSAGE: messages to = Some (from, msg)),
        Time.lt from to;
    DISJOINT:
      forall to1 to2 from1 from2 msg1 msg2
        (TO: to1 <> to2)
        (MESSAGE1: messages to1 = Some (from1, msg1))
        (MESSAGE2: messages to2 = Some (from2, msg2)),
        Interval.disjoint (from1, to1) (from2, to2);
    DOMAIN:
      exists tos,
      forall to from msg (MSG: messages to = Some (from, msg)),
        List.In to tos;
  }.

  Lemma eq_iff cell1 cell2
        (MSG: forall to, messages cell1 to = messages cell2 to):
    cell1 = cell2.
  Proof.
    destruct cell1, cell2. ss.
    assert (messages0 = messages1); subst.
    { apply TimeFun.extensionality. apply MSG. }
    assert (VOLUME0 = VOLUME1) by apply proof_irrelevance; subst.
    assert (DISJOINT0 = DISJOINT1) by apply proof_irrelevance; subst.
    assert (DOMAIN0 = DOMAIN1) by apply proof_irrelevance; subst.
    auto.
  Qed.

  Definition get (to:Time.t) (cell:t): option Message.t :=
    option_map snd (cell.(messages) to).

  Lemma extensionality lhs rhs
        (MESSAGES: forall x, lhs.(messages) x = rhs.(messages) x):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    cut (messages0 = messages1).
    { i. subst. f_equal; apply proof_irrelevance. }
    extensionality to. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg (MSG: lhs.(messages) to = Some (from, msg)),
      rhs.(messages) to = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. apply H0. apply H. auto. Qed.

  Inductive own (cell:t) (ts:Time.t): Prop :=
  | own_intro
      to from msg
      (MESSAGE: cell.(messages) to = Some (from, msg))
      (INTERVAL: Interval.mem (from, to) ts)
  .

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall ts (LHS: own lhs ts) (RHS: own rhs ts), False)
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. eapply DISJOINT0; eauto.
  Qed.

  Lemma disjoint_messages
        to lhs rhs lx rx
        (DISJ: disjoint lhs rhs)
        (LHS: lhs.(messages) to = Some lx)
        (RHS: rhs.(messages) to = Some rx):
    False.
  Proof.
    destruct lx, rx.
    eapply DISJ; econs; eauto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
  Qed.

  Program Definition init: t :=
    mk
      (TimeFun.add Time.elt (Some (Time.decr Time.elt, Message.mk 0 Snapshot.init)) (TimeFun.init None))
      _ _ _.
  Next Obligation.
    unfold TimeFun.add in *.
    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end;
      inv MESSAGE.
    apply Time.decr_spec.
  Qed.
  Next Obligation.
    unfold TimeFun.add in *.
    repeat match goal with
           | [H: context[if ?c then _ else _] |- _] => destruct c
           end;
      subst; inv MESSAGE1; inv MESSAGE2.
    congruence.
  Qed.
  Next Obligation.
    exists [Time.elt]. i.
    unfold TimeFun.add in *.
    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end;
      subst; inv MSG.
    econs. auto.
  Qed.

  Inductive add_new (from to:Time.t) (msg:Message.t) (cell1 cell2:t): Prop :=
  | add_new_intro
      (MESSAGES1: cell1.(messages) to = None)
      (MESSAGES2: cell2.(messages) = TimeFun.add to (Some (from, msg)) cell1.(messages))
  .

  Inductive add_split (from to to':Time.t) (msg msg':Message.t) (cell1 cell2:t): Prop :=
  | add_split_intro
      (MESSAGES1: cell1.(messages) to' = Some (from, msg'))
      (MESSAGES2: cell2.(messages) =
                  TimeFun.add to' (Some (to, msg'))
                              (TimeFun.add to (Some (from, msg)) cell1.(messages)))
  .

  Lemma add_new_iff from to msg cell1:
    (exists cell2, add_new from to msg cell1 cell2) <->
    <<TO: Time.lt from to>> /\
    <<OWN: forall x, Interval.mem (from, to) x -> ~ own cell1 x>>.
  Proof.
    econs; i.
    - des. inv H. splits.
      + eapply VOLUME. rewrite MESSAGES2.
        unfold TimeFun.add.
        destruct (Time.eq_dec to to); [|congruence].
        eauto.
      + ii. inv H. inv H0. inv INTERVAL. ss.
        assert (to <> to0).
        { ii. subst. congruence. }
        eapply (DISJOINT cell2); eauto.
        * rewrite MESSAGES2. unfold TimeFun.add.
          destruct (Time.eq_dec to to); [|congruence].
          eauto.
        * rewrite MESSAGES2. unfold TimeFun.add.
          destruct (Time.eq_dec to0 to); [congruence|].
          eauto.
        * econs; eauto.
        * econs; eauto.
    - des. eexists. econs.
      { destruct (messages cell1 to) as [[]|] eqn:CELL1; [|done].
        exfalso. eapply OWN.
        * apply Interval.mem_ub. auto.
        * econs; eauto. apply Interval.mem_ub. eapply VOLUME; eauto.
      }
      instantiate (1 := mk _ _ _ _). s. eauto.
  Unshelve.
      + i. unfold TimeFun.add in *.
        destruct (Time.eq_dec to0 to).
        { inv MESSAGE. auto. }
        eapply VOLUME; eauto.
      + i. unfold TimeFun.add in *.
        destruct (Time.eq_dec to1 to), (Time.eq_dec to2 to);
          repeat
            (try match goal with
                 | [H: Some _ = Some _ |- _] => inv H
                 end;
             ss; subst).
        * congruence.
        * ii. eapply OWN; eauto. econs; eauto.
        * ii. eapply OWN; eauto. econs; eauto.
        * eapply DISJOINT; eauto.
      + generalize (DOMAIN cell1). i. des.
        exists (to::tos). i.
        unfold TimeFun.add in *. destruct (Time.eq_dec to0 to).
        { inv MSG. left. auto. }
        { right. eapply H. eauto. }
  Qed.

  Lemma add_split_iff from to to' msg msg' cell1:
    (exists cell2, add_split from to to' msg msg' cell1 cell2) <->
    (<<TO: Time.lt from to>> /\
     <<TO': Time.lt to to'>> /\
     <<MSG: cell1.(messages) to' = Some (from, msg')>>).
  Proof.
    econs; i.
    - des. inv H. splits; auto.
      + exploit (VOLUME cell1); eauto. i.
        destruct (Time.eq_dec to to'); [by subst|].
        eapply (VOLUME cell2); eauto.
        rewrite MESSAGES2. unfold TimeFun.add, TimeFun.find.
        destruct (Time.eq_dec to to'); [congruence|].
        destruct (Time.eq_dec to to); [|congruence].
        eauto.
      + eapply (VOLUME cell2); eauto.
        rewrite MESSAGES2. unfold TimeFun.add.
        destruct (Time.eq_dec to' to'); [|congruence].
        eauto.
    - des. eexists. econs; eauto.
      instantiate (1 := mk _ _ _ _). s. eauto.
  Unshelve.
      + i. unfold TimeFun.add in *.
        destruct (Time.eq_dec to0 to').
        { inv MESSAGE. auto. }
        unfold TimeFun.find in *.
        destruct (Time.eq_dec to0 to).
        { inv MESSAGE. auto. }
        eapply VOLUME; eauto.
      + i. unfold TimeFun.add, TimeFun.find in *.
        ii. inversion LHS. inversion RHS. ss.
        destruct (Time.eq_dec to1 to'), (Time.eq_dec to2 to'),
                 (Time.eq_dec to1 to), (Time.eq_dec to2 to);
          repeat
            (try match goal with
                 | [H: Some _ = Some _ |- _] => inv H
                 | [H: Time.lt ?x ?x |- _] =>
                   apply Time.lt_strorder in H; inv H
                 | [H1: Time.lt ?a ?b, H2: Time.le ?b ?a |- _] =>
                   generalize (Time.lt_le_lt H1 H2); i
                 end;
             ss; subst;
             try congruence).
        * eapply DISJOINT; [|apply MESSAGE2|apply MSG| |]; eauto.
          econs; auto. s. rewrite TO. auto.
        * eapply DISJOINT; [|apply MESSAGE1|apply MSG| |]; eauto.
          econs; auto. s. rewrite TO. auto.
        * eapply DISJOINT; [|apply MESSAGE2|apply MSG| |]; eauto.
          econs; auto. s. rewrite TO1. apply Time.le_lteq. auto.
        * eapply DISJOINT; [|apply MESSAGE1|apply MSG| |]; eauto.
          econs; auto. s. rewrite TO2. apply Time.le_lteq. auto.
        * eapply DISJOINT; [|apply MESSAGE1|apply MESSAGE2| |]; eauto.
      + generalize (DOMAIN cell1). i. des.
        exists (to::tos). i.
        unfold TimeFun.add, TimeFun.find in *.
        destruct (Time.eq_dec to0 to).
        { inv MSG. left. auto. }
        destruct (Time.eq_dec to0 to').
        { inv MSG0. right. eapply H. eauto. }
        { right. eapply H. eauto. }
  Qed.

  Lemma add_new_messages from to msg cell1 cell2
        (DECLARE: add_new from to msg cell1 cell2):
    forall f t m,
      cell2.(messages) t = Some (f, m) <->
      cell1.(messages) t = Some (f, m) \/
      (f = from /\ t = to /\ m = msg).
  Proof.
    destruct (@add_new_iff from to msg cell1) as [DECL _].
    exploit DECL; eauto. i. des.
    inv DECLARE. rewrite MESSAGES2. unfold TimeFun.add, TimeFun.find.
    destruct (Time.eq_dec t0 to).
    - subst. econs; i.
      + inv H. right. auto.
      + des; [congruence|]. des. subst. auto.
    - econs; auto. i. des; auto.
      congruence.
  Qed.

  Lemma add_split_messages from to to' msg msg' cell1 cell2
        (DECLARE: add_split from to to' msg msg' cell1 cell2):
    forall f t m,
      cell2.(messages) t = Some (f, m) <->
      (t <> to' /\ t <> to /\ cell1.(messages) t = Some (f, m)) \/
      (f = to /\ t = to' /\ m = msg') \/
      (f = from /\ t = to /\ m = msg).
  Proof.
    destruct (@add_split_iff from to to' msg msg' cell1) as [DECL _].
    exploit DECL; eauto. i. des.
    inv DECLARE. rewrite MESSAGES2. unfold TimeFun.add, TimeFun.find.
    rewrite MSG in MESSAGES1. inv MESSAGES1.
    destruct (Time.eq_dec t0 to'); subst.
    - econs; i.
      + inv H. auto.
      + des; subst; [congruence| |]; auto.
        apply Time.lt_strorder in TO'. inv TO'.
    - destruct (Time.eq_dec t0 to); subst.
      + econs; i.
        * inv H. right. right. auto.
        * des; congruence.
      + econs; i.
        * left. auto.
        * des; congruence.
  Qed.

  Lemma add_new_unique from to msg cell1 cell2 cell2'
        (CELL2: add_new from to msg cell1 cell2)
        (CELL2': add_new from to msg cell1 cell2'):
    cell2 = cell2'.
  Proof.
    apply eq_iff. i.
    inv CELL2. inv CELL2'.
    rewrite MESSAGES2, MESSAGES3. auto.
  Qed.

  Lemma add_split_unique from1 from2 to to1' to2' msg msg1' msg2' cell1 cell2 cell2'
        (CELL2: add_split from1 to to1' msg msg1' cell1 cell2)
        (CELL2': add_split from2 to to2' msg msg2' cell1 cell2'):
    from1 = from2 /\
    to1' = to2' /\
    msg1' = msg2' /\
    cell2 = cell2'.
  Proof.
    destruct (@add_split_iff from1 to to1' msg msg1' cell1) as [DECL _].
    exploit DECL; eauto. clear DECL. i. des.
    destruct (@add_split_iff from2 to to2' msg msg2' cell1) as [DECL _].
    exploit DECL; eauto. clear DECL. i. des.
    destruct (Time.eq_dec to1' to2').
    - subst. rewrite MSG in MSG0. inv MSG0. splits; auto.
      apply eq_iff. i. inv CELL2. inv CELL2'.
      rewrite MESSAGES2, MESSAGES3. auto.
    - exfalso. eapply DISJOINT; eauto.
      + econs; eauto. s. apply Time.le_lteq. auto.
      + econs; eauto. s. apply Time.le_lteq. auto.
  Qed.

  Inductive future (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGES:
         forall to from_lhs msg
           (LHS: lhs.(messages) to = Some (from_lhs, msg)),
         exists from_rhs,
           rhs.(messages) to = Some (from_rhs, msg))
      (OWNERSHIP: own lhs <1= own rhs)
  .

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation.
    ii. econs; i; eauto.
  Qed.
  Next Obligation.
    ii. inv H; inv H0. econs; i.
    - exploit MESSAGES; eauto. i. des.
      eapply MESSAGES0; eauto.
    - exploit OWNERSHIP; eauto.
  Qed.

  Lemma add_new_future
        from to msg cell1 cell2
        (DECLARE: add_new from to msg cell1 cell2):
    future cell1 cell2.
  Proof.
    destruct (@add_new_iff from to msg cell1) as [DECL _].
    exploit DECL; eauto. i. des.
    generalize DECLARE. intro D. inv D. econs; i.
    - edestruct (@add_new_messages from to msg cell1) as [_ SPEC]; eauto.
    - inv PR.
      edestruct (@add_new_messages from to msg cell1) as [_ SPEC]; [eauto|].
      econs; [|eauto]. eauto.
  Qed.

  Lemma add_split_future
        from to to' msg msg' cell1 cell2
        (DECLARE: add_split from to to' msg msg' cell1 cell2):
    future cell1 cell2.
  Proof.
    destruct (@add_split_iff from to to' msg msg' cell1) as [DECL _].
    exploit DECL; eauto. i. des.
    generalize DECLARE. intro D. inv D.
    rewrite MSG in MESSAGES1. inv MESSAGES1.
    econs; i.
    - destruct (Time.eq_dec to0 to'); subst.
      { rewrite MSG in LHS. inv LHS.
        edestruct (@add_split_messages from_lhs to to' msg msg0 cell1) as [_ SPEC]; eauto.
        eexists. apply SPEC. right. left. eauto.
      }
      destruct (Time.eq_dec to0 to); subst.
      + exfalso. eapply DISJOINT; eauto.
        * apply Interval.mem_ub. eapply VOLUME; eauto.
        * econs; eauto. s. apply Time.le_lteq.
          destruct (Time.compare_spec to to'); intuition.
      + edestruct (@add_split_messages from to to' msg msg' cell1) as [_ SPEC]; eauto.
        eexists. apply SPEC. left. splits; eauto.
    - inv PR.
      destruct (Time.eq_dec to0 to'); subst.
      { rewrite MSG in MESSAGE. inv MESSAGE. inv INTERVAL. ss.
        destruct (TimeSet.Raw.MX.lt_dec to x0).
        - econs.
          + instantiate (3 := to'). rewrite MESSAGES2. unfold TimeFun.add.
            destruct (Time.eq_dec to' to'); [|congruence]. eauto.
          + econs; eauto.
        - econs.
          + instantiate (3 := to). rewrite MESSAGES2. unfold TimeFun.add, TimeFun.find.
            destruct (Time.eq_dec to to').
            { subst. apply Time.lt_strorder in TO'. inv TO'. }
            destruct (Time.eq_dec to to); [|congruence]. eauto.
          + econs; eauto. s. apply Time.le_lteq.
            destruct (Time.compare_spec x0 to); auto. congruence.
      }
      destruct (Time.eq_dec to0 to); subst.
      + exfalso. eapply DISJOINT; [eauto|eauto|eauto| |].
        * apply Interval.mem_ub. eapply VOLUME; eauto.
        * econs; eauto. s. apply Time.le_lteq.
          destruct (Time.compare_spec to to'); intuition.
      + edestruct (@add_split_messages from to to' msg msg' cell1) as [_ SPEC]; eauto.
        econs; eauto.
  Qed.

  Lemma messages_from
        cell to1 to2 from msg1 msg2
        (TO1: messages cell to1 = Some (from, msg1))
        (TO2: messages cell to2 = Some (from, msg2)):
    to1 = to2 /\ msg1 = msg2.
  Proof.
    destruct (Time.eq_dec to1 to2).
    - subst. splits; congruence.
    - exfalso.
      destruct (Time.compare_spec to1 to2); [congruence| |].
      + eapply DISJOINT; eauto.
        * apply Interval.mem_ub.
          eapply VOLUME. eauto.
        * econs; s.
          { eapply VOLUME. eauto. }
          { apply Time.le_lteq. auto. }
      + eapply DISJOINT; eauto.
        * econs; s.
          { eapply VOLUME. eauto. }
          { apply Time.le_lteq. auto. }
        * apply Interval.mem_ub.
          eapply VOLUME. eauto.
  Qed.

  Lemma add_new_le
        from to msg cell1 cell2 cell1' cell2'
        (LE: le cell1 cell2)
        (DECLARE1: add_new from to msg cell1 cell1')
        (DECLARE2: add_new from to msg cell2 cell2'):
    le cell1' cell2'.
  Proof.
    ii.
    eapply add_new_messages in MSG; eauto.
    eapply add_new_messages; eauto.
    des; auto.
  Qed.

  Lemma add_split_le
        from to to' msg msg' cell1 cell2 cell1'
        (LE: le cell1 cell2)
        (DECLARE1: add_split from to to' msg msg' cell1 cell1'):
    exists cell2',
      <<LE: le cell1' cell2'>> /\
      <<DECLARE2: add_split from to to' msg msg' cell2 cell2'>>.
  Proof.
    destruct (@add_split_iff from to to' msg msg' cell1) as [DECL _].
    exploit DECL; eauto. clear DECL. i. des.
    exploit LE; eauto. i.
    destruct (@add_split_iff from to to' msg msg' cell2) as [_ DECL].
    exploit DECL; eauto. i. des.
    eexists. splits; eauto.
    ii.
    eapply add_split_messages in MSG0; eauto.
    eapply add_split_messages; eauto.
    des; auto.
  Qed.

  Program Definition remove (to:Time.t) (cell:t): t :=
    mk (TimeFun.add to None cell.(messages)) _ _ _.
  Next Obligation.
    unfold TimeFun.add in *.    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end; inv MESSAGE.
    eapply VOLUME; eauto.
  Qed.
  Next Obligation.
    unfold TimeFun.add in *.    repeat match goal with
           | [H: context[if ?c then _ else _] |- _] => destruct c
           end;
      inv MESSAGE1; inv MESSAGE2.
    eapply DISJOINT; eauto.
  Qed.
  Next Obligation.
    generalize (DOMAIN cell). i. des.
    exists tos. i.
    unfold TimeFun.add in *.    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end; inv MSG.
    eapply H; eauto.
  Qed.

  Lemma remove_disjoint
        ts cell1 cell2
        (DISJOINT: disjoint cell1 cell2):
    disjoint (remove ts cell1) cell2.
  Proof.
    econs. i.
    inv DISJOINT. specialize (DISJOINT0 ts0).
    apply DISJOINT0; auto.
    inv LHS. econs; eauto.
    unfold remove in *. ss.
    unfold TimeFun.add in *.
    destruct (TimeSet.Facts.eq_dec to ts); inv MESSAGE. eauto.
  Qed.

  Lemma remove_le
        ts cell mem
        (LE: le cell mem):
    le (remove ts cell) mem.
  Proof.
    ii. unfold remove in *. ss.
    unfold TimeFun.add, TimeFun.find in *.
    destruct (TimeSet.Facts.eq_dec to ts); inv MSG.
    exploit LE; eauto. i. rewrite x. auto.
  Qed.
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (to:Time.t) (mem:t): option Message.t :=
    Cell.get to (mem loc).

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (LE: forall loc, Cell.le (lhs loc) (rhs loc))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. econs. intro loc. reflexivity. Qed.
  Next Obligation. econs. inv H. inv H0. intro loc. etransitivity; eauto. Qed.

  Definition own (mem:t) (loc:Loc.t) (to:Time.t): Prop :=
    Cell.own (mem loc) to.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc, Cell.disjoint (lhs loc) (rhs loc))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. symmetry. apply DISJOINT.
  Qed.

  Definition init: t := LocFun.init Cell.init.

  Inductive add_new (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem1:t): forall (mem2:t), Prop :=
  | add_new_intro
      cell2
      (ALLOC: Cell.add_new from to msg (mem1 loc) cell2):
      add_new loc from to msg mem1 (LocFun.add loc cell2 mem1)
  .

  Inductive add_split (loc:Loc.t) (from to to':Time.t) (msg msg':Message.t) (mem1:t): forall (mem2:t), Prop :=
  | add_split_intro
      cell2
      (ALLOC: Cell.add_split from to to' msg msg' (mem1 loc) cell2):
      add_split loc from to to' msg msg' mem1 (LocFun.add loc cell2 mem1)
  .

  Inductive future (lhs rhs:t): Prop :=
  | future_intro
      (FUTURE: forall loc, Cell.future (lhs loc) (rhs loc))
  .

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation. econs. intros loc. reflexivity. Qed.
  Next Obligation. econs. inv H. inv H0. intros loc. etransitivity; eauto. Qed.

  Lemma add_new_unique loc from to msg mem1 mem2 mem2'
        (MEM2: add_new loc from to msg mem1 mem2)
        (MEM2': add_new loc from to msg mem1 mem2'):
    mem2 = mem2'.
  Proof.
    inv MEM2. inv MEM2'.
    exploit Cell.add_new_unique; [apply ALLOC|apply ALLOC0|]. i. subst. auto.
  Qed.

  Lemma add_split_unique loc from1 from2 to to1' to2' msg msg1' msg2' mem1 mem2 mem2'
        (MEM2: add_split loc from1 to to1' msg msg1' mem1 mem2)
        (MEM2': add_split loc from2 to to2' msg msg2' mem1 mem2'):
    from1 = from2 /\
    to1' = to2' /\
    msg1' = msg2' /\
    mem2 = mem2'.
  Proof.
    inv MEM2. inv MEM2'.
    exploit Cell.add_split_unique; [apply ALLOC|apply ALLOC0|]. i. des. subst.
    splits; auto.
  Qed.

  Lemma add_new_future
        loc from to msg mem1 mem2
        (DECLARE: add_new loc from to msg mem1 mem2):
    future mem1 mem2.
  Proof.
    econs. intro loc'.
    inv DECLARE. unfold LocFun.add.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c
    end.
    - subst. eapply Cell.add_new_future; eauto.
    - reflexivity.
  Qed.

  Lemma add_split_future
        loc from to to' msg msg' mem1 mem2
        (DECLARE: add_split loc from to to' msg msg' mem1 mem2):
    future mem1 mem2.
  Proof.
    econs. intro loc'.
    inv DECLARE. unfold LocFun.add.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c
    end.
    - subst. eapply Cell.add_split_future; eauto.
    - reflexivity.
  Qed.

  Lemma add_new_le
        loc from to msg mem1 mem2 mem1' mem2'
        (LE: le mem1 mem2)
        (ADD_NEW1: add_new loc from to msg mem1 mem1')
        (ADD_NEW2: add_new loc from to msg mem2 mem2'):
    le mem1' mem2'.
  Proof.
    econs. intro loc'.
    inv ADD_NEW1. inv ADD_NEW2. unfold LocFun.add.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c
    end.
    - subst. eapply Cell.add_new_le; eauto.
      inv LE. eauto.
    - apply LE.
  Qed.

  Lemma add_split_le
        loc from to to' msg msg' mem1 mem2 mem1'
        (LE: le mem1 mem2)
        (ADD_SPLIT1: add_split loc from to to' msg msg' mem1 mem1'):
    exists mem2',
      <<LE:le mem1' mem2'>> /\
      <<ADD_SPLIT2: add_split loc from to to' msg msg' mem2 mem2'>>.
  Proof.
    inv ADD_SPLIT1.
    exploit Cell.add_split_le; try apply LE; eauto. i. des.
    exists (LocFun.add loc cell2' mem2). splits.
    - econs. intro loc'. unfold LocFun.add.
      destruct (Loc.eq_dec loc' loc); auto.
      apply LE.
    - econs. auto.
  Qed.

  Definition remove (loc:Loc.t) (to:Time.t) (mem:t): t :=
    LocFun.add loc (Cell.remove to (mem loc)) mem.

  Lemma remove_disjoint
        loc ts mem1 mem2
        (DISJOINT: disjoint mem1 mem2):
    disjoint (remove loc ts mem1) mem2.
  Proof.
    econs. i. unfold remove, LocFun.add.
    destruct (LocSet.Facts.eq_dec loc0 loc).
    + apply Cell.remove_disjoint.
      inv DISJOINT. eauto.
    + apply DISJOINT.
  Qed.

  Lemma remove_le
        loc ts mem1 mem2
        (LE: le mem1 mem2):
    le (remove loc ts mem1) mem2.
  Proof.
    econs. i. unfold remove in *.
    unfold LocFun.add, LocFun.find in *.
    destruct (LocSet.Facts.eq_dec loc0 loc).
    - apply Cell.remove_le. inv LE. auto.
    - apply LE.
  Qed.
End Memory.
