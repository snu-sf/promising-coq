Require Import Omega.

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
  }.

  Definition wf (cell:t): Prop :=
    forall to1 to2 from1 from2 msg1 msg2
      (TO: to1 <> to2)
      (MESSAGE1: cell.(messages) to1 = Some (from1, msg1))
      (MESSAGE2: cell.(messages) to2 = Some (from2, msg2)),
      Interval.disjoint (from1, to1) (from2, to2).

  Lemma extensionality lhs rhs
        (MESSAGES: forall x, lhs.(messages) x = rhs.(messages) x):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    cut (messages0 = messages1).
    { i. subst. f_equal. apply proof_irrelevance. }
    extensionality to. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg (MSG: lhs.(messages) to = Some (from, msg)),
      rhs.(messages) to = Some (from, msg).

  Program Definition init: t :=
    mk
      (TimeFun.add Time.elt (Some (Time.decr Time.elt, Message.mk 0 Snapshot.init)) (TimeFun.init None))
      _.
  Next Obligation.
    unfold TimeFun.add in *.
    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end;
      inv MESSAGE.
    apply Time.decr_spec.
  Qed.

  Lemma init_wf: wf init.
  Proof.
    unfold wf, init. i. simpl in *.
    unfold TimeFun.add in *.
    repeat
      match goal with
      | [H: context[if ?c then _ else _] |- _] => destruct c
      | [H: Some _ = Some _ |- _] => inv H
      end;
      try inv MESSAGE1;
      try inv MESSAGE2.
    congruence.
  Qed.

  Inductive own (cell:t) (ts:Time.t): Prop :=
  | own_intro
      to from msg
      (MESSAGE: cell.(messages) to = Some (from, msg))
      (INTERVAL: Interval.mem (from, to) ts)
  .

  Definition disjoint (lhs rhs:t): Prop :=
    forall ts (LHS: own lhs ts) (RHS: own rhs ts), False.

  Lemma disjoint_comm lhs rhs
        (DISJ: disjoint lhs rhs):
    disjoint rhs lhs.
  Proof.
    ii. eapply DISJ; eauto.
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

  Program Definition join (lhs rhs:t): t :=
    mk
      (fun x =>
         match lhs.(messages) x, rhs.(messages) x with
         | Some _, Some _ => Some (Time.decr x, Message.elt)
         | Some lhs, None => Some lhs
         | None, Some rhs => Some rhs
         | None, None => None
         end)
      _.
  Next Obligation.
    destruct (messages lhs to) as [[]|] eqn:LHS,
             (messages rhs to) as [[]|] eqn:RHS; try inv MESSAGE.
    - apply Time.decr_spec.
    - exploit (lhs.(VOLUME)); eauto.
    - exploit (rhs.(VOLUME)); eauto.
  Qed.

  Lemma join_wf
        lhs rhs
        (DISJ: disjoint lhs rhs)
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (join lhs rhs).
  Proof.
    ii. simpl in *.
    destruct (messages lhs to1) as [[]|] eqn:LHS1,
             (messages rhs to1) as [[]|] eqn:RHS1;
      inv MESSAGE1;
    destruct (messages lhs to2) as [[]|] eqn:LHS2,
             (messages rhs to2) as [[]|] eqn:RHS2;
      inv MESSAGE2;
      try (eapply (disjoint_messages to1); eauto; fail);
      try (eapply (disjoint_messages to2); eauto; fail).
    - eapply LHS; eauto.
    - eapply DISJ; econs; eauto.
    - eapply DISJ; econs; eauto.
    - eapply RHS; eauto.
  Qed.

  Lemma join_assoc x y z:
    join (join x y) z = join x (join y z).
  Proof.
    apply extensionality. simpl. i.
    destruct (messages x x0), (messages y x0), (messages z x0); auto.
  Qed.

  Lemma join_le
        lhs rhs
        (DISJ: disjoint lhs rhs):
    le lhs (join lhs rhs).
  Proof.
    unfold join. ii. simpl in *.
    destruct (messages lhs to) as [[]|] eqn:LHS,
             (messages rhs to) as [[]|] eqn:RHS;
      try congruence.
    exfalso. eapply disjoint_messages; eauto.
  Qed.

  Lemma join_spec
        lhs rhs b
        (DISJ: disjoint lhs rhs)
        (LHS: le lhs b)
        (RHS: le rhs b):
    le (join lhs rhs) b.
  Proof.
    unfold join. ii. simpl in *.
    destruct (messages lhs to) as [[]|] eqn:LHS1,
             (messages rhs to) as [[]|] eqn:RHS1;
      inv MSG;
      try congruence.
    - exfalso. eapply disjoint_messages; eauto.
    - apply LHS. auto.
    - apply RHS. auto.
  Qed.

  Lemma join_comm lhs rhs:
    join lhs rhs = join rhs lhs.
  Proof.
    apply extensionality. simpl. i.
    destruct (messages lhs x), (messages rhs x); auto.
  Qed.

  Program Definition sub (lhs rhs:t): t :=
    mk
      (fun x =>
         match lhs.(messages) x, rhs.(messages) x with
         | _, Some _
         | None, _ => None
         | Some lhs, None => Some lhs
         end)
      _.
  Next Obligation.
    destruct (messages lhs to) eqn:LHS, (messages rhs to) eqn:RHS; inv MESSAGE.
    eapply VOLUME; eauto.
  Qed.

  Lemma sub_wf
        lhs rhs
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (sub lhs rhs).
  Proof.
    ii. simpl in *.
    destruct (messages lhs to1) as [[]|] eqn:LHS1,
             (messages rhs to1) as [[]|] eqn:RHS1;
      inv MESSAGE1;
    destruct (messages lhs to2) as [[]|] eqn:LHS2,
             (messages rhs to2) as [[]|] eqn:RHS2;
      inv MESSAGE2;
      try (eapply (disjoint_messages to1); eauto; fail);
      try (eapply (disjoint_messages to2); eauto; fail).
    eapply LHS; eauto.
  Qed.

  Lemma sub_le lhs rhs:
    le (sub lhs rhs) lhs.
  Proof.
    unfold sub. ii. simpl in *.
    destruct (messages lhs to) as [[]|] eqn:LHS,
             (messages rhs to) as [[]|] eqn:RHS;
      congruence.
  Qed.

  Lemma sub_spec lhs rhs
        (DISJ: disjoint lhs rhs):
    sub (join lhs rhs) rhs = lhs.
  Proof.
    apply extensionality. simpl. i.
    destruct (messages lhs x) as [[]|] eqn:LHS,
             (messages rhs x) as [[]|] eqn:RHS;
      try congruence.
    exfalso. eapply disjoint_messages; eauto.
  Qed.
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.
  Definition wf (mem:t): Prop := forall loc, Cell.wf (mem loc).
  Definition le (lhs rhs:t): Prop := forall loc, Cell.le (lhs loc) (rhs loc).

  Definition init: t := LocFun.init Cell.init.
  Lemma init_wf: wf init.
  Proof. intro loc. apply Cell.init_wf. Qed.

  Definition disjoint (lhs rhs:t): Prop :=
    forall loc, Cell.disjoint (lhs loc) (rhs loc).

  Lemma disjoint_comm lhs rhs
        (DISJ: disjoint lhs rhs):
    disjoint rhs lhs.
  Proof.
    intro loc. specialize (DISJ loc).
    apply Cell.disjoint_comm. auto.
  Qed.

  Definition join (lhs rhs:t): t :=
    fun loc => Cell.join (lhs loc) (rhs loc).

  Lemma join_wf
        lhs rhs
        (DISJ: disjoint lhs rhs)
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (join lhs rhs).
  Proof. intro loc. apply Cell.join_wf; auto. Qed.

  Lemma join_assoc x y z:
    join (join x y) z = join x (join y z).
  Proof. extensionality loc. apply Cell.join_assoc. Qed.

  Lemma join_le
        lhs rhs
        (DISJ: disjoint lhs rhs):
    le lhs (join lhs rhs).
  Proof. intro loc. apply Cell.join_le; auto. Qed.

  Lemma join_spec
        lhs rhs b
        (DISJ: disjoint lhs rhs)
        (LHS: le lhs b)
        (RHS: le rhs b):
    le (join lhs rhs) b.
  Proof. intro loc. apply Cell.join_spec; auto. Qed.

  Lemma join_comm lhs rhs:
    join lhs rhs = join rhs lhs.
  Proof. extensionality loc. apply Cell.join_comm. Qed.

  Definition sub (lhs rhs:t): t :=
    fun loc => Cell.sub (lhs loc) (rhs loc).

  Lemma sub_wf
        lhs rhs
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (sub lhs rhs).
  Proof. intro loc. apply Cell.sub_wf; auto. Qed.

  Lemma sub_le lhs rhs:
    le (sub lhs rhs) lhs.
  Proof. intro loc. apply Cell.sub_le. Qed.

  Lemma sub_spec lhs rhs
        (DISJ: disjoint lhs rhs):
    sub (join lhs rhs) rhs = lhs.
  Proof. extensionality loc. apply Cell.sub_spec. auto. Qed.
End Memory.


Module Memory.
  Structure t := mk {
    messages: MessageSet.t;
    used: IntervalSets.t;
  }.

  Definition init: t := mk MessageSet.empty IntervalSets.bot.

  Inductive step (thl1:ThreadLocal.t) (mem1:t): forall (e:option MemEvent.t) (thl2:ThreadLocal.t), Prop :=
  | step_read
      loc val ts released ord tc2
      (READ: Commit.read thl1.(ThreadLocal.tc) loc ts released ord tc2)
      (DECLARE: ~ IntervalSets.mem loc ts thl1.(ThreadLocal.declares))
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.read loc val ord))
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  | step_write
      loc val ts0 ts released ord tc2 declares2
      (WRITE: Commit.write thl1.(ThreadLocal.tc) loc ts released ord tc2)
      (DECLARE: IntervalSets.remove loc ts0 ts thl1.(ThreadLocal.declares) = Some declares2)
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.write loc val ord))
           (ThreadLocal.mk tc2 declares2)
  | step_update
      loc valr tsr releasedr valw tsw releasedw ord tc2 tc3 declares3
      (READ: Commit.read thl1.(ThreadLocal.tc) loc tsr releasedr ord tc2)
      (WRITE: Commit.write tc2 loc tsw releasedw ord tc3)
      (RELEASE: Snapshot.le releasedr releasedw)
      (DECLARE: IntervalSets.remove loc tsr tsw thl1.(ThreadLocal.declares) = Some declares3)
      (MESSAGE1: MessageSet.get loc tsr mem1.(messages) = Some (Message.mk valr releasedr))
      (MESSAGE2: MessageSet.get loc tsw mem1.(messages) = Some (Message.mk valw releasedw)):
      step thl1 mem1
           (Some (MemEvent.update loc valr valw ord))
           (ThreadLocal.mk tc3 declares3)
  | step_fence
      ord tc2
      (FENCE: Commit.fence thl1.(ThreadLocal.tc) ord tc2):
      step thl1 mem1
           (Some (MemEvent.fence ord))
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  | step_None
      tc2
      (COMMIT: Commit.le thl1.(ThreadLocal.tc) tc2):
      step thl1 mem1
           None
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  .

  Inductive declare (thl1:ThreadLocal.t) (mem1:t): forall (thl2:ThreadLocal.t) (mem2:t), Prop :=
  | declare_intro
      loc ts val released ts0 declares2 used2
      (TS: Time.lt ts0 ts)
      (LOCAL: ThreadLocal.declare loc ts0 ts thl1.(ThreadLocal.declares) mem1.(used) declares2 used2)
      (GET: MessageSet.get loc ts mem1.(messages) = None):
      declare thl1 mem1
              (ThreadLocal.mk thl1.(ThreadLocal.tc) declares2)
              (mk (MessageSet.set loc ts (Message.mk val released) mem1.(messages))
                  used2)
  .

  (* TODO: messages are in rhs.(used)? *)
  Inductive future (declares:IntervalSets.t) (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGE: forall loc ts, Message.future (MessageSet.get loc ts lhs.(messages)) (MessageSet.get loc ts rhs.(messages)))
      (DECLARE:
         forall loc ts (DECLARE: IntervalSets.mem loc ts declares),
           MessageSet.get loc ts lhs.(messages) = MessageSet.get loc ts rhs.(messages))
      (PERM: IntervalSets.le lhs.(used) rhs.(used))
  .
End Memory.




Module Commit.
  Structure t := mk {
    current: Snapshot.t;
    released: LocFun.t Snapshot.t;
    acquirable: Snapshot.t;
  }.

  Definition init: t := mk Snapshot.init (LocFun.init Snapshot.init) Snapshot.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: Snapshot.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Snapshot.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Snapshot.le lhs.(acquirable) rhs.(acquirable))
  .

  Inductive read
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | read_intro
      (FUTURE: le tc1 tc2)
      (READABLE: Snapshot.readable tc1.(current) loc ts)
      (READ: Time.le ts (Times.get loc tc2.(current).(Snapshot.reads)))
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le released tc2.(current))
      (ACQUIRABLE: Snapshot.le released tc2.(acquirable))
  .

  Inductive write
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | write_intro
      (FUTURE: le tc1 tc2)
      (WRITABLE: Snapshot.writable tc1.(current) loc ts)
      (WRITE: Time.le ts (Times.get loc tc2.(current).(Snapshot.writes)))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord),
          Snapshot.le tc2.(current) released)
      (RELEASED: Snapshot.le (LocFun.find loc tc2.(Commit.released)) released)
  .

  Inductive fence
            (tc1:t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | fence_intro
      (FUTURE: le tc1 tc2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le tc2.(acquirable) tc2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          Snapshot.le tc2.(current) (LocFun.find loc tc2.(released)))
  .
End Commit.

Module ThreadLocal.
  Structure t := mk {
    tc: Commit.t;
    declares: IntervalSets.t;
  }.

  Definition init := mk Commit.init IntervalSets.bot.

  Inductive declare
            (loc:Loc.t) (ts0 ts:Time.t)
            (declares1:IntervalSets.t) (used1:IntervalSets.t):
    forall (declares2:IntervalSets.t) (used2:IntervalSets.t), Prop :=
  | declare_alloc
      (DISJOINT: IntervalSets.disjoint loc ts0 ts used1):
      declare loc ts0 ts declares1 used1
              (IntervalSets.add loc ts0 ts declares1)
              (IntervalSets.add loc ts0 ts used1)
  | declare_split
      ts1 declares2
      (TIME: Time.lt ts ts1)
      (DECLARE: IntervalSets.remove loc ts0 ts1 declares1 = Some declares2):
      declare loc ts0 ts declares1 used1
              (IntervalSets.add loc ts0 ts (IntervalSets.add loc ts ts1 declares2))
              used1
  .
End ThreadLocal.
