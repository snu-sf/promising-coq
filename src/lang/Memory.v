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

  Inductive own (cell:t) (ts:Time.t): Prop :=
  | own_intro
      to from msg
      (MESSAGE: cell.(messages) to = Some (from, msg))
      (INTERVAL: Interval.mem (from, to) ts)
  .

  Definition disjoint (lhs rhs:t): Prop :=
    forall ts (LHS: own lhs ts) (RHS: own rhs ts), False.

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

  Lemma disjoint_comm lhs rhs
        (DISJ: disjoint lhs rhs):
    disjoint rhs lhs.
  Proof.
    ii. eapply DISJ; eauto.
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

  Inductive declare (from to:Time.t) (msg:Message.t) (cell1 cell2:t): Prop :=
  | declare_add
      (MESSAGES1: cell1.(messages) to = None)
      (MESSAGES2: cell2.(messages) = TimeFun.add to (Some (from, msg)) cell1.(messages))
  | declare_split
      msg' middle
      (MESSAGES1: cell1.(messages) to = Some (from, msg'))
      (MESSAGES2: cell2.(messages) =
                  TimeFun.add middle (Some (from, msg))
                              (TimeFun.add to (Some (middle, msg)) cell1.(messages)))
  .

  Definition future: forall (lhs rhs:t), Prop :=
    rtc (fun c1 c2 => exists from to msg, declare from to msg c1 c2).

  Lemma declare_future
        from to msg cell1 cell2
        (DECLARE: declare from to msg cell1 cell2):
    future cell1 cell2.
  Proof.
    econs 2; [|econs 1].
    eexists _, _, _. eauto.
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
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (to:Time.t) (mem:t): option Message.t :=
    Cell.get to (mem loc).

  Definition le (lhs rhs:t): Prop := forall loc, Cell.le (lhs loc) (rhs loc).

  Definition disjoint (lhs rhs:t): Prop :=
    forall loc, Cell.disjoint (lhs loc) (rhs loc).

  Lemma disjoint_comm lhs rhs
        (DISJ: disjoint lhs rhs):
    disjoint rhs lhs.
  Proof.
    intro loc. specialize (DISJ loc).
    apply Cell.disjoint_comm. auto.
  Qed.

  Definition init: t := LocFun.init Cell.init.

  Inductive declare (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem1:t): forall (mem2:t), Prop :=
  | declare_intro
      cell2
      (ALLOC: Cell.declare from to msg (mem1 loc) cell2):
      declare loc from to msg mem1 (LocFun.add loc cell2 mem1)
  .

  Definition future: forall (lhs rhs:t), Prop :=
    rtc (fun c1 c2 => exists loc from to msg, declare loc from to msg c1 c2).

  Lemma declare_future
        loc from to msg mem1 mem2
        (DECLARE: declare loc from to msg mem1 mem2):
    future mem1 mem2.
  Proof.
    econs 2; [|econs 1].
    eexists _, _, _. eauto.
  Qed.

  Definition remove (loc:Loc.t) (to:Time.t) (mem:t): t :=
    LocFun.add loc (Cell.remove to (mem loc)) mem.
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
      (MONOTONE: le tc1 tc2)
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
      (MONOTONE: le tc1 tc2)
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
      (MONOTONE: le tc1 tc2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le tc2.(acquirable) tc2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          Snapshot.le tc2.(current) (LocFun.find loc tc2.(released)))
  .
End Commit.

Module ThreadLocal.
  Structure t := mk {
    commit: Commit.t;
    local: Memory.t;
  }.

  Definition init := mk Commit.init Memory.init.

  Inductive step (thl1:t) (mem1:Memory.t): forall (e:option MemEvent.t) (thl2:t), Prop :=
  | step_read
      loc val ts released ord commit2
      (READ: Commit.read thl1.(commit) loc ts released ord commit2)
      (MESSAGE: Memory.get loc ts mem1 = Some (Message.mk val released))
      (LOCAL: Memory.get loc ts thl1.(local) = None):
      step thl1 mem1
           (Some (MemEvent.read loc val ord))
           (mk commit2 thl1.(local))
  | step_write
      loc val ts released ord commit2
      (WRITE: Commit.write thl1.(commit) loc ts released ord commit2)
      (MESSAGE: Memory.get loc ts thl1.(local) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.write loc val ord))
           (mk commit2 (Memory.remove loc ts thl1.(local)))
  | step_update
      loc valr tsr releasedr valw tsw releasedw ord commit2 commit3
      (READ: Commit.read thl1.(commit) loc tsr releasedr ord commit2)
      (WRITE: Commit.write commit2 loc tsw releasedw ord commit3)
      (RELEASE: Snapshot.le releasedr releasedw)
      (MESSAGE1: Memory.get loc tsr mem1 = Some (Message.mk valr releasedr))
      (MESSAGE2: Memory.get loc tsw thl1.(local) = Some (Message.mk valw releasedw)):
      step thl1 mem1
           (Some (MemEvent.update loc valr valw ord))
           (mk commit3 (Memory.remove loc tsw thl1.(local)))
  | step_fence
      ord commit2
      (FENCE: Commit.fence thl1.(commit) ord commit2):
      step thl1 mem1
           (Some (MemEvent.fence ord))
           (mk commit2 thl1.(local))
  | step_None
      commit2
      (COMMIT: Commit.le thl1.(commit) commit2):
      step thl1 mem1
           None
           (mk commit2 thl1.(local))
  .

  Inductive declare (thl1:t) (mem1:Memory.t) (thl2:t) (mem2:Memory.t): Prop :=
  | declare_intro
      loc from to msg
      (COMMIT: Commit.le thl1.(commit) thl2.(commit))
      (LOCAL: Memory.declare loc from to msg thl1.(local) thl2.(local))
      (MEMORY: Memory.declare loc from to msg mem1 mem2)
  .
End ThreadLocal.
