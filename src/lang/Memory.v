Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.

Set Implicit Arguments.

Module Timestamps.
  Definition t := LocFun.t Time.t.
  Definition init: t := LocFun.init Time.elt.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (LocFun.find loc lhs) (LocFun.find loc rhs).

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Timestamps.

Module Commit.
  Structure t := mk {
    reads: Timestamps.t;
    writes: Timestamps.t;
  }.

  Definition init: t := mk Timestamps.init Timestamps.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (READS: Timestamps.le lhs.(reads) rhs.(reads))
      (WRITES: Timestamps.le lhs.(writes) rhs.(writes))
  .

  Inductive readable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | readable_intro
      (* (CoRR: Time.le (Timestamps.get loc history.(Commit.reads)) ts) *)
      (CoWR: Time.le (Timestamps.get loc history.(Commit.writes)) ts)
  .

  Inductive writable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | writable_intro
      (CoRW: Time.lt (Timestamps.get loc history.(Commit.reads)) ts)
      (CoWW: Time.lt (Timestamps.get loc history.(Commit.writes)) ts)
  .
End Commit.


Module ThreadCommit.
  Structure t := mk {
    current: Commit.t;
    released: LocFun.t Commit.t;
    acquirable: Commit.t;
  }.

  Definition init: t := mk Commit.init (LocFun.init Commit.init) Commit.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: Commit.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Commit.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Commit.le lhs.(acquirable) rhs.(acquirable))
  .

  Inductive read
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Commit.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | read_intro
      (FUTURE: le tc1 tc2)
      (READABLE: Commit.readable tc1.(current) loc ts)
      (READ: Time.le ts (Timestamps.get loc tc2.(current).(Commit.reads)))
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Commit.le released tc2.(current))
      (ACQUIRABLE: Commit.le released tc2.(acquirable))
  .

  Inductive write
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Commit.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | write_intro
      (FUTURE: le tc1 tc2)
      (WRITABLE: Commit.writable tc1.(current) loc ts)
      (WRITE: Time.le ts (Timestamps.get loc tc2.(current).(Commit.writes)))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord),
          Commit.le tc2.(current) released)
      (RELEASED: Commit.le (LocFun.find loc tc2.(ThreadCommit.released)) released)
  .

  Inductive fence
            (tc1:t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | fence_intro
      (FUTURE: le tc1 tc2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Commit.le tc2.(acquirable) tc2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          Commit.le tc2.(current) (LocFun.find loc tc2.(released)))
  .
End ThreadCommit.

Module ThreadLocal.
  Structure t := mk {
    tc: ThreadCommit.t;
    declares: IntervalSets.t;
  }.

  Definition init := mk ThreadCommit.init IntervalSets.bot.

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
      (MEM: IntervalSets.remove loc ts0 ts1 declares1 = Some declares2):
      declare loc ts0 ts declares1 used1
              (IntervalSets.add loc ts0 ts (IntervalSets.add loc ts ts1 declares2))
              used1
  .
End ThreadLocal.


Module Message.
  Structure t := mk {
    val: Const.t;
    released: Commit.t;
  }.

  Inductive future: forall (lhs rhs:option t), Prop :=
  | future_None rhs:
      future None rhs
  | future_Some msg:
      future (Some msg) (Some msg)
  .
End Message.

Module MessageSet.
  Definition t := LocFun.t (TimeFun.t (option Message.t)).
  Definition empty: t := LocFun.init (TimeFun.init None).

  Definition get (loc:Loc.t) (ts:Time.t) (m:t): option Message.t :=
    TimeFun.find ts (LocFun.find loc m).

  Definition set (loc:Loc.t) (ts:Time.t) (msg:Message.t) (m:t): t :=
    LocFun.add loc (TimeFun.add ts (Some msg) (LocFun.find loc m)) m.
End MessageSet.

Module Memory.
  Structure t := mk {
    messages: MessageSet.t;
    used: IntervalSets.t;
  }.

  Definition init: t := mk MessageSet.empty IntervalSets.bot.

  Inductive step (thl1:ThreadLocal.t) (mem1:t): forall (e:option MemEvent.t) (thl2:ThreadLocal.t), Prop :=
  | step_read
      loc val ts released ord tc2
      (READ: ThreadCommit.read thl1.(ThreadLocal.tc) loc ts released ord tc2)
      (DECLARE: ~ IntervalSets.mem loc ts thl1.(ThreadLocal.declares))
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.read loc val ord))
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  | step_write
      loc val ts0 ts released ord tc2 declares2
      (WRITE: ThreadCommit.write thl1.(ThreadLocal.tc) loc ts released ord tc2)
      (DECLARE: IntervalSets.remove loc ts0 ts thl1.(ThreadLocal.declares) = Some declares2)
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.write loc val ord))
           (ThreadLocal.mk tc2 declares2)
  | step_update
      loc valr tsr releasedr valw tsw releasedw ord tc2 tc3 declares3
      (READ: ThreadCommit.read thl1.(ThreadLocal.tc) loc tsr releasedr ord tc2)
      (WRITE: ThreadCommit.write tc2 loc tsw releasedw ord tc3)
      (RELEASE: Commit.le releasedr releasedw)
      (DECLARE: IntervalSets.remove loc tsr tsw thl1.(ThreadLocal.declares) = Some declares3)
      (MESSAGE1: MessageSet.get loc tsr mem1.(messages) = Some (Message.mk valr releasedr))
      (MESSAGE2: MessageSet.get loc tsw mem1.(messages) = Some (Message.mk valw releasedw)):
      step thl1 mem1
           (Some (MemEvent.update loc valr valw ord))
           (ThreadLocal.mk tc3 declares3)
  | step_fence
      ord tc2
      (FENCE: ThreadCommit.fence thl1.(ThreadLocal.tc) ord tc2):
      step thl1 mem1
           (Some (MemEvent.fence ord))
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  | step_None
      tc2
      (COMMIT: ThreadCommit.le thl1.(ThreadLocal.tc) tc2):
      step thl1 mem1
           None
           (ThreadLocal.mk tc2 thl1.(ThreadLocal.declares))
  .

  Inductive declare (thl1:ThreadLocal.t) (mem1:t): forall (thl2:ThreadLocal.t) (mem2:t), Prop :=
  | declare_intro
      loc ts val released ts0 tc2 declares2 used2
      (TS: Time.lt ts0 ts)
      (COMMIT: ThreadCommit.le thl1.(ThreadLocal.tc) tc2)
      (LOCAL: ThreadLocal.declare loc ts0 ts thl1.(ThreadLocal.declares) mem1.(used) declares2 used2)
      (GET: MessageSet.get loc ts mem1.(messages) = None):
      declare thl1 mem1
              (ThreadLocal.mk tc2 declares2)
              (mk (MessageSet.set loc ts (Message.mk val released) mem1.(messages))
                  used2)
  .

  Inductive future (declares:IntervalSets.t) (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGE: forall loc ts, Message.future (MessageSet.get loc ts lhs.(messages)) (MessageSet.get loc ts rhs.(messages)))
      (NONPERM:
         forall loc ts (DECL: IntervalSets.mem loc ts declares),
           MessageSet.get loc ts lhs.(messages) = MessageSet.get loc ts rhs.(messages))
      (PERM: IntervalSets.le lhs.(used) rhs.(used))
  .
End Memory.
