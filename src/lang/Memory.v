Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.

Set Implicit Arguments.

Module Timestamps.
  Definition t := LocFun.t Time.t.
  Definition init: t := LocFun.init Time.elt.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (LocFun.find loc lhs) (LocFun.find loc rhs).

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Timestamps.

Module History.
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
      (* (CoRR: Time.le (Timestamps.get loc history.(History.reads)) ts) *)
      (CoWR: Time.le (Timestamps.get loc history.(History.writes)) ts)
  .

  Inductive writable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | writable_intro
      (CoRW: Time.lt (Timestamps.get loc history.(History.reads)) ts)
      (CoWW: Time.lt (Timestamps.get loc history.(History.writes)) ts)
  .
End History.

Module Commit.
  Structure t := mk {
    current: History.t;
    released: LocFun.t History.t;
    acquirable: History.t;
  }.

  Definition init: t := mk History.init (LocFun.init History.init) History.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: History.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), History.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: History.le lhs.(acquirable) rhs.(acquirable))
  .

  Inductive read
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:History.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_intro
      (FUTURE: le commit1 commit2)
      (READABLE: History.readable commit1.(current) loc ts)
      (READ: Time.le ts (Timestamps.get loc commit2.(current).(History.reads)))
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          History.le released commit2.(current))
      (ACQUIRABLE: History.le released commit2.(acquirable))
  .

  Inductive write
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:History.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_intro
      (FUTURE: le commit1 commit2)
      (WRITABLE: History.writable commit1.(current) loc ts)
      (WRITE: Time.le ts (Timestamps.get loc commit2.(current).(History.writes)))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord),
          History.le commit2.(current) released)
      (RELEASED: History.le (LocFun.find loc commit2.(Commit.released)) released)
  .

  Inductive fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | fence_intro
      (FUTURE: le commit1 commit2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          History.le commit2.(acquirable) commit2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          History.le commit2.(current) (LocFun.find loc commit2.(released)))
  .
End Commit.

Module Permission.
  Definition t := LocFun.t IntervalSet.t.
  Definition bot: t := LocFun.init IntervalSet.empty.

  Definition has_perm (loc:Loc.t) (ts:Time.t) (perm:t): Prop :=
    IntervalSet.time_mem ts (LocFun.find loc perm).

  Definition disjoint (lhs rhs:t): Prop :=
    forall loc, IntervalSet.time_disjoint (LocFun.find loc lhs) (LocFun.find loc rhs).

  Definition le (lhs rhs:t): Prop :=
    forall loc ts (LHS: IntervalSet.time_mem ts (LocFun.find loc lhs)),
      IntervalSet.time_mem ts (LocFun.find loc rhs).

  Definition add (loc:Loc.t) (ts0 ts:Time.t) (perm:t): t :=
    LocFun.add loc (IntervalSet.add (ts0, ts) (LocFun.find loc perm)) perm.
End Permission.

Module DeclareSet.
  Definition t := LocFun.t TimeSet.t.
  Definition empty: t := LocFun.init TimeSet.empty.

	Definition get loc ts (ds:t): bool :=
    TimeSet.mem ts (LocFun.find loc ds).

	Definition set loc ts (ds:t): t :=
    LocFun.add loc (TimeSet.add ts (LocFun.find loc ds)) ds.

	Definition unset loc ts (ds:t): t :=
    LocFun.add loc (TimeSet.remove ts (LocFun.find loc ds)) ds.

	Definition add loc ts (ds:t): option t :=
    if get loc ts ds
    then None
    else Some (set loc ts ds).

	Definition remove loc ts (ds:t): option t :=
    if get loc ts ds
    then Some (unset loc ts ds)
    else None.
End DeclareSet.

Module ThreadLocal.
  Structure t := mk {
    commit: Commit.t;
    permission: Permission.t;
    declares: DeclareSet.t;
  }.

  Definition init := mk Commit.init Permission.bot DeclareSet.empty.
End ThreadLocal.


Module Message.
  Structure t := mk {
    val: Const.t;
    released: History.t;
  }.

  Inductive future: forall (lhs rhs:option t), Prop :=
  | future_None rhs:
      future None rhs
  | future_Some msg:
      future (Some msg) (Some msg)
  .
End Message.

Module Memory.
  Structure t := mk {
    messages: LocFun.t (TimeFun.t (option Message.t));
    permission: Permission.t;
  }.

  Definition init: t :=
    mk (LocFun.init (TimeFun.add Time.elt (Some (Message.mk 0 History.init)) (TimeFun.init None)))
       Permission.bot.

  Definition get (loc:Loc.t) (ts:Time.t) (m:t): option Message.t :=
    TimeFun.find ts (LocFun.find loc m.(messages)).

  Definition set (loc:Loc.t) (ts:Time.t) (msg:Message.t) (m:t): t :=
    mk (LocFun.add loc (TimeFun.add ts (Some msg) (LocFun.find loc m.(messages))) m.(messages))
       m.(permission).

  Inductive add (perm:Permission.t) (loc:Loc.t) (ts0 ts:Time.t) (msg:Message.t) (lhs:t): forall (rhs:t), Prop :=
  | add_intro
      (PERM: forall x
               (ITV: Interval.time_mem x (ts0, ts))
               (MEM: Permission.has_perm loc x lhs.(permission)),
          Permission.has_perm loc x perm)
      (LHS: get loc ts lhs = None):
      add perm loc ts0 ts msg lhs (set loc ts msg lhs)
  .

  Inductive step (thl1:ThreadLocal.t) (mem1:t): forall (e:option MemEvent.t) (thl2:ThreadLocal.t), Prop :=
  | step_read
      loc val ts released ord commit2
      (COMMIT: Commit.read thl1.(ThreadLocal.commit) loc ts released ord commit2)
      (DECLARES: DeclareSet.get loc ts thl1.(ThreadLocal.declares) = false)
      (MEMORY: get loc ts mem1 = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.read loc val ord))
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.permission) thl1.(ThreadLocal.declares))
  | step_write
      loc val ts released ord commit2 declares2
      (COMMIT: Commit.write thl1.(ThreadLocal.commit) loc ts released ord commit2)
      (PERMISSION: Permission.has_perm loc ts thl1.(ThreadLocal.permission))
      (DECLARES: DeclareSet.remove loc ts thl1.(ThreadLocal.declares) = Some declares2)
      (MEMORY: get loc ts mem1 = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.write loc val ord))
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.permission) declares2)
  | step_update
      loc valr tsr releasedr valw tsw releasedw ord commit2 commit3 declares3
      (COMMIT1: Commit.read thl1.(ThreadLocal.commit) loc tsr releasedr ord commit2)
      (COMMIT2: Commit.write commit2 loc tsw releasedw ord commit3)
      (RELEASED: History.le releasedr releasedw)
      (PERMISSION: forall x (ITV: Interval.time_mem x (tsr, tsw)), IntervalSet.time_mem x (LocFun.find loc thl1.(ThreadLocal.permission)))
      (DECLARES: DeclareSet.remove loc tsw thl1.(ThreadLocal.declares) = Some declares3)
      (MEMORY1: get loc tsr mem1 = Some (Message.mk valr releasedr))
      (MEMORY2: get loc tsw mem1 = Some (Message.mk valw releasedw)):
      step thl1 mem1
           (Some (MemEvent.update loc valr valw ord))
           (ThreadLocal.mk commit3 thl1.(ThreadLocal.permission) declares3)
  | step_fence
      ord commit2
      (COMMIT: Commit.fence thl1.(ThreadLocal.commit) ord commit2):
      step thl1 mem1
           (Some (MemEvent.fence ord))
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.permission) thl1.(ThreadLocal.declares))
  | step_None
      commit2
      (COMMIT: Commit.le thl1.(ThreadLocal.commit) commit2):
      step thl1 mem1
           None
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.permission) thl1.(ThreadLocal.declares))
  .

  Inductive declare (thl1:ThreadLocal.t) (mem1:t): forall (thl2:ThreadLocal.t) (mem2:t), Prop :=
  | declare_intro
      loc ts val released ts0 thl2
      (TS: Time.le ts0 ts)
      (COMMIT: Commit.le thl1.(ThreadLocal.commit) thl2.(ThreadLocal.commit))
      (PERMISSION: Permission.add loc ts0 ts thl1.(ThreadLocal.permission) = thl2.(ThreadLocal.permission))
      (DECLARE: DeclareSet.add loc ts thl1.(ThreadLocal.declares) = Some thl2.(ThreadLocal.declares))
      (PERM: forall x (ITV: Interval.time_mem x (ts0, ts)) (MEM: Permission.has_perm loc x mem1.(permission)),
          Permission.has_perm loc x thl1.(ThreadLocal.permission))
      (GET: get loc ts mem1 = None):
      declare thl1 mem1 thl2 (set loc ts (Message.mk val released) mem1)
  .

  Inductive future (perm:Permission.t) (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGE: forall loc ts, Message.future (get loc ts lhs) (get loc ts rhs))
      (NONPERM: forall loc ts (NONPERM: Permission.has_perm loc ts perm),
          get loc ts lhs = get loc ts rhs)
      (PERM: Permission.le lhs.(permission) rhs.(permission))
  .
End Memory.
