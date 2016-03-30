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

  Definition allocatable (loc:Loc.t) (ts0 ts:Time.t) (perm:t): Prop :=
    forall x (ITV: Interval.time_mem x (ts0, ts)),
      ~ has_perm loc x perm.

  Definition add (loc:Loc.t) (ts0 ts:Time.t) (perm:t): t :=
    LocFun.add loc (IntervalSet.add (ts0, ts) (LocFun.find loc perm)) perm.
End Permission.

Module DeclareSet.
  Definition t := LocFun.t (TimeFun.t (option Time.t)).
  Definition empty: t := LocFun.init (TimeFun.init None).

	Definition get loc ts (ds:t): option Time.t :=
    TimeFun.find ts (LocFun.find loc ds).

	Definition set loc ts0 ts (ds:t): t :=
    LocFun.add loc (TimeFun.add ts (Some ts0) (LocFun.find loc ds)) ds.

	Definition unset loc ts (ds:t): t :=
    LocFun.add loc (TimeFun.add ts None (LocFun.find loc ds)) ds.
End DeclareSet.

(* TODO: merge with Module Thread *)
Module ThreadLocal.
  Structure t := mk {
    commit: Commit.t;
    declares: DeclareSet.t;
  }.

  Definition init := mk Commit.init DeclareSet.empty.
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

Module MessageSet.
  Definition t := LocFun.t (TimeFun.t (option Message.t)).
  Definition empty: t := LocFun.init (TimeFun.init None).

  Definition get (loc:Loc.t) (ts:Time.t) (m:t): option Message.t :=
    TimeFun.find ts (LocFun.find loc m).

  Definition set (loc:Loc.t) (ts:Time.t) (msg:Message.t) (m:t): t :=
    LocFun.add loc (TimeFun.add ts (Some msg) (LocFun.find loc m)) m.

  Definition add (loc:Loc.t) (ts:Time.t) (msg:Message.t) (m:t): option t :=
    if get loc ts m
    then None
    else Some (set loc ts msg m).
End MessageSet.

Module Memory.
  Structure t := mk {
    messages: MessageSet.t;
    permission: Permission.t;
  }.

  Definition init: t := mk MessageSet.empty Permission.bot.

  Inductive step (thl1:ThreadLocal.t) (mem1:t): forall (e:option MemEvent.t) (thl2:ThreadLocal.t), Prop :=
  | step_read
      loc val ts released ord commit2
      (READ: Commit.read thl1.(ThreadLocal.commit) loc ts released ord commit2)
      (DECLARE: DeclareSet.get loc ts thl1.(ThreadLocal.declares) = None)
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.read loc val ord))
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.declares))
  | step_write
      loc val ts0 ts released ord commit2
      (WRITE: Commit.write thl1.(ThreadLocal.commit) loc ts released ord commit2)
      (DECLARE: DeclareSet.get loc ts thl1.(ThreadLocal.declares) = Some ts0)
      (MESSAGE: MessageSet.get loc ts mem1.(messages) = Some (Message.mk val released)):
      step thl1 mem1
           (Some (MemEvent.write loc val ord))
           (ThreadLocal.mk commit2 (DeclareSet.unset loc ts thl1.(ThreadLocal.declares)))
  | step_update
      loc valr tsr releasedr valw tsw0 tsw releasedw ord commit2 commit3
      (READ: Commit.read thl1.(ThreadLocal.commit) loc tsr releasedr ord commit2)
      (WRITE: Commit.write commit2 loc tsw releasedw ord commit3)
      (RELEASE: History.le releasedr releasedw)
      (DECLARE: DeclareSet.get loc tsw thl1.(ThreadLocal.declares) = Some tsw0)
      (PERMISSION: Time.le tsw0 tsr)
      (MESSAGE1: MessageSet.get loc tsr mem1.(messages) = Some (Message.mk valr releasedr))
      (MESSAGE2: MessageSet.get loc tsw mem1.(messages) = Some (Message.mk valw releasedw)):
      step thl1 mem1
           (Some (MemEvent.update loc valr valw ord))
           (ThreadLocal.mk commit3 (DeclareSet.unset loc tsw thl1.(ThreadLocal.declares)))
  | step_fence
      ord commit2
      (FENCE: Commit.fence thl1.(ThreadLocal.commit) ord commit2):
      step thl1 mem1
           (Some (MemEvent.fence ord))
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.declares))
  | step_None
      commit2
      (COMMIT: Commit.le thl1.(ThreadLocal.commit) commit2):
      step thl1 mem1
           None
           (ThreadLocal.mk commit2 thl1.(ThreadLocal.declares))
  .

  Inductive declarable (loc:Loc.t) (ts0 ts:Time.t) (decls:DeclareSet.t) (perm:Permission.t): Prop :=
  | declarable_declares
      ts0' ts'
      (DECL:DeclareSet.get loc ts' decls = Some ts0')
      (TS0: Time.le ts0' ts0)
      (TS0: Time.lt ts ts')
  | declarable_alloc
      (ALLOC: Permission.allocatable loc ts0 ts perm)
  .

  Inductive declare (thl1:ThreadLocal.t) (mem1:t): forall (thl2:ThreadLocal.t) (mem2:t), Prop :=
  | declare_intro
      loc ts val released ts0 commit2
      (TS: Time.lt ts0 ts)
      (COMMIT: Commit.le thl1.(ThreadLocal.commit) commit2)
      (PERMISSION: declarable loc ts0 ts thl1.(ThreadLocal.declares) mem1.(permission))
      (GET: MessageSet.get loc ts mem1.(messages) = None):
      declare thl1 mem1
              (ThreadLocal.mk commit2 (DeclareSet.set loc ts0 ts thl1.(ThreadLocal.declares)))
              (mk (MessageSet.set loc ts (Message.mk val released) mem1.(messages))
                  (Permission.add loc ts0 ts mem1.(permission)))
  .

  Inductive future (decls:DeclareSet.t) (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGE: forall loc ts, Message.future (MessageSet.get loc ts lhs.(messages)) (MessageSet.get loc ts rhs.(messages)))
      (NONPERM:
         forall loc ts0 ts (DECL: DeclareSet.get loc ts decls = Some ts0),
         forall x (ITV: Interval.time_mem x (ts0, ts)),
           MessageSet.get loc x lhs.(messages) = MessageSet.get loc x rhs.(messages))
      (PERM: Permission.le lhs.(permission) rhs.(permission))
  .
End Memory.
