Require Import List.
Require Import Equalities.
Require Import PeanoNat.
Require Import Relations.
Require Import MSetList.
Require Import Omega.

Require Import sflib.
Require Import paco.

Require Import DataStructure.
Require Import Basic.
Require Import Event.
Require Import Program.
Require Import UsualFMapPositive.

Set Implicit Arguments.
Import ListNotations.


Module Clock.
  Definition t := LocFun.t positive.

  Definition bot: t := LocFun.init 1%positive.

  Definition le (lhs rhs:t): Prop :=
    forall loc, (LocFun.find loc lhs <= LocFun.find loc rhs)%positive.

  Definition add (loc:Loc.t) (ts:positive) (c:t) :=
    LocFun.add loc (Pos.max (LocFun.find loc c) ts) c.

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Clock.


Module Legacy.
  Structure t := mk {
    writes: Clock.t;
    reads: Clock.t;
  }.

  Definition bot: t := mk Clock.bot Clock.bot.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (WRITES: Clock.le lhs.(writes) rhs.(writes))
      (READS: Clock.le lhs.(reads) rhs.(reads))
  .

  Inductive read (loc:Loc.t) (ts:positive) (l1 l2:t): Prop :=
  | read_intro
      (WRITES1: (Clock.get loc l1.(writes) <= ts)%positive)
      (READ2: (ts <= Clock.get loc l2.(reads))%positive)
  .

  Inductive write (loc:Loc.t) (ts:positive) (l1 l2:t): Prop :=
  | write_intro
      (WRITES1: (Clock.get loc l1.(writes) < ts)%positive)
      (READS1: (Clock.get loc l1.(reads) < ts)%positive)
      (WRITE2: (ts <= Clock.get loc l2.(writes))%positive)
  .
End Legacy.


Module Thread.
  Structure t := mk {
    commit: Legacy.t;
    released: LocFun.t Legacy.t;
    acquirable: Legacy.t;
  }.

  Definition init: t :=
    mk Legacy.bot (LocFun.init Legacy.bot) Legacy.bot.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (COMMIT: Legacy.le lhs.(commit) rhs.(commit))
      (RELEASED: forall (loc:Loc.t), Legacy.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Legacy.le lhs.(acquirable) rhs.(acquirable))
  .

  Inductive fence (ord:Ordering.t) (th:t): Prop :=
  | fence_intro
      (ACQUIRE: forall (ORDERING: Ordering.ord Ordering.acquire ord),
          Legacy.le th.(acquirable) th.(commit))
      (RELEASE: forall (ORDERING: Ordering.ord Ordering.release ord) loc,
          Legacy.le th.(commit) (LocFun.find loc th.(released)))
  .
End Thread.


Module Message.
  Structure t := mk {
    val: Const.t;
    released: Legacy.t;
    is_declared: option (IdentSet.t);
  }.

  Inductive lt (tid:Ident.t) (lhs rhs:t): Prop :=
  | lt_intro
      declared
      (VAL: lhs.(val) = rhs.(val))
      (RELEASED: lhs.(released) = rhs.(released))
      (DECLARED: lhs.(is_declared) = Some declared)
      (TID: IdentSet.In tid declared)
      (UNDECLARED: rhs.(is_declared) = None)
  .
End Message.


Module Messages.
  Definition t := LocFun.t (UsualPositiveMap.t Message.t).

  Definition init: t :=
    LocFun.init
      (UsualPositiveMap.add
         1%positive
         (Message.mk 0 Legacy.bot None)
         (UsualPositiveMap.empty _)).

  Definition get (loc:Loc.t) (ts:positive) (m:t): option Message.t :=
    UsualPositiveMap.find ts (LocFun.find loc m).

  Definition add (tid:Ident.t) (loc:Loc.t) (ts:positive) (message:Message.t) (m1:t): t :=
    LocFun.add loc (UsualPositiveMap.add ts message (LocFun.find loc m1)) m1.

  Inductive is_declared (m:t): Prop :=
  | declared_intro
      loc ts message declared
      (GET: get loc ts m = Some message)
      (DECLARED: message.(Message.is_declared) = Some declared)
  .
End Messages.


Module Memory.
  Structure t := mk {
    messages: Messages.t;
    threads: IdentFun.t Thread.t;
  }.

  Definition init: t :=
    mk Messages.init (IdentFun.init Thread.init).

  Inductive read (tid:Ident.t) (loc:Loc.t) (ts:positive) (message:Message.t) (ord:Ordering.t) (m:t) (th:Thread.t): Prop :=
  | read_intro
      (MESSAGE: Messages.get loc ts m.(messages) = Some message)
      (LE: Thread.le (IdentFun.find tid m.(threads)) th)
      (READ: Legacy.read loc ts (IdentFun.find tid m.(threads)).(Thread.commit) th.(Thread.commit))
      (ACQUIRE: forall (ORDERING: Ordering.ord Ordering.acquire ord),
          Legacy.le message.(Message.released) th.(Thread.commit))
      (ACQUIRABLE: Legacy.le message.(Message.released) th.(Thread.acquirable))
  .

  Inductive write (tid:Ident.t) (loc:Loc.t) (ts:positive) (message:Message.t) (ord:Ordering.t) (m:t) (th:Thread.t): Prop :=
  | write_intro
      (LE: Thread.le (IdentFun.find tid m.(threads)) th)
      (WRITE: Legacy.write loc ts (IdentFun.find tid m.(threads)).(Thread.commit) th.(Thread.commit))
      (RELEASE: forall (ORDERING: Ordering.ord Ordering.release ord),
          Legacy.le th.(Thread.commit) (LocFun.find loc th.(Thread.released)))
      (RELEASED: Legacy.le (LocFun.find loc th.(Thread.released)) message.(Message.released))
      (REPLACE: forall message0 (GET: Messages.get loc ts m.(messages) = Some message0), Message.lt tid message0 message)
  .

  Inductive step (tid:Ident.t) (m1:t): forall (e:option MemEvent.t) (m2:t), Prop :=
  | step_read
      loc ts message ord
      th2
      (READ: read tid loc ts message ord m1 th2):
      step tid m1
           (Some (MemEvent.read loc message.(Message.val) ord))
           (mk m1.(messages) (IdentFun.add tid th2 m1.(threads)))
  | step_write
      loc ts message ord
      th2
      (WRITE: write tid loc ts message ord m1 th2):
      step tid m1
           (Some (MemEvent.write loc message.(Message.val) ord))
           (mk
              (Messages.add tid loc ts message m1.(messages))
              (IdentFun.add tid th2 m1.(threads)))
  | step_update
      loc ts messager messagew ord
      th2
      (READ: read tid loc ts messager ord m1 th2)
      (WRITE: write tid loc (ts + 1) messagew ord m1 th2)
      (RELEASE: Legacy.le messager.(Message.released) messagew.(Message.released)):
      step tid m1
           (Some (MemEvent.update loc messager.(Message.val) messagew.(Message.val) ord))
           (mk
              (Messages.add tid loc (ts + 1) messagew m1.(messages))
              (IdentFun.add tid th2 m1.(threads)))
  | step_fence
      ord
      (FENCE: Thread.fence ord (IdentFun.find tid m1.(threads))):
      step tid m1
           (Some (MemEvent.fence ord))
           m1
  .
End Memory.
