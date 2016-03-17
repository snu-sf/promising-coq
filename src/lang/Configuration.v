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
Require Import Thread.
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
End Legacy.


Module Commit.
  Structure t := mk {
    current: Legacy.t;
    released: LocFun.t Legacy.t;
    acquirable: Legacy.t;
  }.

  Definition bot: t :=
    mk Legacy.bot (LocFun.init Legacy.bot) Legacy.bot.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: Legacy.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Legacy.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Legacy.le lhs.(acquirable) rhs.(acquirable))
  .

  Inductive fence (ord:Ordering.t) (th:t): Prop :=
  | fence_intro
      (ACQUIRE: forall (ORDERING: Ordering.ord Ordering.acquire ord),
          Legacy.le th.(acquirable) th.(current))
      (RELEASE: forall (ORDERING: Ordering.ord Ordering.release ord) loc,
          Legacy.le th.(current) (LocFun.find loc th.(released)))
  .
End Commit.


Module Message.
  Structure t := mk {
    val: Const.t;
    released: Legacy.t;
    confirmed: bool;
  }.
End Message.


Module Messages.
  Definition t := LocFun.t (UsualPositiveMap.t Message.t).

  Definition init: t :=
    LocFun.init
      (UsualPositiveMap.add
         1%positive
         (Message.mk 0 Legacy.bot true)
         (UsualPositiveMap.empty _)).

  Definition get (loc:Loc.t) (ts:positive) (m:t): option Message.t :=
    UsualPositiveMap.find ts (LocFun.find loc m).

  Inductive declare (loc:Loc.t) (ts:positive) (val:Const.t) (released:Legacy.t) (m1:t): forall (m2:t), Prop :=
  | declare_intro
      (GET: get loc ts m1 = None):
      declare loc ts val released m1
              (LocFun.add loc (UsualPositiveMap.add ts (Message.mk val released false) (LocFun.find loc m1)) m1)
  .

  Inductive read (commit:Commit.t) (loc:Loc.t) (ts:positive) (ord:Ordering.t) (m:t) (val:Const.t): Prop :=
  | read_intro
      released confirmed
      (COMMIT0: (Clock.get loc commit.(Commit.current).(Legacy.writes) <= ts)%positive)
      (COMMIT1: (ts <= Clock.get loc commit.(Commit.current).(Legacy.reads))%positive)
      (GET: Messages.get loc ts m = Some (Message.mk val released confirmed))
      (ACQUIRE: forall (ORDERING: Ordering.ord Ordering.acquire ord),
          Legacy.le commit.(Commit.current) released)
      (ACQUIRABLE: Legacy.le released commit.(Commit.acquirable)):
      read commit loc ts ord m val
  .

  Inductive write (commit1:Commit.t) (loc:Loc.t) (ts:positive) (val:Const.t) (ord:Ordering.t) (m1:t) (commit2:Commit.t): forall (m2:t), Prop :=
  | write_intro
      released
      (DECLARE: Messages.get loc ts m1 = Some (Message.mk val released false))
      (COMMIT0: Commit.le commit1 commit2)
      (COMMIT1: (Clock.get loc commit1.(Commit.current).(Legacy.writes) < ts)%positive)
      (COMMIT2: (Clock.get loc commit1.(Commit.current).(Legacy.reads) < ts)%positive)
      (COMMIT3: (ts <= Clock.get loc commit2.(Commit.current).(Legacy.writes))%positive)
      (RELEASE: forall (ORDERING: Ordering.ord Ordering.release ord),
          Legacy.le commit1.(Commit.current) (LocFun.find loc commit1.(Commit.released)))
      (RELEASED: Legacy.le (LocFun.find loc commit1.(Commit.released)) released):
      write commit1 loc ts val ord m1
            commit2
            (LocFun.add loc (UsualPositiveMap.add ts (Message.mk val released true) (LocFun.find loc m1)) m1)
  .

  Inductive declared (m:t): Prop :=
  | confirmed_intro
      loc ts val released
      (GET: Messages.get loc ts m = Some (Message.mk val released false))
  .
End Messages.


Module Configuration.
  Definition syntax := IdentMap.t Thread.syntax.

  Structure t := mk {
    messages: Messages.t;
    threads: IdentMap.t (Commit.t * Thread.t);
  }.

  Definition init (s:syntax): t :=
    mk Messages.init (IdentMap.map (fun th => (Commit.bot, Thread.init th)) s).

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid commit th (FIND: IdentMap.find tid c.(threads) = Some (commit, th)),
           Thread.is_terminal th)
  .

  Inductive base_step (c1:t): forall (reading:bool) (c2:t), Prop :=
  | step_tau
      tid commit th1 th2
      (TID: IdentMap.find tid c1.(threads) = Some (commit, th1))
      (THREAD: Thread.step th1 None th2):
      base_step
        c1 false
        (mk c1.(messages) (IdentMap.add tid (commit, th2) c1.(threads)))
  | step_read
      tid commit th1 th2
      loc ts ord val
      (TID: IdentMap.find tid c1.(threads) = Some (commit, th1))
      (READ: Messages.read commit loc ts ord c1.(messages) val)
      (THREAD: Thread.step th1 (Some (ThreadEvent.mem (MemEvent.read loc val ord))) th2):
      base_step
        c1 true
        (mk c1.(messages) (IdentMap.add tid (commit, th2) c1.(threads)))
  | step_write
      tid commit1 commit2 th1 th2
      loc ts ord val messages2
      (TID: IdentMap.find tid c1.(threads) = Some (commit1, th1))
      (WRITE: Messages.write commit1 loc ts val ord c1.(messages) commit2 messages2)
      (THREAD: Thread.step th1 (Some (ThreadEvent.mem (MemEvent.write loc val ord))) th2):
      base_step
        c1 false
        (mk messages2 (IdentMap.add tid (commit2, th2) c1.(threads)))
  | step_update
      tid commit1 commit2 th1 th2
      loc ts ord valr valw messages2
      (TID: IdentMap.find tid c1.(threads) = Some (commit1, th1))
      (READ: Messages.read commit1 loc ts ord c1.(messages) valr)
      (WRITE: Messages.write commit1 loc (ts + 1) valw ord c1.(messages) commit2 messages2)
      (RELEASE_TODO: True) (* (RELEASE: Legacy.le messager.(Message.released) messagew.(Message.released)): *)
      (THREAD: Thread.step th1 (Some (ThreadEvent.mem (MemEvent.update loc valr valw ord))) th2):
      base_step
        c1 true
        (mk messages2 (IdentMap.add tid (commit2, th2) c1.(threads)))
  | step_fence
      tid commit th1 th2
      ord
      (TID: IdentMap.find tid c1.(threads) = Some (commit, th1))
      (FENCE: Commit.fence ord commit)
      (THREAD: Thread.step th1 (Some (ThreadEvent.mem (MemEvent.fence ord))) th2):
      base_step
        c1 false
        (mk c1.(messages) (IdentMap.add tid (commit, th2) c1.(threads)))

  | step_declare
      loc ts val released messages2
      (DECLARE: Messages.declare loc ts val released c1.(messages) messages2):
      base_step
        c1 false
        (mk messages2 c1.(threads))
  | step_commit
      tid commit1 commit2 th
      (TID: IdentMap.find tid c1.(threads) = Some (commit1, th))
      (COMMIT: Commit.le commit1 commit2):
      base_step
        c1 false
        (mk c1.(messages) (IdentMap.add tid (commit2, th) c1.(threads)))
  .

  Inductive internal_step: forall (c1 c2:t), Prop :=
  | step_immediate
      c1 c2
      (STEP: base_step c1 false c2):
      internal_step c1 c2
  | step_validation
      c1 c2
      (STEP: base_step c1 true c2)
      (FEASIBLE: feasible c1):
      internal_step c1 c2
  with internal_steps: forall (c1 c2:t), Prop :=
  | steps_nil c:
      internal_steps c c
  | steps_cons
      c1 c2 c3
      (STEP: internal_step c1 c2)
      (STEPS: internal_steps c2 c3):
      internal_steps c1 c3
  with feasible: forall (c1:t), Prop :=
  | feasible_intro
      c1 c2
      (STEPS: internal_steps c1 c2)
      (CONFIRM: ~ Messages.declared c2.(messages)):
      feasible c1
  .

  Lemma internal_steps_append c1 c2 c3
        (STEPS12: internal_steps c1 c2)
        (STEPS23: internal_steps c2 c3):
    internal_steps c1 c3.
  Proof.
    revert c3 STEPS23. induction STEPS12; auto. i.
    econs 2; eauto.
  Qed.

  Lemma internal_steps_feasible c1 c2
        (STEPS: internal_steps c1 c2)
        (FEASIBLE: feasible c2):
    feasible c1.
  Proof.
    inv FEASIBLE. econs; [|eauto].
    eapply internal_steps_append; eauto.
  Qed.

  Lemma init_feasible s: feasible (init s).
  Proof.
    econs.
    - econs 1.
    - unfold init. simpl. intro X. inv X.
      unfold Messages.get, Messages.init in *.
      rewrite LocFun.init_spec in *.
      rewrite IdentMap.Facts.add_o in *.
      match goal with
      | [H: context[if ?cond then _ else _] |- _] =>
        destruct cond; inv H
      end.
      rewrite IdentMap.Facts.empty_o in *. inv H0.
  Qed.

  Inductive external_step (c1:t): forall (e:Event.t) (c2:t), Prop :=
  | step_syscall
      tid commit th1 th2
      e
      (TID: IdentMap.find tid c1.(threads) = Some (commit, th1))
      (THREAD: Thread.step th1 (Some (ThreadEvent.syscall e)) th2):
      external_step
        c1 e
        (mk c1.(messages) (IdentMap.add tid (commit, th2) c1.(threads)))
  .

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_internal
      c1 c2
      (STEP: internal_step c1 c2)
      (FEASIBLE: feasible c2):
      step c1 None c2
  | step_external
      c1 c2
      e
      (STEP: external_step c1 e c2)
      (FEASIBLE: feasible c2):
      step c1 (Some e) c2
  .
End Configuration.
