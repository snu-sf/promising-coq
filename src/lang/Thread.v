Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.

Set Implicit Arguments.


Module ThreadEvent.
  Inductive t :=
  | promise (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t) (kind: Memory.promise_kind)
  | silent
  | read (loc:Loc.t) (ts:Time.t) (val:Const.t) (released:Capability.t) (ord:Ordering.t)
  | write (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t) (ord:Ordering.t) (kind: Memory.promise_kind)
  | update (loc:Loc.t) (tsr tsw:Time.t) (valr valw:Const.t) (releasedr releasedw:Capability.t) (ordr ordw:Ordering.t) (kind: Memory.promise_kind)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Const.t * Capability.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | update loc tsr _ valr _ releasedr _ ordr _ _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Const.t * Capability.t * Ordering.t * Memory.promise_kind) :=
    match e with
    | write loc from to val released ord kind => Some (loc, from, to, val, released, ord, kind)
    | update loc tsr tsw _ valw _ releasedw _ ordw kind => Some (loc, tsr, tsw, valw, releasedw, ordw, kind)
    | _ => None
    end.
End ThreadEvent.


Module Local.
  Structure t := mk {
    commit: Commit.t;
    promises: Memory.t;
  }.

  Definition init := mk Commit.bot Memory.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: lc.(promises) = Memory.bot)
  .

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (COMMIT_WF: Commit.wf lc.(commit))
      (COMMIT_CLOSED: Commit.closed lc.(commit) mem)
      (PROMISES: Memory.le lc.(promises) mem)
  .

  Inductive disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (DISJOINT: Memory.disjoint lc1.(promises) lc2.(promises))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t): forall (lc2:t) (mem2:Memory.t) (kind:Memory.promise_kind), Prop :=
  | step_promise
      promises2 mem2 kind
      (PROMISE: Memory.promise lc1.(promises) mem1 loc from to val released promises2 mem2 kind)
      (CLOSED: Memory.closed_capability released mem2):
      promise_step lc1 mem1 loc from to val released (mk lc1.(commit) promises2) mem2 kind
  .

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:Capability.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_read
      from
      commit2
      (GET: Memory.get loc to mem1 = Some (from, Message.mk val released))
      (READABLE: Commit.readable lc1.(commit) loc to released ord)
      (COMMIT: Commit.read_commit lc1.(commit) loc to released ord = commit2):
      read_step lc1 mem1 loc to val released ord (mk commit2 lc1.(promises))
  .

  Inductive write_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:Capability.t) (ord:Ordering.t): forall (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.promise_kind), Prop :=
  | step_write
      promises2 mem2 kind
      (RELEASED: released = if Ordering.le Ordering.relaxed ord
                            then Capability.join releasedm ((Commit.write_commit lc1.(commit) sc1 loc to ord).(Commit.rel) loc)
                            else Capability.bot)
      (WRITABLE: Commit.writable lc1.(commit) sc1 loc to ord)
      (WRITE: Memory.write lc1.(promises) mem1 loc from to val released promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.acqrel ord ->
                lc1.(promises) loc = Cell.bot /\
                kind = Memory.promise_kind_add):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord
                 (mk (Commit.write_commit lc1.(commit) sc1 loc to ord) promises2)
                 (Commit.write_sc sc1 loc to ord)
                 mem2 kind
  .

  Inductive fence_step (lc1:t) (sc1:TimeMap.t) (ordr ordw:Ordering.t): forall (lc2:t) (sc2:TimeMap.t), Prop :=
  | step_fence
      commit2
      (READ: Commit.read_fence_commit lc1.(commit) ordr = commit2)
      (RELEASE: Ordering.le Ordering.acqrel ordw -> lc1.(promises) = Memory.bot):
      fence_step lc1 sc1 ordr ordw (mk (Commit.write_fence_commit commit2 sc1 ordw) lc1.(promises)) (Commit.write_fence_sc commit2 sc1 ordw)
  .

  Lemma promise_step_future lc1 sc1 mem1 loc from to val released lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc1 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: Capability.wf released>> /\
    <<REL_TS: Time.le (Capability.rw released loc) to>> /\
    <<REL_CLOSED: Memory.closed_capability released mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
    - econs; ss. eapply Commit.future_closed; eauto.
    - eapply Memory.future_closed_timemap; eauto.
    - inv PROMISE.
      + inv PROMISES0. inv ADD. auto.
      + inv PROMISES0. inv SPLIT. auto.
      + inv PROMISES0. inv LOWER. auto.
    - by inv PROMISE.
  Qed.

  Lemma read_step_future lc1 mem1 loc ts val released ord lc2
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<REL_WF: Capability.wf released>> /\
    <<REL_CLOSED: Memory.closed_capability released mem1>>.
  Proof.
    inv WF1. inv STEP.
    exploit CommitFacts.read_future; eauto.
    { eapply CLOSED1. eauto. }
    inv CLOSED1. exploit CLOSED; eauto. i. des.
    splits; auto. econs; eauto.
  Qed.

  Lemma promise_closed_capability
        promises1 mem1 commit1 sc1 loc from to val releasedm released ord promises2 mem2 kind
        (PROMISES: Memory.le promises1 mem1)
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: Commit.closed commit1 mem1)
        (CLOSED3: Memory.closed_capability releasedm mem1)
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
    Memory.closed_capability
      (if Ordering.le Ordering.relaxed ord
       then Capability.join
              releasedm
              (Commit.rel (Commit.write_commit commit1 sc1 loc to ord) loc)
       else Capability.bot)
      mem2.
  Proof.
    exploit Memory.promise_future0; eauto; try by committac. i. des.
    repeat (try condtac; committac).
    - eapply Memory.promise_closed_capability; eauto.
    - eapply Memory.promise_closed_capability; eauto. apply CLOSED2.
    - eapply LE_PROMISES2. eapply Memory.promise_get2. apply PROMISE.
    - econs; committac.
      eapply Memory.promise_closed_timemap; eauto.
    - eapply Memory.promise_closed_capability; eauto. apply CLOSED2.
  Qed.

  Lemma write_closed_capability
        promises1 mem1 commit1 sc1 loc from to val releasedm released ord promises2 mem2 kind
        (PROMISES: Memory.le promises1 mem1)
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: Commit.closed commit1 mem1)
        (CLOSED3: Memory.closed_capability releasedm mem1)
        (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind):
    Memory.closed_capability
      (if Ordering.le Ordering.relaxed ord
       then Capability.join
              releasedm
              (Commit.rel (Commit.write_commit commit1 sc1 loc to ord) loc)
       else Capability.bot)
      mem2.
  Proof.
    inv WRITE. eapply promise_closed_capability; eauto.
  Qed.

  Lemma write_step_future lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (REL_WF: Capability.wf releasedm)
        (REL_CLOSED: Memory.closed_capability releasedm mem1)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: Capability.wf released>> /\
    <<REL_TS: Time.le (Capability.rw released loc) to>> /\
    <<REL_CLOSED: Memory.closed_capability released mem2>>.
  Proof.
    assert (REL'_WF: Capability.wf released).
    { inv STEP. repeat (try condtac; committac; try apply WF1). }
    assert (REL'_TS: Time.le (Capability.rw released loc) to).
    { inv STEP. inv WRITE. inv PROMISE; auto. }
    assert (REL'_CLOSED: Memory.closed_capability released mem2).
    { inv STEP. eapply write_closed_capability; try apply WF1; eauto. }
    inv WF1. inv STEP.
    exploit Memory.write_future; try apply WRITE; eauto. i. des.
    exploit Memory.write_get2; try apply WRITE; eauto; try by committac. i.
    exploit CommitFacts.write_future; eauto.
    { eapply Commit.future_closed; eauto. }
    { eapply Memory.future_closed_timemap; eauto. }
    i. des. splits; eauto.
    - econs; ss.
    - apply CommitFacts.write_sc_incr.
  Qed.

  Lemma fence_step_future lc1 sc1 mem1 ordr ordw lc2 sc2
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<SC2: Memory.closed_timemap sc2 mem1>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>>.
  Proof.
    inv WF1. inv STEP.
    exploit CommitFacts.read_fence_future; eauto. i. des.
    exploit CommitFacts.write_fence_future; eauto. i. des.
    splits; eauto.
    - econs; eauto.
    - apply CommitFacts.write_fence_sc_incr.
  Qed.

  Lemma promise_step_disjoint
        lc1 sc1 mem1 loc from to val released lc2 mem2 lc kind
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.promise_future; try apply PROMISE; eauto. i. des.
    exploit Memory.promise_disjoint; try apply PROMISE; eauto. i. des.
    splits; ss. econs; eauto.
    eapply Commit.future_closed; eauto.
  Qed.

  Lemma read_step_disjoint
        lc1 mem1 lc2 loc ts val released ord lc
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma write_step_disjoint
        lc1 sc1 mem1 lc2 sc2 loc from to val releasedm released ord mem2 kind lc
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.write_future0; try apply WRITE; eauto; try by committac. i. des.
    exploit Memory.write_disjoint; try apply WRITE; eauto. i. des.
    splits; ss. econs; eauto.
    inv WRITE. eapply Commit.promise_closed; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 sc1 mem1 lc2 sc2 ordr ordw lc
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem1>>.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. splits; ss.
  Qed.

  Lemma read_step_promises
        lc1 mem loc to val released ord lc2
        (READ: read_step lc1 mem loc to val released ord lc2):
    lc1.(promises) = lc2.(promises).
  Proof.
    inv READ. auto.
  Qed.
End Local.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Structure t := mk {
      state: lang.(Language.state);
      local: Local.t;
      sc: TimeMap.t;
      memory: Memory.t;
    }.

    Inductive promise_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to val released kind
        lc2 mem2
        (LOCAL: Local.promise_step lc1 mem1 loc from to val released lc2 mem2 kind):
        promise_step (ThreadEvent.promise loc from to val released kind) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a write SC fence.  We did not let
     * syscalls act like a read SC fence, since it is enough to
     * disallow the weak behavior w/ SC & syscalls.
     *
     * If it is hard to explain, it is fine to let syscalls act like
     * both read & write SC fences.
     *
     * https://github.com/jeehoonkang/memory-model-explorer/issues/65
     *)
    Inductive program_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_silent
        st1 lc1 sc1 mem1
        st2
        (STATE: lang.(Language.step) None st1 st2):
        program_step ThreadEvent.silent (mk st1 lc1 sc1 mem1) (mk st2 lc1 sc1 mem1)
    | step_read
        st1 lc1 sc1 mem1
        st2 loc ts val released ord lc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.read loc val ord)) st1 st2)
        (LOCAL: Local.read_step lc1 mem1 loc ts val released ord lc2):
        program_step (ThreadEvent.read loc ts val released ord) (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc1 mem1)
    | step_write
        st1 lc1 sc1 mem1
        st2 loc from to val released ord lc2 sc2 mem2 kind
        (STATE: lang.(Language.step) (Some (ProgramEvent.write loc val ord)) st1 st2)
        (LOCAL: Local.write_step lc1 sc1 mem1 loc from to val Capability.bot released ord lc2 sc2 mem2 kind):
        program_step (ThreadEvent.write loc from to val released ord kind) (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem2)
    | step_update
        st1 lc1 sc1 mem1
        st3 loc ordr ordw
        tsr valr releasedr releasedw lc2
        tsw valw lc3 sc3 mem3 kind
        (STATE: lang.(Language.step) (Some (ProgramEvent.update loc valr valw ordr ordw)) st1 st3)
        (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
        (LOCAL2: Local.write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
        program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw kind) (mk st1 lc1 sc1 mem1) (mk st3 lc3 sc3 mem3)
    | step_fence
        st1 lc1 sc1 mem1
        st2 ordr ordw lc2 sc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.fence ordr ordw)) st1 st2)
        (LOCAL: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
        program_step (ThreadEvent.fence ordr ordw) (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem1)
    | step_syscall
        st1 lc1 sc1 mem1
        st2 e lc2 sc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.syscall e)) st1 st2)
        (LOCAL: Local.fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
        program_step (ThreadEvent.syscall e) (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem1)
    .

    Inductive step (e:ThreadEvent.t) (e1 e2:t): Prop :=
    | step_promise
        (STEP: promise_step e e1 e2)
    | step_program
        (STEP: program_step e e1 e2)
    .

    Inductive tau_step (e1 e2:t): Prop :=
    | step_tau
        e
        (STEP: step e e1 e2)
        (TAU: ThreadEvent.get_event e = None)
    .

    Inductive opt_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        e e1 e2
        (STEP: step e e1 e2):
        opt_step e e1 e2
    .

    Definition consistent (e:t): Prop :=
      forall sc1 mem1
        (FUTURE: Memory.future e.(memory) mem1)
        (FUTURE: TimeMap.le e.(sc) sc1)
        (WF: Local.wf e.(local) mem1)
        (SC: Memory.closed_timemap sc1 mem1)
        (MEM: Memory.closed mem1),
      exists e2,
        <<STEPS: rtc tau_step (mk e.(state) e.(local) sc1 mem1) e2>> /\
        <<PROMISES: e2.(local).(Local.promises) = Memory.bot>>.

    Lemma promise_step_future
          e e1 e2
          (STEP: promise_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP. ss.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto.
    Qed.

    Lemma program_step_future e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; ss.
      - splits; eauto; refl.
      - exploit Local.read_step_future; eauto. i. des. splits; ss; refl.
      - exploit Local.write_step_future; eauto; committac. i. des. auto.
      - exploit Local.read_step_future; eauto. i. des.
        exploit Local.write_step_future; eauto. i. des. auto.
      - exploit Local.fence_step_future; eauto. i. des. splits; ss. refl.
      - exploit Local.fence_step_future; eauto. i. des. splits; ss. refl.
    Qed.

    Lemma step_future e e1 e2
          (STEP: step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - exploit promise_step_future; eauto. i. des. splits; ss.
        inv STEP0. ss. refl.
      - eapply program_step_future; eauto.
    Qed.

    Lemma opt_step_future e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_step_future e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma promise_step_disjoint
          e e1 e2 lc
        (STEP: promise_step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      exploit Local.promise_step_future; eauto. i. des.
      exploit Local.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint e e1 e2 lc
        (STEP: program_step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - ss.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto.
      - exploit Local.write_step_future; eauto; try by committac. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i. des.
        exploit Local.read_step_disjoint; eauto. i.
        exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.fence_step_future; eauto. i.
        exploit Local.fence_step_disjoint; eauto.
      - exploit Local.fence_step_future; eauto. i.
        exploit Local.fence_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint e e1 e2 lc
        (STEP: step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint e e1 e2 lc
        (STEP: opt_step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_step_disjoint e1 e2 lc
        (STEP: rtc tau_step e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto. i. inv H.
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.
  End Thread.
End Thread.
