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
Require Import Memory.
Require Import Commit.

Set Implicit Arguments.


Module ThreadEvent.
  Inductive t :=
  | silent
  | promise (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t)
  | read (loc:Loc.t) (ts:Time.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (ts:Time.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (tsr tsw:Time.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Ordering.t) :=
    match e with
    | read loc ts _ ord => Some (loc, ts, ord)
    | update loc tsr _ _ _ ordr _ => Some (loc, tsr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Ordering.t) :=
    match e with
    | write loc ts _ ord => Some (loc, ts, ord)
    | update loc _ tsw _ _ _ ordw => Some (loc, tsw, ordw)
    | _ => None
    end.
End ThreadEvent.


Module Local.
  Structure t := mk {
    commit: Commit.t;
    promises: Memory.t;
  }.

  Definition init := mk Commit.elt Memory.bot.

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
      commit2 promises2 mem2 kind
      (PROMISE: Memory.promise lc1.(promises) mem1 loc from to (Message.mk val released) promises2 mem2 kind)
      (COMMIT: Commit.le lc1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem2):
      promise_step lc1 mem1 loc from to val released (mk commit2 promises2) mem2 kind
  .

  Inductive silent_step (lc1:t) (mem1:Memory.t): forall (lc2:t), Prop :=
  | step_silent
      commit2
      (COMMIT: Commit.le lc1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1):
      silent_step lc1 mem1 (mk commit2 lc1.(promises))
  .

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:Capability.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_read
      from
      commit2
      (GET: Memory.get loc to mem1 = Some (from, Message.mk val released))
      (COMMIT: Commit.read lc1.(commit) loc to released ord commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1):
      read_step lc1 mem1 loc to val released ord (mk commit2 lc1.(promises))
  .

  Inductive fulfill_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedc releasedm:Capability.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_fulfill
      commit2 promises2
      (FULFILL: Memory.fulfill lc1.(promises) loc from to (Message.mk val releasedm) promises2)
      (COMMIT: Commit.write lc1.(commit) loc to releasedc ord commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1)
      (RELEASED_CLOSED: Memory.closed_capability releasedc mem1):
      fulfill_step lc1 mem1 loc from to val releasedc releasedm ord (mk commit2 promises2)
  .

  Inductive write_kind :=
  | write_kind_fulfill
  | write_kind_promise_fulfill
  .

  Inductive write_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedc releasedm:Capability.t) (ord:Ordering.t): forall (lc2:t) (mem2:Memory.t) (kind:write_kind), Prop :=
  | step_write_fulfill
      lc2
      (FULFILL: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
      (RELEASE: Ordering.le Ordering.acqrel ord -> lc1.(promises) loc = Cell.bot):
      write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem1 write_kind_fulfill
  | step_write_promise_fulfill
      lc2 mem2 lc3
      (PROMISE: promise_step lc1 mem1 loc from to val releasedm lc2 mem2 Memory.promise_kind_add)
      (FULFILL: fulfill_step lc2 mem2 loc from to val releasedc releasedm ord lc3)
      (RELEASE: Ordering.le Ordering.acqrel ord -> lc1.(promises) loc = Cell.bot):
      write_step lc1 mem1 loc from to val releasedc releasedm ord lc3 mem2 write_kind_promise_fulfill
  .

  Inductive fence_step (lc1:t) (mem1:Memory.t) (ordr ordw:Ordering.t): forall (lc2:t), Prop :=
  | step_fence
      commit2 commit3
      (READ: Commit.read_fence lc1.(commit) ordr commit2)
      (WRITE: Commit.write_fence commit2 ordw commit3)
      (RELEASE: Ordering.le Ordering.acqrel ordw -> lc1.(promises) = Memory.bot)
      (COMMIT_CLOSED: Commit.closed commit3 mem1):
      fence_step lc1 mem1 ordr ordw (mk commit3 lc1.(promises))
  .

  Lemma future_read_step lc1 mem1 mem1' loc ts val released ord lc2
        (FUTURE: Memory.future mem1 mem1')
        (STEP: read_step lc1 mem1 loc ts val released ord lc2):
    read_step lc1 mem1' loc ts val released ord lc2.
  Proof.
    inv STEP. exploit Memory.future_get; eauto. i. des.
    econs; eauto. eapply Commit.future_closed; eauto.
  Qed.

  Lemma future_fulfill_step lc1 mem1 mem1' loc from to val releasedc releasedm ord lc2
        (FUTURE: Memory.future mem1 mem1')
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2):
    fulfill_step lc1 mem1' loc from to val releasedc releasedm ord lc2.
  Proof.
    inv STEP. econs; eauto.
    - eapply Commit.future_closed; eauto.
    - eapply Memory.future_closed_capability; eauto.
  Qed.

  Lemma future_fence_step lc1 mem1 mem1' ordr ordw lc2
        (FUTURE: Memory.future mem1 mem1')
        (STEP: fence_step lc1 mem1 ordr ordw lc2):
    fence_step lc1 mem1' ordr ordw lc2.
  Proof.
    inv STEP. econs; eauto.
    eapply Commit.future_closed; eauto.
  Qed.

  Lemma promise_step_future lc1 mem1 loc from to val released lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma silent_step_future lc1 mem1 lc2
        (STEP: silent_step lc1 mem1 lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma read_step_future lc1 mem1 loc ts val released ord lc2
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. econs; ss. apply COMMIT.
  Qed.

  Lemma fulfill_step_future lc1 mem1 loc from to val releasedc releasedm ord lc2
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. econs; ss.
    - apply COMMIT.
    - eapply Memory.fulfill_future; eauto.
  Qed.

  Lemma write_step_future lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2 kind
        (STEP: write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP.
    - exploit fulfill_step_future; eauto. i. splits; ss. refl.
    - exploit promise_step_future; eauto. i. des.
      exploit fulfill_step_future; eauto.
  Qed.

  Lemma fence_step_future lc1 mem1 ordr ordw lc2
        (STEP: fence_step lc1 mem1 ordr ordw lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. econs; ss. apply WRITE.
  Qed.

  Lemma promise_step_disjoint
        lc1 mem1 loc from to val released lc2 mem2 lc kind
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.promise_future; try apply PROMISE; eauto. i. des.
    exploit Memory.promise_disjoint; try apply PROMISE; eauto. i. des.
    splits; ss. econs; eauto. eapply Commit.future_closed; eauto.
  Qed.

  Lemma silent_step_disjoint
        lc1 mem1 lc2 lc
        (STEP: silent_step lc1 mem1 lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
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

  Lemma fulfill_step_disjoint
        lc1 mem1 lc2 loc from to val releasedc releasedm ord lc
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    hexploit Memory.fulfill_future; try apply FULFILL; eauto. i. des.
    hexploit Memory.fulfill_disjoint; try apply FULFILL; try apply DISJOINT; eauto. i. des.
    econs. auto.
  Qed.

  Lemma write_step_disjoint
        lc1 mem1 lc2 loc from to val releasedc releasedm ord mem2 lc kind
        (STEP: write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv STEP.
    - exploit fulfill_step_future; eauto. i. des.
      exploit fulfill_step_disjoint; eauto.
    - exploit promise_step_future; eauto. i. des.
      exploit promise_step_disjoint; eauto. i. des.
      exploit fulfill_step_disjoint; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 mem1 lc2 ordr ordw lc
        (STEP: fence_step lc1 mem1 ordr ordw lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.
End Local.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Structure t := mk {
      state: lang.(Language.state);
      local: Local.t;
      memory: Memory.t;
    }.

    Inductive promise_step (e1:t) loc from to val released: forall (e2:t), Prop :=
    | promise_step_intro
        lc2 mem2 kind
        (LOCAL: Local.promise_step e1.(local) e1.(memory) loc from to val released lc2 mem2 kind):
        promise_step e1 loc from to val released (mk e1.(state) lc2 mem2)
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
        st1 lc1 mem1
        st2 lc2
        (STATE: lang.(Language.step) None st1 st2)
        (LOCAL: Local.silent_step lc1 mem1 lc2):
        program_step ThreadEvent.silent (mk st1 lc1 mem1) (mk st2 lc2 mem1)
    | step_read
        st1 lc1 mem1
        st2 loc ts val released ord lc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.read loc val ord)) st1 st2)
        (LOCAL: Local.read_step lc1 mem1 loc ts val released ord lc2):
        program_step (ThreadEvent.read loc ts val ord) (mk st1 lc1 mem1) (mk st2 lc2 mem1)
    | step_write
        st1 lc1 mem1
        st2 loc from to val released ord lc2 mem2 kind
        (STATE: lang.(Language.step) (Some (ProgramEvent.write loc val ord)) st1 st2)
        (LOCAL: Local.write_step lc1 mem1 loc from to val released released ord lc2 mem2 kind):
        program_step (ThreadEvent.write loc to val ord) (mk st1 lc1 mem1) (mk st2 lc2 mem2)
    | step_update
        st1 lc1 mem1
        st3 loc ordr ordw
        tsr valr releasedr lc2
        tsw valw releasedw lc3 mem3 kind
        (STATE: lang.(Language.step) (Some (ProgramEvent.update loc valr valw ordr ordw)) st1 st3)
        (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
        (LOCAL2: Local.write_step lc2 mem1 loc tsr tsw valw releasedw (Capability.join releasedr releasedw) ordw lc3 mem3 kind):
        program_step (ThreadEvent.update loc tsr tsw valr valw ordr ordw) (mk st1 lc1 mem1) (mk st3 lc3 mem3)
    | step_fence
        st1 lc1 mem1
        st2 ordr ordw lc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.fence ordr ordw)) st1 st2)
        (LOCAL: Local.fence_step lc1 mem1 ordr ordw lc2):
        program_step (ThreadEvent.fence ordr ordw) (mk st1 lc1 mem1) (mk st2 lc2 mem1)
    | step_syscall
        st1 lc1 mem1
        st2 e lc2
        (STATE: lang.(Language.step) (Some (ProgramEvent.syscall e)) st1 st2)
        (LOCAL: Local.fence_step lc1 mem1 Ordering.unordered Ordering.seqcst lc2):
        program_step (ThreadEvent.syscall e) (mk st1 lc1 mem1) (mk st2 lc2 mem1)
    .

    Inductive step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_promise
        loc from to val released e1 e2
        (STEP: promise_step e1 loc from to val released e2):
        step (ThreadEvent.promise loc from to val released) e1 e2
    | step_program
        e e1 e2
        (STEP: program_step e e1 e2):
        step e e1 e2
    .

    Inductive tau_step (e1 e2:t): Prop :=
    | step_tau
        e
        (STEP: step e e1 e2)
        (TAU: ThreadEvent.get_event e = None)
    .

    Definition consistent (e:t): Prop :=
      forall mem1
        (FUTURE: Memory.future e.(memory) mem1)
        (WF: Local.wf e.(local) mem1)
        (MEM: Memory.closed mem1),
      exists e2,
        <<STEPS: rtc tau_step (mk e.(state) e.(local) mem1) e2>> /\
        <<PROMISES: e2.(local).(Local.promises) = Memory.bot>>.

    Lemma promise_step_future
          loc from to val released e1 e2
          (STEP: promise_step e1 loc from to val released e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv WF1. inv STEP. s.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto. econs; eauto.
    Qed.

    Lemma program_step_future e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; ss.
      - exploit Local.silent_step_future; eauto. i. splits; ss. refl.
      - exploit Local.read_step_future; eauto. i. splits; ss. refl.
      - exploit Local.write_step_future; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.write_step_future; eauto.
      - exploit Local.fence_step_future; eauto. i. splits; ss. refl.
      - exploit Local.fence_step_future; eauto. i. splits; ss. refl.
    Qed.

    Lemma step_future e e1 e2
          (STEP: step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma rtc_step_future e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss. refl.
      - i. inv H.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss. etrans; eauto.
    Qed.

    Lemma promise_step_disjoint
          loc from to val released e1 e2 lc
        (STEP: promise_step e1 loc from to val released e2)
        (WF1: Local.wf e1.(local) e1.(memory))
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
        (CLOSED1: Memory.closed e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - exploit Local.silent_step_future; eauto. i.
        exploit Local.silent_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto.
      - exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i.
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

    Lemma rtc_step_disjoint e1 e2 lc
        (STEP: rtc tau_step e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
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
