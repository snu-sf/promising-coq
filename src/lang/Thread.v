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
Require Import TView.

Set Implicit Arguments.


Module ThreadEvent.
  Inductive t :=
  | promise (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:View.t)
  | silent
  | read (loc:Loc.t) (ts:Time.t) (val:Const.t) (released:View.t) (ord:Ordering.t)
  | write (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:View.t) (ord:Ordering.t)
  | update (loc:Loc.t) (tsr tsw:Time.t) (valr valw:Const.t) (releasedr releasedw:View.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Const.t * View.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | update loc tsr _ valr _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Const.t * View.t * Ordering.t) :=
    match e with
    | write loc from to val released ord => Some (loc, from, to, val, released, ord)
    | update loc tsr tsw _ valw _ releasedw _ ordw => Some (loc, tsr, tsw, valw, releasedw, ordw)
    | _ => None
    end.
End ThreadEvent.


Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: Memory.t;
  }.

  Definition init := mk TView.bot Memory.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: lc.(promises) = Memory.bot)
  .

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf lc.(tview))
      (TVIEW_CLOSED: TView.closed lc.(tview) mem)
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

  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:View.t): forall (lc2:t) (mem2:Memory.t) (kind:Memory.op_kind), Prop :=
  | step_promise
      promises2 mem2 kind
      (PROMISE: Memory.promise lc1.(promises) mem1 loc from to val released promises2 mem2 kind)
      (CLOSED: Memory.closed_view released mem2):
      promise_step lc1 mem1 loc from to val released (mk lc1.(tview) promises2) mem2 kind
  .

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:View.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_read
      from
      tview2
      (GET: Memory.get loc to mem1 = Some (from, Message.mk val released))
      (READABLE: TView.readable lc1.(tview) loc to released ord)
      (TVIEW: TView.read_tview lc1.(tview) loc to released ord = tview2):
      read_step lc1 mem1 loc to val released ord (mk tview2 lc1.(promises))
  .

  Inductive write_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:View.t) (ord:Ordering.t): forall (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind), Prop :=
  | step_write
      promises2 mem2 kind
      (RELEASED: released = TView.write_released lc1.(tview) sc1 loc to releasedm ord)
      (WRITABLE: TView.writable lc1.(tview) sc1 loc to ord)
      (WRITE: Memory.write lc1.(promises) mem1 loc from to val released promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.acqrel ord ->
                lc1.(promises) loc = Cell.bot /\
                kind = Memory.op_kind_add):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord
                 (mk (TView.write_tview lc1.(tview) sc1 loc to ord) promises2)
                 (TView.write_sc sc1 loc to ord)
                 mem2 kind
  .

  Inductive fence_step (lc1:t) (sc1:TimeMap.t) (ordr ordw:Ordering.t): forall (lc2:t) (sc2:TimeMap.t), Prop :=
  | step_fence
      tview2
      (READ: TView.read_fence_tview lc1.(tview) ordr = tview2):
      fence_step lc1 sc1 ordr ordw (mk (TView.write_fence_tview tview2 sc1 ordw) lc1.(promises)) (TView.write_fence_sc tview2 sc1 ordw)
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
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<REL_WF: View.wf released>> /\
    <<REL_TS: Time.le (released.(View.rlx) loc) to>> /\
    <<REL_CLOSED: Memory.closed_view released mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
    - econs; ss. eapply TView.future_closed; eauto.
    - eapply Memory.future_closed_timemap; eauto.
    - refl.
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
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<REL_WF: View.wf released>> /\
    <<REL_CLOSED: Memory.closed_view released mem1>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.read_future; eauto.
    { eapply CLOSED1. eauto. }
    inv CLOSED1. exploit CLOSED; eauto. i. des.
    splits; auto.
    - econs; eauto.
    - apply TViewFacts.read_tview_incr.
  Qed.

  Lemma write_step_future lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (REL_WF: View.wf releasedm)
        (REL_CLOSED: Memory.closed_view releasedm mem1)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: View.wf released>> /\
    <<REL_TS: Time.le (released.(View.rlx) loc) to>> /\
    <<REL_CLOSED: Memory.closed_view released mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.write_future; eauto.
    { inv WRITE. eapply Memory.promise_op. eauto. }
    s. i. des.
    exploit Memory.write_future; try apply WRITE; eauto. i. des.
    exploit Memory.write_get2; try apply WRITE; eauto; try by viewtac. i. des.
    splits; eauto.
    - econs; ss.
    - apply TViewFacts.write_tview_incr. auto.
    - apply TViewFacts.write_sc_incr.
    - inv WRITE. inv PROMISE; auto.
  Qed.

  Lemma fence_step_future lc1 sc1 mem1 ordr ordw lc2 sc2
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<SC2: Memory.closed_timemap sc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.read_fence_future; eauto. i. des.
    exploit TViewFacts.write_fence_future; eauto. i. des.
    splits; eauto.
    - econs; eauto.
    - etrans.
      + apply TViewFacts.write_fence_tview_incr. auto.
      + apply TViewFacts.write_fence_tview_mon; eauto; try refl.
        apply TViewFacts.read_fence_tview_incr. auto.
    - apply TViewFacts.write_fence_sc_incr.
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
    eapply TView.future_closed; eauto.
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
    exploit Memory.write_future0; try apply WRITE; eauto; try by viewtac. i. des.
    exploit Memory.write_disjoint; try apply WRITE; eauto. i. des.
    splits; ss. econs; eauto.
    inv WRITE. eapply TView.promise_closed; eauto.
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
        promise_step (ThreadEvent.promise loc from to val released) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like an SC fence.
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
        (LOCAL: Local.write_step lc1 sc1 mem1 loc from to val View.bot released ord lc2 sc2 mem2 kind):
        program_step (ThreadEvent.write loc from to val released ord) (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem2)
    | step_update
        st1 lc1 sc1 mem1
        st3 loc ordr ordw
        tsr valr releasedr releasedw lc2
        tsw valw lc3 sc3 mem3 kind
        (STATE: lang.(Language.step) (Some (ProgramEvent.update loc valr valw ordr ordw)) st1 st3)
        (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
        (LOCAL2: Local.write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
        program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw) (mk st1 lc1 sc1 mem1) (mk st3 lc3 sc3 mem3)
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
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
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
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; ss.
      - splits; eauto; refl.
      - exploit Local.read_step_future; eauto. i. des. splits; ss; refl.
      - exploit Local.write_step_future; eauto; viewtac. i. des. splits; ss.
      - exploit Local.read_step_future; eauto. i. des.
        exploit Local.write_step_future; eauto. i. des. splits; ss.
        etrans; eauto.
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
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
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
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
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
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
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
      - exploit Local.write_step_future; eauto; try by viewtac. i. des.
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
