Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.

Set Implicit Arguments.


Module ThreadEvent.
  Inductive program_t :=
  | silent
  | read (loc:Loc.t) (ts:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t)
  | write (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t)
  | update (loc:Loc.t) (tsr tsw:Time.t) (valr valw:Const.t) (releasedr releasedw:option View.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .

  Inductive t :=
  | promise (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:option View.t) (kind:Memory.op_kind)
  | program (event:program_t)
  .
  Coercion ThreadEvent.program: ThreadEvent.program_t >-> ThreadEvent.t.

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition get_program_event (e:program_t) : ProgramEvent.t :=
    match e with
    | silent => ProgramEvent.silent
    | read loc _ val _ ord => ProgramEvent.read loc val ord
    | write loc _ _ val _ ord => ProgramEvent.write loc val ord
    | update loc _ _ valr valw _ _ ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    | fence ordr ordw => ProgramEvent.fence ordr ordw
    | syscall ev => ProgramEvent.syscall ev
    end.

  Definition get_program (e:t): option program_t :=
    match e with
    | promise _ _ _ _ _ _ => None
    | program e => Some e
    end.

  Definition is_promising (e:t) : option (Loc.t * Time.t) :=
    match e with
    | promise loc from to v rel kind => Some (loc, to)
    | _ => None
    end.

  Definition is_lower_none (e:t) : bool :=
    match e with
    | promise loc from to v rel kind => Memory.op_kind_is_lower kind && negb rel
    | _ => false
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | update loc tsr _ valr _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | write loc from to val released ord => Some (loc, from, to, val, released, ord)
    | update loc tsr tsw _ valw _ releasedw _ ordw => Some (loc, tsr, tsw, valw, releasedw, ordw)
    | _ => None
    end.

  Definition is_accessing (e:t): option (Loc.t * Time.t) :=
    match e with
    | read loc ts _ _ _ => Some (loc, ts)
    | write loc _ ts _ _ _ => Some (loc, ts)
    | update loc _ ts _ _ _ _ _ _ => Some (loc, ts)
    | _ => None
    end.

  Inductive le: forall (lhs rhs:t), Prop :=
  | le_promise
      loc from to val rel1 rel2 kind1 kind2
      (LEREL: View.opt_le rel1 rel2):
      le (promise loc from to val rel1 kind1) (promise loc from to val rel2 kind2)
  | le_silent:
      le (program silent) (program silent)
  | le_read
      loc ts val rel1 rel2 ord
      (LEREL: View.opt_le rel1 rel2):
      le (read loc ts val rel1 ord) (read loc ts val rel2 ord)
  | le_write
      loc from to val rel1 rel2 ord
      (LEREL: View.opt_le rel1 rel2):
      le (write loc from to val rel1 ord) (write loc from to val rel2 ord)
  | le_update
      loc tsr tsw valr valw relr1 relr2 relw1 relw2 ordr ordw
      (LEREL: View.opt_le relr1 relr2)
      (LEREL: View.opt_le relw1 relw2):
      le (update loc tsr tsw valr valw relr1 relw1 ordr ordw) (update loc tsr tsw valr valw relr2 relw2 ordr ordw)
  | le_fence ordr ordw:
      le (fence ordr ordw) (fence ordr ordw)
  | le_syscall e:
      le (syscall e) (syscall e)
  .

  Definition lift (ord0:Ordering.t) (e:program_t): program_t :=
    match e with
    | silent => silent
    | read loc ts val released ord =>
      read loc ts val released (Ordering.join ord0 ord)
    | write loc from to val released ord =>
      write loc from to val released (Ordering.join ord0 ord)
    | update loc tsr tsw valr valw releasedr releasedw ordr ordw =>
      update loc tsr tsw valr valw releasedr releasedw (Ordering.join ord0 ordr) (Ordering.join ord0 ordw)
    | fence ordr ordw =>
      fence (Ordering.join ord0 ordr) (Ordering.join ord0 ordw)
    | syscall e =>
      syscall e
    end.

  Lemma lift_plain e:
    lift Ordering.plain e = e.
  Proof. destruct e; ss. Qed.
End ThreadEvent.
Coercion ThreadEvent.program: ThreadEvent.program_t >-> ThreadEvent.t.

Inductive tau T (step: forall (e:ThreadEvent.t) (e1 e2:T), Prop) (e1 e2:T): Prop :=
| tau_intro
    e
    (TSTEP: step e e1 e2)
    (EVENT: ThreadEvent.get_event e = None)
.
#[export]
Hint Constructors tau: core.

Inductive union E T (step: forall (e:E) (e1 e2:T), Prop) (e1 e2:T): Prop :=
| union_intro
    e
    (USTEP: step e e1 e2)
.
#[export]
Hint Constructors union: core.

Lemma tau_mon T (step1 step2: forall (e:ThreadEvent.t) (e1 e2:T), Prop)
      (STEP: step1 <3= step2):
  tau step1 <2= tau step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma union_mon E T (step1 step2: forall (e:E) (e1 e2:T), Prop)
      (STEP: step1 <3= step2):
  union step1 <2= union step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_union: tau <4= (@union ThreadEvent.t).
Proof.
  ii. inv PR. econs. eauto.
Qed.


Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: Memory.t;
  }.

  Definition init := mk TView.bot Memory.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: (promises lc) = Memory.bot)
  .

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf (tview lc))
      (TVIEW_CLOSED: TView.closed (tview lc) mem)
      (PROMISES: Memory.le (promises lc) mem)
      (FINITE: Memory.finite (promises lc))
  .

  Inductive disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (DISJOINT: Memory.disjoint (promises lc1) (promises lc2))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:option View.t): forall (lc2:t) (mem2:Memory.t) (kind:Memory.op_kind), Prop :=
  | promise_step_intro
      promises2 mem2 kind
      (PROMISE: Memory.promise (promises lc1) mem1 loc from to val released promises2 mem2 kind)
      (CLOSED: Memory.closed_opt_view released mem2):
      promise_step lc1 mem1 loc from to val released (mk (tview lc1) promises2) mem2 kind
  .

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | read_step_intro
      from
      tview2
      (GET: Memory.get loc to mem1 = Some (from, Message.mk val released))
      (READABLE: TView.readable (TView.cur (tview lc1)) loc to released ord)
      (TVIEW: TView.read_tview (tview lc1) loc to released ord = tview2):
      read_step lc1 mem1 loc to val released ord (mk tview2 (promises lc1))
  .

  Inductive write_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t): forall (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind), Prop :=
  | write_step_intro
      promises2 mem2 kind
      (RELEASED: released = TView.write_released (tview lc1) sc1 loc to releasedm ord)
      (WRITABLE: TView.writable (TView.cur (tview lc1)) sc1 loc to ord)
      (WRITE: Memory.write (promises lc1) mem1 loc from to val released promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.strong_relaxed ord ->
                Memory.nonsynch_loc loc (promises lc1) /\
                kind = Memory.op_kind_add):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord
                 (mk (TView.write_tview (tview lc1) sc1 loc to ord) promises2)
                 sc1 mem2 kind
  .

  Inductive fence_step (lc1:t) (sc1:TimeMap.t) (ordr ordw:Ordering.t): forall (lc2:t) (sc2:TimeMap.t), Prop :=
  | fence_step_intro
      tview2
      (READ: TView.read_fence_tview (tview lc1) ordr = tview2)
      (RELEASE: Ordering.le Ordering.strong_relaxed ordw -> Memory.nonsynch (promises lc1)):
      fence_step lc1 sc1 ordr ordw (mk (TView.write_fence_tview tview2 sc1 ordw) (promises lc1)) (TView.write_fence_sc tview2 sc1 ordw)
  .

  Inductive program_step: 
    forall (e:ThreadEvent.t) (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t), Prop :=
  | step_silent
      lc1 sc1 mem1:
      program_step ThreadEvent.silent lc1 sc1 mem1 lc1 sc1 mem1
  | step_read
      lc1 sc1 mem1
      loc ts val released ord lc2
      (LOCAL: Local.read_step lc1 mem1 loc ts val released ord lc2):
      program_step (ThreadEvent.read loc ts val released ord) lc1 sc1 mem1 lc2 sc1 mem1
  | step_write
      lc1 sc1 mem1
      loc from to val released ord lc2 sc2 mem2 kind
      (LOCAL: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      program_step (ThreadEvent.write loc from to val released ord) lc1 sc1 mem1 lc2 sc2 mem2
  | step_update
      lc1 sc1 mem1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 sc3 mem3 kind
      (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: Local.write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
      program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw) lc1 sc1 mem1 lc3 sc3 mem3
  | step_fence
      lc1 sc1 mem1
      ordr ordw lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      program_step (ThreadEvent.fence ordr ordw) lc1 sc1 mem1 lc2 sc2 mem1
  | step_syscall
      lc1 sc1 mem1
      e lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
      program_step (ThreadEvent.syscall e) lc1 sc1 mem1 lc2 sc2 mem1
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
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le ((View.rlx (View.unwrap released)) loc) to>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem2>>.
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
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem1>>.
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
        (REL_WF: View.opt_wf releasedm)
        (REL_CLOSED: Memory.closed_opt_view releasedm mem1)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le ((View.rlx (View.unwrap released)) loc) to>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem2>>.
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
    - refl.
    - inv WRITE. inv PROMISE; auto.
  Qed.

  Lemma fence_step_future lc1 sc1 mem1 ordr ordw lc2 sc2
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<SC2: Memory.closed_timemap sc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
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

  Lemma program_step_future e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl.
    - exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto. etrans; eauto.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
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
    (promises lc1) = (promises lc2).
  Proof.
    inv READ. auto.
  Qed.

  Lemma program_step_disjoint
        e lc1 sc1 mem1 lc2 sc2 mem2 lc
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto.
    - exploit read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit read_step_future; eauto. i. des.
      exploit read_step_disjoint; eauto. i. des.
      exploit write_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
  Qed.
End Local.


Module Thread.
  Section Thread.
    Variable (lang:language).

    Structure t := mk {
      state: (Language.state lang);
      local: Local.t;
      sc: TimeMap.t;
      memory: Memory.t;
    }.

    Inductive promise_step (pf:bool): forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to val released kind
        lc2 mem2
        (LOCAL: Local.promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
        (PF: pf = andb (Memory.op_kind_is_lower kind) (negb released)):
        promise_step pf (ThreadEvent.promise loc from to val released kind) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like an SC fence.
     *)
    Inductive program_step (e:ThreadEvent.program_t): forall (e1 e2:t), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem2)
    .
    #[local]
    Hint Constructors program_step: core.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_promise
        pf e e1 e2
        (STEP: promise_step pf e e1 e2):
        step pf e e1 e2
    | step_program
        e e1 e2
        (STEP: program_step e e1 e2):
        step true e e1 e2
    .
    #[local]
    Hint Constructors step: core.

    Inductive step_allpf (e:ThreadEvent.t) (e1 e2:t): Prop :=
    | step_nopf_intro
        pf
        (STEP: step pf e e1 e2)
    .
    #[local]
    Hint Constructors step_allpf: core.

    Lemma allpf pf: step pf <3= step_allpf.
    Proof.
      i. econs. eauto.
    Qed.

    Definition pf_tau_step := tau (step true).
    #[local]
    Hint Unfold pf_tau_step: core.

    Definition tau_step := tau step_allpf.
    #[local]
    Hint Unfold tau_step: core.

    Definition all_step := union step_allpf.
    #[local]
    Hint Unfold all_step: core.

    Inductive opt_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        pf e e1 e2
        (STEP: step pf e e1 e2):
        opt_step e e1 e2
    .
    #[local]
    Hint Constructors opt_step: core.

    Definition consistent (e:t): Prop :=
      forall sc1 mem1
        (FUTURE: Memory.future (memory e) mem1)
        (FUTURE: TimeMap.le (sc e) sc1)
        (WF: Local.wf (local e) mem1)
        (SC: Memory.closed_timemap sc1 mem1)
        (MEM: Memory.closed mem1),
      exists e2,
        <<STEPS: rtc tau_step (mk (state e) (local e) sc1 mem1) e2>> /\
        <<PROMISES: (Local.promises (local e2)) = Memory.bot>>.

    Lemma promise_step_future
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto. refl.
    Qed.

    Lemma program_step_future e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_future; eauto.
    Qed.

    Lemma step_future pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma step_nonpf_future e e1 e2
          (STEP: step false e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>> /\
      <<STATE: (state e1) = (state e2)>>.
    Proof.
      inv STEP. inv STEP0. ss.
      exploit Local.promise_step_future; eauto. i. des.
      esplits; ss. refl.
    Qed.

    Lemma opt_step_future e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future e1 e2
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H. inv USTEP.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma rtc_step_nonpf_future e1 e2
          (STEP: rtc (union (step false)) e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>> /\
      <<STATE: (state e1) = (state e2)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - inv H. i. exploit step_nonpf_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma promise_step_disjoint
          pf e e1 e2 lc
        (STEP: promise_step pf e e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      exploit Local.promise_step_future; eauto. i. des.
      exploit Local.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint e e1 e2 lc
        (STEP: program_step e e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint pf e e1 e2 lc
        (STEP: step pf e e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint e e1 e2 lc
        (STEP: opt_step e e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint e1 e2 lc
        (STEP: rtc all_step e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto. i.
      inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.

    Lemma rtc_tau_step_disjoint e1 e2 lc
        (STEP: rtc tau_step e1 e2)
        (WF1: Local.wf (local e1) (memory e1))
        (SC1: Memory.closed_timemap (sc e1) (memory e1))
        (CLOSED1: Memory.closed (memory e1))
        (DISJOINT1: Local.disjoint (local e1) lc)
        (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.
  End Thread.
End Thread.

Lemma promise_pf_inv
      (kind:Memory.op_kind)
      (released:option View.t)
      (PF: (Memory.op_kind_is_lower kind) && (negb released)):
  exists released0, kind = Memory.op_kind_lower released0 /\
               released = None.
Proof.
  apply andb_true_iff in PF. des.
  destruct kind; inv PF. destruct released; inv PF0.
  esplits; eauto.
Qed.

Lemma promise_pf_false_inv
      (kind:Memory.op_kind)
      (released:option View.t)
      (PF: false = (Memory.op_kind_is_lower kind) && (negb released)):
  Memory.op_kind_is_lower kind = false \/ released <> None.
Proof.
  symmetry in PF. apply andb_false_iff in PF. des; auto.
  destruct released; ss. right. ss.
Qed.
