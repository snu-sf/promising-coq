Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import SmallStep.

Set Implicit Arguments.


Inductive ord_thread_step (ord:Ordering.t) (lang:language) (e:ThreadEvent.program_t): forall (e1 e2:Thread.t lang), Prop :=
| ra_thread_step_intro
    st1 lc1 sc1 mem1
    st2 lc2 sc2 mem2
    (STATE: (Language.step lang) (ThreadEvent.get_program_event (ThreadEvent.lift ord e)) st1 st2)
    (LOCAL: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
    ord_thread_step ord e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
.
Hint Constructors ord_thread_step.

Inductive ord_step (ord:Ordering.t) (e:ThreadEvent.program_t) (tid:Ident.t): forall (c1 c2:Configuration.t), Prop :=
| ord_step_intro
    c1 lang st1 lc1 st2 lc2 sc2 memory2
    (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
    (STEP: ord_thread_step ord e (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) (Thread.mk _ st2 lc2 sc2 memory2)):
    ord_step ord e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) sc2 memory2)
.

Inductive ord_step_evt (ord:Ordering.t) (e:option Event.t) (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| ord_step_evt_intro
    te
    (STEP: ord_step ord te tid c1 c2)
    (EVENT: e = ThreadEvent.get_event te)
.

Inductive ord_step_all (ord:Ordering.t) (c1 c2:Configuration.t): Prop :=
| ord_step_all_intro
    e tid
    (STEP: ord_step ord e tid c1 c2)
.

Definition interleaving (e:ThreadEvent.t) (c2:Configuration.t): bool :=
  match ThreadEvent.is_accessing e with
  | None => true
  | Some (loc, ts) =>
    Time.le_lt_dec (Memory.max_ts loc (Configuration.memory c2)) ts
  end.

Inductive interleaving_step (etid:ThreadEvent.program_t * Ident.t) (c1 c2:Configuration.t): Prop :=
| interleaving_step_intro
    (STEP: ord_step Ordering.acqrel (fst etid) (snd etid) c1 c2)
    (INTERLEAVING: interleaving (fst etid) c2)
.

Lemma ord_step_threads1
      ord e tid c1 c2
      (STEP: ord_step ord e tid c1 c2):
  exists th1, IdentMap.find tid (Configuration.threads c1) = Some th1.
Proof. inv STEP. eauto. Qed.

Lemma ord_step_threads2
      ord e tid c1 c2
      (STEP: ord_step ord e tid c1 c2):
  exists th2, IdentMap.find tid (Configuration.threads c2) = Some th2.
Proof. inv STEP. s. rewrite IdentMap.gss. eauto. Qed.

Lemma interleaving_step_threads1
      etid c1 c2
      (STEP: interleaving_step etid c1 c2):
  exists th1, IdentMap.find (snd etid) (Configuration.threads c1) = Some th1.
Proof. inv STEP. eapply ord_step_threads1. eauto. Qed.

Lemma interleaving_step_threads2
      etid c1 c2
      (STEP: interleaving_step etid c1 c2):
  exists th2, IdentMap.find (snd etid) (Configuration.threads c2) = Some th2.
Proof. inv STEP. eapply ord_step_threads2. eauto. Qed.

Lemma small_step_false_ord_step_plain
      tid e c1 c2
      (PROMISE: ~ Configuration.has_promise c1)
      (STEP: small_step false tid e c1 c2):
  exists pe,
    <<STEP: ord_step Ordering.plain pe tid c1 c2>> /\
    <<PROMISE: ~ Configuration.has_promise c2>> /\
    <<EVENT: e = pe>>.
Proof.
  inversion STEP. subst. inv STEP0.
  - contradict PROMISE.
    destruct pf; ss. inv STEP1.
    symmetry in PF. apply promise_pf_inv in PF. des. subst.
    inv LOCAL. inv PROMISE. exploit Memory.lower_get0; try exact PROMISES; eauto. i.
    econs; eauto.
  - esplits; eauto.
    + econs; eauto. inv STEP1. econs; eauto.
      rewrite ThreadEvent.lift_plain. ss.
    + contradict PROMISE. inv PROMISE. ss.
      exploit small_step_promise_decr; eauto. i. des.
      econs; eauto.
Qed.

Lemma rtc_tau_small_step_false_rtc_union_ord_step_plain
      tid c1 c2
      (PROMISE: ~ Configuration.has_promise c1)
      (STEP: rtc (tau (small_step false tid)) c1 c2):
  <<STEP: rtc (union (ord_step_evt Ordering.plain None)) c1 c2>> /\
  <<PROMISE: ~ Configuration.has_promise c2>>.
Proof.
  revert PROMISE. induction STEP.
  - i. esplits; eauto.
  - i. inv H. exploit small_step_false_ord_step_plain; eauto. i. des. subst.
    exploit IHSTEP; eauto. i. des.
    esplits; eauto. econs 2; eauto. econs. econs; eauto.
Qed.

Lemma rtc_small_step_all_false_ord_step_all_plain
      c1 c2
      (PROMISE: ~ Configuration.has_promise c1)
      (STEP: rtc (small_step_all false) c1 c2):
  <<STEP: rtc (ord_step_all Ordering.plain) c1 c2>> /\
  <<PROMISE: ~ Configuration.has_promise c2>>.
Proof.
  revert PROMISE. induction STEP.
  - i. esplits; eauto.
  - i. inv H. inv USTEP. exploit small_step_false_ord_step_plain; eauto. i. des. subst.
    exploit IHSTEP; eauto. i. des.
    esplits; eauto. econs 2; eauto. econs. eauto.
Qed.
