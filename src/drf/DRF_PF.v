Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import MemoryRel.
Require Import SmallStep.
Require Import Fulfilled.
Require Import Race.
Require Import PIStep.
Require Import PIStepProgress.
Require Import Lift.
Require Import PromiseConsistent.
Require Import PFConsistent.
Require Import PIStepPreservation.

Require Import OrdStep.
Require Import SimWhole.
Require Import Behavior.

Set Implicit Arguments.


Inductive sim_pf (c_src c_tgt:Configuration.t): Prop :=
| sim_pf_intro
    (WF: pi_wf loctmeq (c_src, c_tgt))
    (PI_CONSISTENT: pi_consistent (c_src, c_tgt))
    (CONSISTENT: Configuration.consistent c_tgt)
    (PI_RACEFREE: pf_racefree c_src)
.

Lemma sim_pf_init
      s
      (RACEFREE: pf_racefree (Configuration.init s)):
  sim_pf (Configuration.init s) (Configuration.init s).
Proof.
  econs; ss.
  - econs; ss.
    + apply Configuration.init_wf.
    + apply Configuration.init_wf.
    + destruct s; ss. unfold Threads.init.
      apply IdentMap.eq_leibniz. ii.
      rewrite ? IdentMap.Facts.map_o.
      match goal with
      | [|- context[IdentMap.find ?k ?m]] =>
        destruct (IdentMap.find k m) eqn:X
      end; ss.
    + i. esplits; eauto. ii. inv H.
      unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in TID.
      destruct (IdentMap.find tid s) eqn:X; ss. inv TID.
      apply inj_pair2 in H1. subst. ss.
      rewrite Memory.bot_get in *. ss.
    + i. esplits; eauto.
  - econs. i.
    exploit pi_steps_all_small_steps_all_snd.
    { eapply rtc_implies; try exact STEPS. i. inv PR. econs. eauto. }
    s. i.
    exploit small_steps_promise_decr; eauto. s. i. des.
    unfold Threads.init in FIND1. erewrite IdentMap.Facts.map_o in *.
    destruct (IdentMap.find tid s) eqn:X; ss. inv FIND1. ss.
    rewrite Memory.bot_get in *. ss.
  - apply Configuration.init_consistent.
Qed.

Lemma sim_pf_step
      c1_src c1_tgt
      c3_tgt e tid
      (SIM: sim_pf c1_src c1_tgt)
      (STEP_TGT: Configuration.step e tid c1_tgt c3_tgt):
  exists c2_src c3_src te,
    <<STEPS_SRC: rtc (tau (small_step false tid)) c1_src c2_src>> /\
    <<STEP_SRC: small_opt_step false tid te c2_src c3_src>> /\
    <<EVENT: ThreadEvent.get_event te = e>> /\
    <<SIM: sim_pf c3_src c3_tgt>>.
Proof.
  inv SIM.
  exploit Configuration.step_future; eauto.
  { inv WF. ss. }
  i. des.
  exploit pi_consistent_step_pi; eauto. i. des.
  exploit (@rtc_pi_step_future (c1_src, c1_tgt) cST2);
    (try eapply rtc_implies; try apply tau_union);
    eauto.
  { eapply rtc_implies; try apply STEPS. i.
    inv PR. econs. eauto.
  }
  s. i. des.
  exploit pi_step_future; eauto. s. i. des.
  exploit pi_consistent_pi_step_pi_consistent; cycle 4.
  { eapply rtc_n1.
    - eapply rtc_implies; try apply tau_union; eauto.
    - econs. eauto.
  }
  all: eauto. i.
  exploit tau_pi_steps_tau_small_steps_fst; eauto. s. i.
  exploit pi_step_small_step_fst; eauto. s. i.
  esplits; eauto.
  econs; eauto.
  eapply pf_racefree_steps; eauto.
  etrans.
  - eapply rtc_implies; [|apply x1]; eauto.
    i. inv PR. econs. eauto.
  - inv x2; eauto.
    econs 2; [|econs 1]. econs. eauto.
Qed.

Lemma init_has_promise s:
  ~ Configuration.has_promise (Configuration.init s).
Proof.
  ii. inv H.
  ss. unfold Threads.init in *. rewrite IdentMap.Facts.map_o in *.
  destruct (IdentMap.find tid s) as [[]|] eqn:X; ss. inv FIND. ss.
  rewrite Memory.bot_get in *. ss.
Qed.

Lemma sim_pf_has_promise
      c1 c2
      (SIM: sim_pf c1 c2):
  ~ Configuration.has_promise c1.
Proof.
  ii. inv H.
  inv SIM. inv WF. rewrite THS in *. clear -FIND GET.
  rewrite IdentMap.Facts.map_o in *.
  destruct (IdentMap.find tid c2.(Configuration.threads)) as [[]|] eqn:X; ss. inv FIND. ss.
  rewrite Memory.bot_get in *. ss.
Qed.

Lemma sim_pf_sim_whole:
  sim_pf <2= (sim_whole (ord_step_evt Ordering.plain) Configuration.step).
Proof.
  s. pcofix CIH. i. pfold. econs.
  - i. esplits; eauto. inv PR. inv WF. rewrite THS. clear -TERMINAL_TGT.
    ii. rewrite IdentMap.Facts.map_o in FIND.
    destruct (IdentMap.find tid x3.(Configuration.threads)) as [[]|] eqn:X; ss. inv FIND.
    exploit TERMINAL_TGT; eauto. i. des. esplits; ss.
  - hexploit sim_pf_has_promise; eauto. i.
    i. exploit sim_pf_step; eauto. i. des.
    exploit rtc_tau_small_step_false_rtc_union_ord_step_plain; eauto. i. des.
    esplits; [by eauto| |by eauto].
    inv STEP_SRC.
    + rewrite EVENT0. econs 1.
    + econs 2. hexploit small_step_false_ord_step_plain; eauto. i. des. subst.
      econs; eauto.
Qed.

Definition racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc (ord_step_all Ordering.plain) c1 c2)
    (RACE: race c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Theorem drf_pf
      s
      (RACEFREE: racefree (Configuration.init s)):
  behaviors Configuration.step (Configuration.init s) <1=
  behaviors (ord_step_evt Ordering.plain) (Configuration.init s).
Proof.
  apply sim_whole_adequacy, sim_pf_sim_whole, sim_pf_init.
  ii. eapply RACEFREE; [|eauto].
  eapply rtc_small_step_all_false_ord_step_all_plain; eauto.
  eapply init_has_promise.
Qed.
