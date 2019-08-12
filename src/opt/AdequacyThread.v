From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimThread.
Require Import Simulation.

Set Implicit Arguments.


Lemma singleton_consistent
      tid lang st lc sc mem
      (WF: Local.wf lc mem)
      (SC: Memory.closed_timemap sc mem)
      (MEM: Memory.closed mem)
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem)):
  <<WF: Configuration.wf (Configuration.mk (IdentMap.singleton tid (existT _ _ st, lc)) sc mem)>> /\
  <<CONSISTENT: Configuration.consistent (Configuration.mk (IdentMap.singleton tid (existT _ _ st, lc)) sc mem)>>.
Proof.
  econs; ss.
  - econs; ss. econs.
    + i.
      apply IdentMap.singleton_find_inv in TH1.
      apply IdentMap.singleton_find_inv in TH2.
      des. Configuration.simplify.
    + i. apply IdentMap.singleton_find_inv in TH. des.
      Configuration.simplify.
  - ii. apply IdentMap.singleton_find_inv in TH. des.
    Configuration.simplify.
    apply CONSISTENT; eauto.
Qed.

Lemma singleton_consistent_inv
      tid lang st lc sc mem
      (WF: Configuration.wf (Configuration.mk (IdentMap.singleton tid (existT _ _ st, lc)) sc mem))
      (CONSISTENT: Configuration.consistent (Configuration.mk (IdentMap.singleton tid (existT _ _ st, lc)) sc mem)):
  <<WF: Local.wf lc mem>> /\
  <<SC: Memory.closed_timemap sc mem>> /\
  <<MEM: Memory.closed mem>> /\
  <<CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem)>>.
Proof.
  inv WF. inv WF0. exploit THREADS; eauto.
  { apply IdentMap.singleton_eq. }
  i. splits; eauto.
  eapply CONSISTENT. apply IdentMap.singleton_eq.
Qed.

Lemma singleton_is_terminal
      tid lang st lc:
  Threads.is_terminal (IdentMap.singleton tid (existT _ _ st, lc)) <->
  <<STATE: lang.(Language.is_terminal) st>> /\
  <<THREAD: Local.is_terminal lc>>.
Proof.
  econs; intro X.
  - eapply X. apply IdentMap.singleton_eq.
  - ii. apply IdentMap.singleton_find_inv in FIND. i. des.
    Configuration.simplify.
Qed.

Lemma sim_thread_sim
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src sc0_src mem0_src
      st1_tgt lc1_tgt sc0_tgt mem0_tgt
      tid
      (SIM: @sim_thread lang_src lang_tgt sim_terminal
                        st1_src lc1_src sc0_src mem0_src
                        st1_tgt lc1_tgt sc0_tgt mem0_tgt):
  sim
    (IdentMap.singleton tid (existT _ _ st1_src, lc1_src)) sc0_src mem0_src
    (IdentMap.singleton tid (existT _ _ st1_tgt, lc1_tgt)) sc0_tgt mem0_tgt.
Proof.
  revert st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt SIM. pcofix CIH. i. pfold. ii.
  exploit singleton_consistent_inv; try apply WF_SRC; eauto. i. des.
  exploit singleton_consistent_inv; try apply WF_TGT; eauto. i. des.
  splits.
  - i. apply (singleton_is_terminal tid) in TERMINAL_TGT. des.
    punfold SIM. exploit SIM; try apply SC1; eauto. i. des.
    exploit TERMINAL; eauto. i. des.
    esplits; [|eauto|eauto|].
    + generalize (rtc_tail STEPS). intro X. des.
      * inv X0. inv TSTEP. destruct a2. econs 2; [|econs 1].
        econs. rewrite <- EVENT. econs; ss; eauto.
        { eapply IdentMap.singleton_eq. }
        { ii. eexists. splits; eauto. ss.
          eapply SimPromises.sem_bot_inv.
          inv THREAD. rewrite <- PROMISES0. apply LOCAL.
        }
      * inv X. s. erewrite IdentMap.singleton_add. econs.
    + ii. ss. rewrite IdentMap.singleton_add in *.
      apply IdentMap.singleton_find_inv in FIND. des. subst.
      splits; Configuration.simplify. econs; eauto.
      eapply SimPromises.sem_bot_inv.
      inv THREAD. rewrite <- PROMISES0. apply LOCAL.
  - i. inv STEP_TGT. ss.
    apply IdentMap.singleton_find_inv in TID. des.
    Configuration.simplify.
    exploit sim_thread_rtc_step; try apply STEPS; try apply SC1; eauto.
    { eapply sim_thread_future; eauto. }
    i. des. destruct e2. ss.
    exploit sim_thread_opt_step; try apply MEMORY; eauto.
    { econs 2. eauto. }
    i. des. rewrite STEPS1 in STEPS0. inv STEP0.
    { generalize (rtc_tail STEPS0). intro X. des.
      - inv X0. inv TSTEP. esplits; eauto.
        + rewrite <- EVENT. s. rewrite <- EVENT0.
          econs 2. econs; s.
          * apply IdentMap.singleton_eq.
          * etrans; eauto.
          * eauto.
          * eapply sim_thread_consistent; eauto.
        + right. s. rewrite ? IdentMap.singleton_add.
          apply CIH. ss.
      - inv X. esplits; eauto.
        + rewrite <- EVENT. s. instantiate (2 := tid). econs 1.
        + right. s. rewrite ? IdentMap.singleton_add.
          apply CIH. eauto.
    }
    esplits; eauto.
    + rewrite <- EVENT.
      econs 2. econs; s.
      * apply IdentMap.singleton_eq.
      * etrans; eauto.
      * eauto.
      * eapply sim_thread_consistent; eauto.
    + right. s. rewrite ? IdentMap.singleton_add.
      apply CIH. ss.
Qed.
