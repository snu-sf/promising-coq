Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import MemInv.

Set Implicit Arguments.


Section SimulationLocal.
  Variable (lang_src lang_tgt:Language.t).

  Definition SIM_TERMINAL :=
    forall (st_src:lang_src.(Language.state)) (st_tgt:lang_tgt.(Language.state)), Prop.

  Definition SIM_LOCAL := forall (lc_src lc_tgt:Local.t), Prop.

  Inductive sim_local (lc_src lc_tgt:Local.t): Prop :=
  | sim_local_intro
      (COMMIT: Commit.le lc_src.(Local.commit) lc_tgt.(Local.commit))
      (PROMISES: MemInv.sem Promises.bot lc_src.(Local.promises) lc_tgt.(Local.promises))
  .

  Global Program Instance sim_local_Preorder: PreOrder sim_local.
  Next Obligation.
    ii. econs.
    - reflexivity.
    - apply MemInv.sem_bot.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etrans; eauto.
    - apply MemInv.sem_bot_inv in PROMISES.
      apply MemInv.sem_bot_inv in PROMISES0.
      rewrite PROMISES, PROMISES0.
      apply MemInv.sem_bot.
  Qed.

  Definition SIM_THREAD :=
    forall (sim_terminal: SIM_TERMINAL)
      (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (mem_k_src:Memory.t)
      (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (mem_k_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (sim_thread: forall (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (mem_k_src:Memory.t)
                            (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (mem_k_tgt:Memory.t), Prop)
             st1_src lc1_src mem1_src
             st1_tgt lc1_tgt mem1_tgt
    :=
    forall e st3_tgt lc3_tgt mem3_tgt
      (STEP_TGT: Thread.step e
                             (Thread.mk _ st1_tgt lc1_tgt mem1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt mem3_tgt)),
    exists st2_src lc2_src mem2_src st3_src lc3_src mem3_src,
      <<STEPS: rtc (Thread.step None)
                   (Thread.mk _ st1_src lc1_src mem1_src)
                   (Thread.mk _ st2_src lc2_src mem2_src)>> /\
      <<STEP_SRC: Thread.step e
                              (Thread.mk _ st2_src lc2_src mem2_src)
                              (Thread.mk _ st3_src lc3_src mem3_src)>> /\
      <<MEMORY2: sim_memory mem3_src mem3_tgt>> /\
      <<SIM: sim_thread st3_src lc3_src mem3_src st3_tgt lc3_tgt mem3_tgt>>.

  (* TODO: inftau & liveness *)
  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: SIM_TERMINAL)
             (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (mem_k_src:Memory.t)
             (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st1_tgt),
        exists st2_src lc2_src mem2_src,
          <<STEPS: rtc (Thread.step None)
                       (Thread.mk _ st1_src lc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: lang_src.(Language.is_terminal) st2_src>> /\
          <<LOCAL: sim_local lc2_src lc1_tgt>> /\
          <<TERMINAL: sim_terminal st2_src st1_tgt>>>> /\
      <<FUTURE:
        forall mem2_src
          (FUTURE_SRC: Memory.future mem1_src mem2_src)
          (WF_SRC: Local.wf lc1_src mem2_src),
        exists mem2_tgt,
          <<MEMORY: sim_memory mem2_src mem2_tgt>> /\
          <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
          <<WF_TGT: Local.wf lc1_tgt mem2_tgt>>>> /\
      <<PROMISES:
        forall (PROMISES_TGT: lc1_tgt.(Local.promises) = Promises.bot),
        exists st2_src lc2_src mem2_src,
          <<STEPS: rtc (Thread.step None)
                       (Thread.mk _ st1_src lc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src mem2_src)>> /\
          <<PROMISES_SRC: lc2_src.(Local.promises) = Promises.bot>>>> /\
      <<STEP: _sim_thread_step (sim_thread sim_terminal)
                               st1_src lc1_src mem1_src
                               st1_tgt lc1_tgt mem1_tgt>>.

  Lemma _sim_thread_mon: monotone7 _sim_thread.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco7 _sim_thread bot7.

  Lemma sim_thread_mon
        sim_terminal1 sim_terminal2
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <6= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des.
      eexists _, _, _. splits; eauto.
    - ii. exploit STEP; eauto. i. des; [|done].
      eexists _, _, _, _, _, _. splits; eauto.
  Qed.
End SimulationLocal.
Hint Resolve _sim_thread_mon: paco.


Section Simulation.
  Definition SIM :=
    forall (ths1_src:Threads.t) (mem_k_src:Memory.t)
      (ths1_tgt:Threads.t) (mem_k_tgt:Memory.t), Prop.

  (* TODO: inftau & liveness *)
  Definition _sim
             (sim: SIM)
             (ths1_src:Threads.t) (mem_k_src:Memory.t)
             (ths1_tgt:Threads.t) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (CONSISTENT_SRC: Configuration.consistent (Configuration.mk ths1_src mem1_src))
      (CONSISTENT_TGT: Configuration.consistent (Configuration.mk ths1_tgt mem1_tgt))
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
        exists ths2_src mem2_src,
          <<STEPS: rtc (Configuration.step None) (Configuration.mk ths1_src mem1_src) (Configuration.mk ths2_src mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: Threads.is_terminal ths2_src>>>> /\
      <<STEP:
        forall e ths3_tgt mem3_tgt
          (STEP_TGT: Configuration.step e (Configuration.mk ths1_tgt mem1_tgt) (Configuration.mk ths3_tgt mem3_tgt)),
        exists ths2_src mem2_src ths3_src mem3_src,
          <<STEPS: rtc (Configuration.step None) (Configuration.mk ths1_src mem1_src) (Configuration.mk ths2_src mem2_src)>> /\
          <<STEP_SRC: Configuration.step e (Configuration.mk ths2_src mem2_src) (Configuration.mk ths3_src mem3_src)>> /\
          <<MEMORY2: sim_memory mem3_src mem3_tgt>> /\
          <<SIM: sim ths3_src mem3_src ths3_tgt mem3_tgt>>>>.

  Lemma _sim_mon: monotone4 _sim.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco4 _sim bot4.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src mem_k1_src mem_k2_src
      st_tgt lc_tgt mem_k1_tgt mem_k2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src mem_k1_src st_tgt lc_tgt mem_k1_tgt)
      (FUTURE_SRC: Memory.future mem_k1_src mem_k2_src)
      (FUTURE_TGT: Memory.future mem_k1_tgt mem_k2_tgt):
  sim_thread sim_terminal st_src lc_src mem_k2_src st_tgt lc_tgt mem_k2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.


Lemma sim_future
      ths_src mem_k1_src mem_k2_src
      ths_tgt mem_k1_tgt mem_k2_tgt
      (SIM: sim ths_src mem_k1_src ths_tgt mem_k1_tgt)
      (FUTURE_SRC: Memory.future mem_k1_src mem_k2_src)
      (FUTURE_TGT: Memory.future mem_k1_tgt mem_k2_tgt):
  sim ths_src mem_k2_src ths_tgt mem_k2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma singleton_consistent
      tid lang st lc mem:
  Configuration.consistent (Configuration.mk (IdentMap.singleton tid (existT _ _ st, lc)) mem) <->
  <<WF: Local.wf lc mem>> /\
  <<CONSISTENT: Thread.consistent lang st lc mem>>.
Proof.
  econs; intro X.
  - inv X. ss.
    exploit THREADS; eauto. apply IdentMap.singleton_find.
  - des. econs; ss.
    + ii.
      apply IdentMap.singleton_find_inv in TH1.
      apply IdentMap.singleton_find_inv in TH2.
      des. Configuration.simplify. congruence.
    + ii. apply IdentMap.singleton_find_inv in TH. des.
      Configuration.simplify.
    + apply WF.
Qed.

Lemma singleton_is_terminal
      tid lang st lc:
  Threads.is_terminal (IdentMap.singleton tid (existT _ _ st, lc)) <->
  <<STATE: lang.(Language.is_terminal) st>> /\
  <<THREAD: Local.is_terminal lc>>.
Proof.
  econs; intro X.
  - eapply X. apply IdentMap.singleton_find.
  - ii. apply IdentMap.singleton_find_inv in FIND. i. des.
    Configuration.simplify.
Qed.

Lemma sim_step
      lang_src lang_tgt
      sim_terminal
      e
      st1_src lc1_src mem1_src
      st1_tgt lc1_tgt mem1_tgt
      st3_tgt lc3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt e
                          (Thread.mk _ st1_tgt lc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt mem3_tgt))
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src mem1_src st1_tgt lc1_tgt mem1_tgt):
  exists st2_src lc2_src mem2_src st3_src lc3_src mem3_src,
    <<STEPS: rtc (@Thread.step lang_src None)
                 (Thread.mk _ st1_src lc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src mem2_src)>> /\
    <<STEP: Thread.step e
                        (Thread.mk _ st2_src lc2_src mem2_src)
                        (Thread.mk _ st3_src lc3_src mem3_src)>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src mem3_src st3_tgt lc3_tgt mem3_tgt>>.
Proof.
  exploit Thread.step_future; eauto. s. i. des.
  punfold SIM. exploit SIM; eauto; try reflexivity. i. des.
  exploit STEP0; eauto. i. des; [|done].
  exploit Thread.rtc_step_future; eauto. s. i. des.
  exploit Thread.step_future; eauto. s. i. des.
  eexists _, _, _, _, _, _. splits; eauto.
Qed.

Lemma sim_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.step lang_tgt None) e1_tgt e2_tgt)
      (MEMORY: sim_memory mem1_src e1_tgt.(Thread.memory))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf e1_tgt.(Thread.thread) e1_tgt.(Thread.memory))
      (SIM: sim_thread sim_terminal st1_src lc1_src mem1_src e1_tgt.(Thread.state) e1_tgt.(Thread.thread) e1_tgt.(Thread.memory)):
  exists st2_src lc2_src mem2_src,
    <<STEPS: rtc (@Thread.step lang_src None)
                 (Thread.mk _ st1_src lc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src mem2_src)>> /\
    <<MEMORY: sim_memory mem2_src e2_tgt.(Thread.memory)>> /\
    <<WF_SRC: Local.wf lc2_src mem2_src>> /\
    <<WF_TGT: Local.wf e2_tgt.(Thread.thread) e2_tgt.(Thread.memory)>> /\
    <<SIM: sim_thread sim_terminal st2_src lc2_src mem2_src e2_tgt.(Thread.state) e2_tgt.(Thread.thread) e2_tgt.(Thread.memory)>>.
Proof.
  revert st1_src lc1_src mem1_src MEMORY WF_SRC WF_TGT SIM.
  induction STEPS; i.
  { eexists _, _, _. splits; eauto. }
  destruct x, y. ss.
  exploit sim_step; eauto. i. des.
  exploit IHSTEPS; eauto. i. des.
  destruct z. ss.
  eexists _, _, _. splits; try apply MEMORY1; eauto.
  etrans; [eauto|]. econs 2; eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src mem_src
      st_tgt lc_tgt mem_tgt
      (SIM: sim_thread sim_terminal st_src lc_src mem_src st_tgt lc_tgt mem_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Thread.consistent lang_tgt st_tgt lc_tgt mem_tgt):
  Thread.consistent lang_src st_src lc_src mem_src.
Proof.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try reflexivity. i. des.
  ii. exploit FUTURE; eauto. i. des.
  exploit CONSISTENT; eauto; try reflexivity. i. des.
  exploit sim_rtc_step; try apply MEMORY0; eauto.
  { s. eapply sim_thread_future; eauto. }
  i. des. destruct e2. ss.
  punfold SIM0. exploit SIM0; eauto; try reflexivity. i. des.
  exploit PROMISES1; eauto. i. des.
  eexists (Thread.mk _ _ _ _). splits; [|eauto].
  etrans; eauto.
Qed.


Lemma sim_thread_sim
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src mem_k_src
      st1_tgt lc1_tgt mem_k_tgt
      tid
      (SIM: @sim_thread lang_src lang_tgt sim_terminal
                        st1_src lc1_src mem_k_src
                        st1_tgt lc1_tgt mem_k_tgt):
  sim
    (IdentMap.singleton tid (existT _ _ st1_src, lc1_src)) mem_k_src
    (IdentMap.singleton tid (existT _ _ st1_tgt, lc1_tgt)) mem_k_tgt.
Proof.
  revert st1_src lc1_src mem_k_src st1_tgt lc1_tgt mem_k_tgt SIM. pcofix CIH. i. pfold. ii.
  apply singleton_consistent in CONSISTENT_SRC.
  apply singleton_consistent in CONSISTENT_TGT.
  des. splits.
  - i. apply (singleton_is_terminal tid) in TERMINAL_TGT. des.
    punfold SIM0. exploit SIM0; eauto. i. des.
    exploit TERMINAL; eauto. i. des.
    eexists _, _. splits; [|eauto|].
    + generalize (rtc_tail STEPS). intro X. des.
      * destruct a2. econs 2; [|econs 1].
        econs; ss; eauto.
        { eapply IdentMap.singleton_find. }
        { ii. eexists. splits; eauto. ss.
          inv LOCAL. apply MemInv.sem_bot_inv in PROMISES0. etrans; eauto.
          apply THREAD.
        }
      * inv X. s. erewrite IdentMap.singleton_add. econs.
    + ii. ss. rewrite IdentMap.singleton_add in *.
      apply IdentMap.singleton_find_inv in FIND. des. subst.
      splits; Configuration.simplify. econs; eauto.
      inv LOCAL. apply MemInv.sem_bot_inv in PROMISES0. etrans; eauto.
      apply THREAD.
  - i. inv STEP_TGT. ss.
    apply IdentMap.singleton_find_inv in TID. des.
    Configuration.simplify.
    exploit sim_rtc_step; eauto.
    { eapply sim_thread_future; eauto. }
    i. des. destruct e2. ss.
    exploit sim_step; try apply MEMORY; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
    + econs; s.
      * apply IdentMap.singleton_find.
      * etrans; eauto.
      * eauto.
      * eapply sim_thread_consistent; eauto.
    + right. s. rewrite ? IdentMap.singleton_add.
      apply CIH. ss.
Qed.
