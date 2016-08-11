Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.

Set Implicit Arguments.


Section SimulationLocal.
  Variable (lang_src lang_tgt:Language.t).

  Definition SIM_TERMINAL :=
    forall (st_src:lang_src.(Language.state)) (st_tgt:lang_tgt.(Language.state)), Prop.

  Definition SIM_THREAD :=
    forall (sim_terminal: SIM_TERMINAL)
      (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (sim_thread: forall (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                            (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt
    :=
    forall pf_tgt e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP_TGT: Thread.step pf_tgt e_tgt
                             (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)),
    exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
      <<STEPS: rtc (@Thread.tau_step _)
                   (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                   (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
      <<STEP_SRC: Thread.opt_step e_src
                                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                  (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
      <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
      <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
      <<MEMORY3: sim_memory mem3_src mem3_tgt>> /\
      <<SIM: sim_thread st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: SIM_TERMINAL)
             (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall sc1_src mem1_src
      sc1_tgt mem1_tgt
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
      (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
      (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
      (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st1_tgt),
        exists st2_src lc2_src sc2_src mem2_src,
          <<STEPS: rtc (@Thread.tau_step _)
                       (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
          <<SC: TimeMap.le sc2_src sc1_tgt>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: lang_src.(Language.is_terminal) st2_src>> /\
          <<LOCAL: sim_local lc2_src lc1_tgt>> /\
          <<TERMINAL: sim_terminal st2_src st1_tgt>>>> /\
      <<FUTURE:
        forall sc2_src mem2_src
          (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
          (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
          (WF_SRC: Local.wf lc1_src mem2_src)
          (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
          (MEM_SRC: Memory.closed mem2_src),
        exists sc2_tgt mem2_tgt,
          <<SC: TimeMap.le sc2_src sc2_tgt>> /\
          <<MEMORY: sim_memory mem2_src mem2_tgt>> /\
          <<SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt>> /\
          <<MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
          <<WF_TGT: Local.wf lc1_tgt mem2_tgt>> /\
          <<SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt>> /\
          <<MEM_TGT: Memory.closed mem2_tgt>>>> /\
      <<PROMISES:
        forall (PROMISES_TGT: lc1_tgt.(Local.promises) = Memory.bot),
        exists st2_src lc2_src sc2_src mem2_src,
          <<STEPS: rtc (@Thread.tau_step _)
                       (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
          <<PROMISES_SRC: lc2_src.(Local.promises) = Memory.bot>>>> /\
      <<STEP: _sim_thread_step (sim_thread sim_terminal)
                               st1_src lc1_src sc1_src mem1_src
                               st1_tgt lc1_tgt sc1_tgt mem1_tgt>>.

  Lemma _sim_thread_mon: monotone9 _sim_thread.
  Proof.
    ii. exploit IN; try apply SC; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco9 _sim_thread bot9.

  Lemma sim_thread_mon
        sim_terminal1 sim_terminal2
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <8= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; try apply SC; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des.
      esplits; eauto.
    - ii. exploit STEP; eauto. i. des. inv SIM0; [|done].
      esplits; eauto.
  Qed.
End SimulationLocal.
Hint Resolve _sim_thread_mon: paco.


Section Simulation.
  Definition SIM :=
    forall (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim
             (sim: SIM)
             (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall sc1_src mem1_src
      sc1_tgt mem1_tgt
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths1_tgt sc1_tgt mem1_tgt))
      (CONSISTENT_SRC: Configuration.consistent (Configuration.mk ths1_src sc1_src mem1_src))
      (CONSISTENT_TGT: Configuration.consistent (Configuration.mk ths1_tgt sc1_tgt mem1_tgt))
      (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
      (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
      (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
      (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
        exists ths2_src sc2_src mem2_src,
          <<STEPS: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>> /\
          <<SC: TimeMap.le sc2_src sc1_tgt>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: Threads.is_terminal ths2_src>>>> /\
      <<STEP:
        forall e tid_tgt ths3_tgt sc3_tgt mem3_tgt
          (STEP_TGT: Configuration.step e tid_tgt (Configuration.mk ths1_tgt sc1_tgt mem1_tgt) (Configuration.mk ths3_tgt sc3_tgt mem3_tgt)),
        exists tid_src ths2_src sc2_src mem2_src ths3_src sc3_src mem3_src,
          <<STEPS: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>> /\
          <<STEP_SRC: Configuration.opt_step e tid_src (Configuration.mk ths2_src sc2_src mem2_src) (Configuration.mk ths3_src sc3_src mem3_src)>> /\
          <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
          <<MEMORY3: sim_memory mem3_src mem3_tgt>> /\
          <<SIM: sim ths3_src sc3_src mem3_src ths3_tgt sc3_tgt mem3_tgt>>>>.

  Lemma _sim_mon: monotone6 _sim.
  Proof.
    ii. exploit IN; try apply SC1; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco6 _sim bot6.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt):
  sim_thread sim_terminal st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.


Lemma sim_future
      ths_src sc1_src sc2_src mem1_src mem2_src
      ths_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      (SIM: sim ths_src sc1_src mem1_src ths_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt):
  sim ths_src sc2_src mem2_src ths_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.

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
      des. Configuration.simplify. congr.
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

Lemma sim_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  punfold SIM. exploit SIM; eauto; try refl. i. des.
  exploit Thread.step_future; eauto. s. i. des.
  exploit STEP0; eauto. i. des. inv SIM0; [|done].
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit Thread.opt_step_future; eauto. s. i. des.
  esplits; eauto.
Qed.

Lemma sim_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  inv STEP.
  - esplits; eauto. econs 1.
  - eapply sim_step; eauto.
Qed.

Lemma sim_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (SC: TimeMap.le sc1_src e1_tgt.(Thread.sc))
      (MEMORY: sim_memory mem1_src e1_tgt.(Thread.memory))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed e1_tgt.(Thread.memory))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src e1_tgt.(Thread.state) e1_tgt.(Thread.local) e1_tgt.(Thread.sc) e1_tgt.(Thread.memory)):
  exists st2_src lc2_src sc2_src mem2_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<SC: TimeMap.le sc2_src e2_tgt.(Thread.sc)>> /\
    <<MEMORY: sim_memory mem2_src e2_tgt.(Thread.memory)>> /\
    <<WF_SRC: Local.wf lc2_src mem2_src>> /\
    <<WF_TGT: Local.wf e2_tgt.(Thread.local) e2_tgt.(Thread.memory)>> /\
    <<SC_SRC: Memory.closed_timemap sc2_src mem2_src>> /\
    <<SC_TGT: Memory.closed_timemap e2_tgt.(Thread.sc) e2_tgt.(Thread.memory)>> /\
    <<MEM_SRC: Memory.closed mem2_src>> /\
    <<MEM_TGT: Memory.closed e2_tgt.(Thread.memory)>> /\
    <<SIM: sim_thread sim_terminal st2_src lc2_src sc2_src mem2_src e2_tgt.(Thread.state) e2_tgt.(Thread.local) e2_tgt.(Thread.sc) e2_tgt.(Thread.memory)>>.
Proof.
  revert SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT SIM.
  revert st1_src lc1_src sc1_src mem1_src.
  induction STEPS; i.
  { esplits; eauto. }
  inv H. inv TSTEP. destruct x, y. ss.
  exploit sim_step; eauto. i. des.
  exploit IHSTEPS; eauto. i. des.
  destruct z. ss.
  esplits; try apply MEMORY1; eauto.
  etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
  econs 2; eauto. econs.
  - econs. eauto.
  - etrans; eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: sim_thread sim_terminal st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try refl. i. des.
  ii. ss. exploit FUTURE; eauto. i. des.
  exploit CONSISTENT; eauto; try refl. i. des.
  exploit sim_rtc_step; try apply MEMORY0; try apply SC0; eauto.
  { s. eapply sim_thread_future; eauto. }
  i. des. destruct e2. ss.
  punfold SIM0. exploit SIM0; eauto; try refl. i. des.
  exploit PROMISES1; eauto. i. des.
  eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
  etrans; eauto.
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
    punfold SIM0. exploit SIM0; try apply SC1; eauto. i. des.
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
    exploit sim_rtc_step; try apply STEPS; try apply SC1; eauto.
    { eapply sim_thread_future; eauto. }
    i. des. destruct e2. ss.
    exploit sim_opt_step; try apply MEMORY; eauto.
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
