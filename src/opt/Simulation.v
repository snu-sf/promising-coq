Require Import sflib.
From Paco Require Import paco.

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

Set Implicit Arguments.


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
          <<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>> /\
          <<SC: TimeMap.le sc2_src sc1_tgt>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: Threads.is_terminal ths2_src>>>> /\
      <<STEP:
        forall e tid_tgt ths3_tgt sc3_tgt mem3_tgt
          (STEP_TGT: Configuration.step e tid_tgt (Configuration.mk ths1_tgt sc1_tgt mem1_tgt) (Configuration.mk ths3_tgt sc3_tgt mem3_tgt)),
        exists tid_src ths2_src sc2_src mem2_src ths3_src sc3_src mem3_src,
          <<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>> /\
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
