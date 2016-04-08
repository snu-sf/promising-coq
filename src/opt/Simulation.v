Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (MESSAGES:
       forall loc ts msg
         (MSG: Memory.get loc ts mem_tgt = Some msg),
         Memory.get loc ts mem_src = Some msg)
    (OWNERSHIP: Memory.own mem_src = Memory.own mem_tgt)
.


Section SimulationThread.
  Variable (lang:Language.t).

  Definition SIM_THREAD :=
    forall (sim_terminal: forall (th_src th_tgt:Thread.t lang), Prop)
      (th1_src:Thread.t lang) (mem_k_src:Memory.t)
      (th1_tgt:Thread.t lang) (mem_k_tgt:Memory.t), Prop.

  (* TODO: inftau & liveness *)
  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: forall (th_src th_tgt:Thread.t lang), Prop)
             (th1_src:Thread.t lang) (mem_k_src:Memory.t)
             (th1_tgt:Thread.t lang) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (LOCAL_SRC: Memory.le th1_src.(Thread.local) mem1_src)
      (LOCAL_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: lang.(Language.is_terminal) th1_tgt.(Thread.state)),
        exists th2_src mem2_src,
          <<STEPS: rtc (@Thread.internal_step lang) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: lang.(Language.is_terminal) th2_src.(Thread.state)>> /\
          <<DECLARE: th2_src.(Thread.local) = th1_tgt.(Thread.local)>> /\
          <<SIM: sim_terminal th2_src th1_tgt>>>> /\
      <<DECLARE:
        forall (DECLARE_TGT: th1_tgt.(Thread.local) = Memory.init),
        exists th2_src mem2_src,
          <<STEPS: rtc (@Thread.internal_step lang) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<DECLARE_SRC: th2_src.(Thread.local) = Memory.init>>>> /\
      <<STEP:
        forall e th3_tgt mem3_tgt
          (STEP_TGT: Thread.step e th1_tgt mem1_tgt th3_tgt mem3_tgt),
        exists th2_src mem2_src th3_src mem3_src,
          <<STEPS: rtc (@Thread.internal_step lang) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<STEP_SRC: Thread.step e th2_src mem2_src th3_src mem3_src>> /\
          <<MEMORY2: sim_memory mem3_src mem3_tgt>> /\
          <<SIM: sim_thread sim_terminal th3_src mem3_src th3_tgt mem3_tgt>>>>.

  Lemma _sim_thread_mon: monotone5 _sim_thread.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco5 _sim_thread bot5.
End SimulationThread.
Hint Resolve _sim_thread_mon: paco.


Section Simulation.
  Definition SIM :=
    forall (th1_src:Threads.t) (mem_k_src:Memory.t)
      (th1_tgt:Threads.t) (mem_k_tgt:Memory.t), Prop.

  (* TODO: inftau & liveness *)
  Definition _sim
             (sim: SIM)
             (ths1_src:Threads.t) (mem_k_src:Memory.t)
             (ths1_tgt:Threads.t) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (LOCAL_SRC: Threads.le ths1_src mem1_src)
      (LOCAL_TGT: Threads.le ths1_tgt mem1_tgt)
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
        exists ths2_src mem2_src,
          <<STEPS: rtc (Configuration.step None) (Configuration.mk ths1_src mem1_src) (Configuration.mk ths2_src mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: Threads.is_terminal ths2_src>>>> /\
      <<CONSISTENT:
        forall (CONSISTENT_TGT: Configuration.consistent (Configuration.mk ths1_tgt mem1_tgt)),
        <<CONSISTENT_SRC: Configuration.consistent (Configuration.mk ths1_src mem1_src)>>>> /\
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


Lemma sim_thread_sim
      lang sim_terminal th1_src mem_k_src th1_tgt mem_k_tgt tid
      (SIM: @sim_thread lang sim_terminal th1_src mem_k_src th1_tgt mem_k_tgt):
  sim
    (Threads.singleton tid th1_src) mem_k_src
    (Threads.singleton tid th1_tgt) mem_k_tgt.
Proof.
  revert th1_src mem_k_src th1_tgt mem_k_tgt SIM. pcofix CIH. i.
  punfold SIM0. pfold. ii.
  exploit SIM0; eauto.
  { eapply LOCAL_SRC.
    unfold Threads.singleton. rewrite IdentMap.Facts.add_eq_o; eauto.
  }
  { eapply LOCAL_TGT.
    unfold Threads.singleton. rewrite IdentMap.Facts.add_eq_o; eauto.
  }
  i. des. splits.
  - i. exploit TERMINAL; eauto.
    { admit. }
    i. des.
    admit.
  - admit.
  - admit.
Admitted.
