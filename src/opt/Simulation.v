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
