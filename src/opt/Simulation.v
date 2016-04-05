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


Definition SIM_THREAD :=
  forall (th1_src:Thread.t) (mem_k_src:Memory.t)
    (th1_tgt:Thread.t) (mem_k_tgt:Memory.t), Prop.

Definition sim_interference
           (th1_src:Thread.t) (mem_k_src:Memory.t)
           (th1_tgt:Thread.t) (mem_k_tgt:Memory.t): Prop :=
  forall mem1_src mem1_tgt
    (MEMORY1: sim_memory mem1_src mem1_tgt)
    (LOCAL_SRC: Memory.le th1_src.(Thread.local) mem1_src)
    (LOCAL_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
    <<TERMINAL:
      forall (TERMINAL_TGT: Thread.is_terminal th1_tgt),
      exists th2_src mem2_src,
        <<STEPS: rtc Thread.internal_step (th1_src, mem1_src) (th2_src, mem2_src)>> /\
        <<TERMINAL_SRC: Thread.is_terminal th2_src>>>> /\
    <<DECLARE:
      forall (TERMINAL_TGT: th1_tgt.(Thread.local) = Memory.init),
      exists th2_src mem2_src,
        <<STEPS: rtc Thread.internal_step (th1_src, mem1_src) (th2_src, mem2_src)>> /\
        <<TERMINAL_SRC: th2_src.(Thread.local) = Memory.init>>>>.

(* TODO: inftau & liveness *)
Definition _sim_thread_step
           (sim_thread: SIM_THREAD)
           (th1_src:Thread.t) (mem_k_src:Memory.t)
           (th1_tgt:Thread.t) (mem_k_tgt:Memory.t): Prop :=
  forall mem1_src mem1_tgt
    (MEMORY1: sim_memory mem1_src mem1_tgt)
    (LOCAL_SRC: Memory.le th1_src.(Thread.local) mem1_src)
    (LOCAL_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
  forall e th2_tgt mem2_tgt
    (STEP_TGT: Thread.step e th1_tgt mem1_tgt th2_tgt mem2_tgt),
  exists th2_src mem2_src,
    <<STEP_SRC: Thread.step e th1_src mem1_src th2_src mem2_src>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>> /\
    <<SIM: sim_thread th2_src mem2_src th2_tgt mem2_tgt>>.

Lemma _sim_thread_step_mon: monotone4 _sim_thread_step.
Proof.
  ii. exploit IN; eauto. i. des.
  eexists _, _. splits; eauto.
Qed.
Hint Resolve _sim_thread_step_mon: paco.

Definition _sim_thread R := sim_interference /4\ _sim_thread_step R.
Lemma _sim_thread_mon: monotone4 _sim_thread.
Proof.
  ii. unfold _sim_thread in IN. des.
  split; auto. eapply _sim_thread_step_mon; eauto.
Qed.
Hint Resolve _sim_thread_mon: paco.

Definition sim_thread: SIM_THREAD := paco4 _sim_thread bot4.
