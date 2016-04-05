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


(* TODO: inftau & liveness *)
Inductive _sim_thread
          (sim_thread: forall (th1_src:Thread.t) (mem_k_src:Memory.t)
                         (th1_tgt:Thread.t) (mem_k_tgt:Memory.t), Prop)
          (th1_src:Thread.t) (mem_k_src:Memory.t)
          (th1_tgt:Thread.t) (mem_k_tgt:Memory.t): Prop :=
| sim_thread_terminal
    (TGT: Thread.is_terminal th1_tgt)
    (SRC: forall mem1_src
            (LOCAL: Memory.le th1_src.(Thread.local) mem1_src)
            (FUTURE: Memory.future mem_k_src mem1_src),
        exists th2_src mem2_src,
          <<STEPS: rtc Thread.internal_step (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<TERMINAL: Thread.is_terminal th2_src>>)
| sim_thread_step
    (STEP:
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
         <<SIM: sim_thread th2_src mem2_src th2_tgt mem2_tgt>>)
.
Hint Constructors _sim_thread.

Lemma _sim_thread_mon: monotone4 _sim_thread.
Proof.
  repeat intro; inv IN.
  - econs 1; eauto.
  - econs 2. i.
    exploit STEP; eauto. i. des.
    eexists _, _. splits; eauto.
Qed.
Hint Resolve _sim_thread_mon: paco.

Definition sim_thread: _ -> _ -> _ -> _ -> Prop := paco4 _sim_thread bot4.

Definition sim_thread_init s1 s2 :=
  sim_thread (Thread.init s1) Memory.init
             (Thread.init s2) Memory.init.
