Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Program.
Require Import Memory.

Set Implicit Arguments.

Module Configuration.
  Structure t := mk {
    program: Program.t;
    memory: Memory.t;
  }.

  Definition init (s:Program.syntax): Configuration.t :=
    Configuration.mk
      (Program.init s)
      Memory.init.

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (PROGRAM: Program.is_terminal c.(program))
  .

  Inductive base_step (tid:Ident.t): forall (c1 c2:t), Prop :=
  | step_mem
      e
      th1 th2 m1 m2
      (PROGRAM: Program.step tid th1 (option_map ThreadEvent.mem e) th2)
      (MEMORY: Memory.step tid m1 e m2):
      base_step tid (mk th1 m1) (mk th2 m2)
  | step_commit
      th1 messages1 threads1 threads2
      (THREADS: forall i, Thread.le (IdentFun.find i threads1) (IdentFun.find i threads2)):
      base_step tid
                (mk th1 (Memory.mk messages1 threads1))
                (mk th1 (Memory.mk messages1 threads2))
  .

  Inductive internal_step: forall (threads:IdentSet.t) (c1 c2:t), Prop :=
  | step_base
      threads tid c1 c2
      (TID: IdentSet.In tid threads)
      (BASE: base_step tid c1 c2):
      internal_step threads c1 c2
  | step_declare
      threads threads' tid
      c1 c1'
      loc ts val released
      (THREADS: IdentSet.Subset threads' threads)
      (STEPS: internal_steps threads' c1 c1')
      (GET: Messages.get loc ts c1'.(memory).(Memory.messages) = None)
      (GET': Messages.get loc ts c1'.(memory).(Memory.messages) = Some (Message.mk val released None)):
      internal_step
        threads
        c1
        (mk
           c1.(program)
           (Memory.mk
              (Messages.add tid loc ts (Message.mk val released (Some threads')) c1.(memory).(Memory.messages))
              c1.(memory).(Memory.threads)))

  with internal_steps: forall (threads:IdentSet.t) (c1 c2:t), Prop :=
  | steps_nil
      threads c:
      internal_steps threads c c
  | steps_cons
      threads c1 c2 c3
      (STEP: internal_step threads c1 c2)
      (STEPS: internal_steps threads c2 c3):
      internal_steps threads c1 c3
  .

  Lemma internal_step_congr
        threads1 threads2
        c1 c2
        (THREADS: IdentSet.Subset threads1 threads2)
        (STEP: internal_step threads1 c1 c2):
    internal_step threads2 c1 c2
  with internal_steps_congr
         threads1 threads2
         c1 c2
         (THREADS: IdentSet.Subset threads1 threads2)
         (STEP: internal_steps threads1 c1 c2):
         internal_steps threads2 c1 c2.
  Proof.
    - inv STEP.
      + econs 1; eauto.
      + econs 2; eauto.
        etransitivity; eauto.
    - inv STEP.
      + econs 1.
      + econs 2; eauto.
  Qed.

  Lemma internal_steps_append
        threads c1 c2 c3
        (STEPS12: internal_steps threads c1 c2)
        (STEPS23: internal_steps threads c2 c3):
    internal_steps threads c1 c3.
  Proof.
    revert STEPS23. induction STEPS12; auto.
    i. econs; eauto.
  Qed.

  Inductive feasible (c:t): Prop :=
  | feasible_intro
      threads c'
      (STEP: internal_steps threads c c')
      (NODECLARE: ~ Messages.is_declared c'.(memory).(Memory.messages))
  .

  Inductive external_step: forall (c1:t) (e:Event.t) (c2:t), Prop :=
  | step_syscall
      tid th1 e th2 m
      (PROGRAM: Program.step tid th1 (Some (ThreadEvent.syscall e)) th2):
      external_step (mk th1 m) e (mk th2 m)
  .

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_internal
      threads c1 c2
      (STEP: internal_step threads c1 c2)
      (FEASIBLE: feasible c2):
      step c1 None c2
  | step_external
      c1 c2
      e
      (STEP: external_step c1 e c2)
      (FEASIBLE: feasible c2):
      step c1 (Some e) c2
  .
End Configuration.
