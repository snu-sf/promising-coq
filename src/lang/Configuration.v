Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Program.
Require Import Memory.

Set Implicit Arguments.

Module Configuration.
  Structure t := mk {
    clock: Clock.t;
    program: Program.t;
    memory: Memory.t;
  }.

  Definition load (s:Program.syntax): Configuration.t :=
    Configuration.mk
      Clock.init
      (Program.load s)
      (Memory.init s).

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (PROGRAM: Program.is_terminal c.(program))
  .

  Inductive internal_step: forall (c1 c2:t), Prop :=
  | step_tau
      c th1 th2 i m
      (PROGRAM: Program.step th1 i None th2):
      internal_step (mk c th1 m) (mk c th2 m)
  | step_mem
      i e
      c1 c2 th1 th2 m1 m2
      (PROGRAM: Program.step th1 i (Some (ThreadEvent.mem e)) th2)
      (MEMORY: Memory.step c1 m1 i e c2 m2):
      internal_step (mk c1 th1 m1) (mk c2 th2 m2)
  | step_inception
      c1 c2 th1 th2 m1 m2 inception
      (STEPS: internal_steps (mk c1 th1 m1) (mk c2 th2 m2))
      (INCEPTION: Memory.inception m2 inception)
      (CONSISTENT: Memory.consistent (Memory.mk m1.(Memory.buffers) (InceptionSet.add inception m1.(Memory.inceptions)))):
      internal_step (mk c1 th1 m1)
                    (mk c1 th1 (Memory.mk m1.(Memory.buffers) (InceptionSet.add inception m1.(Memory.inceptions))))
  | step_commit
      c1 th m c2
      (CLOCK: Clock.le c1 c2):
      internal_step (mk c1 th m)
                    (mk c2 th m)

  with internal_steps: forall (c1 c2:t), Prop :=
  | steps_nil c:
      internal_steps c c
  | steps_cons
      c1 c2 c3
      (STEP: internal_step c1 c2)
      (STEPS: internal_steps c2 c3):
      internal_steps c1 c3
  .

  Inductive feasible (c:t): Prop :=
  | feasible_intro
      c'
      (STEP: internal_steps c c')
      (INCEPTIONS: InceptionSet.Empty c'.(memory).(Memory.inceptions))
  .

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_internal
      c1 c2
      (STEP: internal_step c1 c2)
      (CONSISTENT: Memory.consistent c2.(memory))
      (FEASIBLE: feasible c2):
      step c1 None c2
  | step_syscall
      c th1 m i e th2
      (PROGRAM: Program.step th1 i (Some (ThreadEvent.syscall e)) th2)
      (FEASIBLE: feasible (mk c th2 m)):
      step (mk c th1 m) (Some e) (mk c th2 m)
  .
End Configuration.
