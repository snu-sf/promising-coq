Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Program.
Require Import Memory.

Set Implicit Arguments.

Module Configuration.
  Structure t := mk {
    clocks: Clocks.t;
    program: Program.t;
    memory: Memory.t;
  }.

  Definition load (s:Program.syntax): Configuration.t :=
    Configuration.mk
      Clocks.init
      (Program.load s)
      (Memory.init s).

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (PROGRAM: Program.is_terminal c.(program))
  .

  Inductive internal_step: forall (c1:t) (c2:t), Prop :=
  | step_tau
      c th1 th2 i m
      (PROGRAM: Program.step th1 i None th2):
      internal_step (mk c th1 m) (mk c th2 m)
  | step_mem
      i e
      c th1 th2 m1 m2
      (PROGRAM: Program.step th1 i (Some (ThreadEvent.mem e)) th2)
      (MEMORY: Memory.step c m1 i e m2)
      (CONSISTENT: Memory.consistent m2):
      internal_step (mk c th1 m1) (mk c th2 m2)
  | step_inception
      c th m1 m2 event ts loc val i n ths
      (STEPS: internal_steps (mk c th m1) (mk c th m2))
      (INCEPTIONS: InceptionSet.Empty m2.(Memory.inceptions))
      (WRITING: RWEvent.is_writing event = Some (loc, val))
      (UPDATE:
         forall loc valr valw ord (EVENT: event = RWEvent.update loc valr valw ord),
         exists event0 ts0 pos0 val0,
           <<IN0: Memory.In m1 (Message.rw event0 ts0) pos0>> /\
           <<TS0: ts0 + 1 = ts>> /\
           <<EVENT0: RWEvent.is_writing event0 = Some (loc, val0)>>)
      (MESSAGE: Memory.In m2 (Message.rw event ts) (Memory.Position.buffer i n))
      (PROGRAM: IdentSet.mem i ths):
      internal_step (mk c th m1)
                    (mk c th (Memory.mk m1.(Memory.buffers) (InceptionSet.add (Inception.mk (Message.rw event ts) ths) m1.(Memory.inceptions))))
  | step_confirm
      c th1 th2 m1 inceptions2
      i e ts ths b
      (PROGRAM: Program.step th1 i (Some (ThreadEvent.mem (ThreadEvent.rw e))) th2)
      (INCEPTIONS: InceptionSet.remove_if_exists (Inception.mk (Message.rw e ts) ths) m1.(Memory.inceptions) = Some inceptions2)
      (THS: IdentSet.mem i ths)
      (BUFFER: IdentMap.find i c.(memory).(Memory.buffers) = Some b):
      internal_step c
                    (mk c.(clocks) c.(program)
                        (Memory.mk (IdentMap.add i (b ++ [Message.rw e ts]) c.(memory).(Memory.buffers)) inceptions2))

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
      (FEASIBLE: feasible c2):
      step c1 None c2
  | step_commit
      c1 th m c2
      (MEMORY: InceptionSet.Empty m.(Memory.inceptions))
      (CLOCKS: Clocks.le c1 c2)
      (CONSISTENT: Memory.consistent m)
      (FEASIBLE: feasible (mk c2 th m)):
      step (mk c1 th m) None (mk c2 th m)
  | step_syscall
      c th1 m i e th2
      (PROGRAM: Program.step th1 i (Some (ThreadEvent.syscall e)) th2)
      (FEASIBLE: feasible (mk c th2 m)):
      step (mk c th1 m) (Some e) (mk c th2 m)
  .
End Configuration.
