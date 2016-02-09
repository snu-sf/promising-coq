Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Memory.

Module Configuration.
  Structure t := mk {
    clocks: Clocks.t;
    threads: Threads.t;
    memory: Memory.t;
    stack: list (Threads.t * Memory.t);
  }.

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (STACK: c.(stack) = nil)
      (THREADS:
         forall i th (THREAD: Ident.Map.find i c.(threads) = Some th),
           Thread.is_terminal th)
  .

  Inductive is_observable (c:t): Prop :=
  | is_observable_intro
      (STACK: c.(stack) = nil)
      (MEMORY: forall i, MessageSet.Empty (Ident.Fun.find i c.(memory)).(Buffer.inception))
  .

  Inductive step: forall (c1 c2:t), Prop :=
  | step_event
      i e
      c p1 p2 m1 m2 stack
      (THREADS: Threads.step p1 i e p2)
      (MEMORY: Memory.step c m1 i e m2)
      (CONSISTENT: Memory.consistent m2):
      step (mk c p1 m1 stack) (mk c p2 m2 stack)
  | step_dream
      c p m stack:
      step (mk c p m stack) (mk c p m ((p, m)::stack))
  | step_inception
      c p m p' m' stack
      event ts loc val
      ts' position i
      (WRITING: RWEvent.is_writing event = Some (loc, val))
      (UPDATE:
         forall loc valr valw ord (EVENT: event = RWEvent.update loc valr valw ord),
         exists event' ts' pos' val',
           <<IN: Memory.In m' (Message.rw event' ts') pos'>> /\
           <<TS: ts' + 1 = ts>> /\
           <<EVENT': RWEvent.is_writing event' = Some (loc, val')>>)
      (MESSAGE: Memory.In m (Message.rw event ts) position)
      (POSITION: Memory.Position.is_inception position = false)
      (INCEPTION:
         forall i,
           MessageSet.Subset
             (Ident.Fun.find i m).(Buffer.inception)
             (Ident.Fun.find i m').(Buffer.inception)):
      step
        (mk c p m ((p', m')::stack))
        (mk c
            p'
            (Ident.Fun.add i (Buffer.add_inception (Message.rw event ts') (Ident.Fun.find i m')) m')
            stack)
  | step_commit
      c p m c'
      (MEMORY: forall i, MessageSet.Empty (Ident.Fun.find i m).(Buffer.inception))
      (CLOCKS: Clocks.le c c'):
      step
        (mk c p m nil)
        (mk c' p m nil)
  .
End Configuration.
