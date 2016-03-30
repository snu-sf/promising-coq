Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Thread.
Require Import Memory.

Set Implicit Arguments.


Module Context.
  Structure t := mk {
    thread: Thread.t;
    local: ThreadLocal.t;
    memory: Memory.t;
  }.

  Inductive step (ctx1:t): forall (ctx2:t), Prop :=
  | step_thread
      e th2 thl2
      (THREAD: Thread.step ctx1.(thread) (option_map ThreadEvent.mem e) th2)
      (MEM: Memory.step ctx1.(local) ctx1.(memory) e thl2):
      step ctx1 (mk th2 thl2 ctx1.(memory))
  | step_declare
      thl2 mem2
      (MEM: Memory.declare ctx1.(local) ctx1.(memory) thl2 mem2):
      step ctx1 (mk ctx1.(thread) thl2 mem2)
  .
End Context.

Module Configuration.
  Definition syntax := IdentMap.t Thread.syntax.

  Structure t := mk {
    threads: IdentMap.t (Thread.t * ThreadLocal.t);
    memory: Memory.t;
  }.

  Definition init (s:syntax): t :=
    mk (IdentMap.map (fun th => (Thread.init th, ThreadLocal.init)) s)
       Memory.init.

  Definition is_terminal (conf:t): Prop :=
    forall tid th thl (FIND: IdentMap.find tid conf.(threads) = Some (th, thl)),
      Thread.is_terminal th.

  Inductive internal_step (c1:t): forall (c2:t), Prop :=
  | internal_step_intro
      tid th1 thl1 th2 thl2 memory2
      (FIND: IdentMap.find tid c1.(threads) = Some (th1, thl1))
      (STEP: tc Context.step (Context.mk th1 thl1 c1.(memory)) (Context.mk th2 thl2 memory2)):
      internal_step c1 (mk (IdentMap.add tid (th2, thl2) c1.(threads)) memory2)
  .

  Inductive external_step (c1:t): forall (e:Event.t) (c2:t), Prop :=
  | external_step_intro
      tid th1 thl1 th2 thl2 e
      (FIND: IdentMap.find tid c1.(threads) = Some (th1, thl1))
      (NODECLARE: thl1.(ThreadLocal.declares) = DeclareSet.empty)
      (THREAD: Thread.step th1 (Some (ThreadEvent.syscall e)) th2):
      external_step
        c1 e
        (mk (IdentMap.add tid (th2, thl2) c1.(threads)) c1.(memory))
  .

  Definition consistent (conf:t): Prop :=
    forall tid th1 thl1 mem1
      (FIND: IdentMap.find tid conf.(threads) = Some (th1, thl1))
      (FUTURE: Memory.future thl1.(ThreadLocal.declares) conf.(memory) mem1),
    exists th2 thl2 mem2,
      <<STEPS: rtc Context.step (Context.mk th1 thl1 mem1) (Context.mk th2 thl2 mem2)>> /\
      <<NODECLARE: thl2.(ThreadLocal.declares) = DeclareSet.empty>>.

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_internal
      c1 c2
      (STEP: internal_step c1 c2)
      (CONSISTENT: consistent c2):
      step c1 None c2
  | step_external
      c1 c2
      e
      (STEP: external_step c1 e c2)
      (CONSISTENT: consistent c2):
      step c1 (Some e) c2
  .
End Configuration.
