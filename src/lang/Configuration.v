Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Thread.

Set Implicit Arguments.


Module Threads.
  Definition syntax := IdentMap.t {lang:Language.t & lang.(Language.syntax)}.
  Definition t := IdentMap.t {lang:Language.t & Thread.t lang}.

  Definition init (s:syntax): t :=
    IdentMap.map (fun s => existT _ _ (Thread.init _ s.(projT2))) s.

  Definition singleton tid lang th: t :=
    IdentMap.add tid (existT _ lang th) (IdentMap.empty _).

  Definition is_terminal (ths:t): Prop :=
    forall tid lang th (FIND: IdentMap.find tid ths = Some (existT _ lang th)),
      Thread.is_terminal th.

  Definition wf (ths:t): Prop :=
    forall tid1 lang1 th1
      tid2 lang2 th2
      (TID: tid1 <> tid2)
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 th1))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 th2)),
      Memory.disjoint th1.(Thread.local) th2.(Thread.local).

  Definition disjoint (ths1 ths2:t): Prop :=
    forall tid1 lang1 th1
      tid2 lang2 th2
      (TH1: IdentMap.find tid1 ths1 = Some (existT _ lang1 th1))
      (TH2: IdentMap.find tid2 ths2 = Some (existT _ lang2 th2)),
      Memory.disjoint th1.(Thread.local) th2.(Thread.local).

  Definition le (ths:t) (mem:Memory.t): Prop :=
    forall tid lang th
      (TH: IdentMap.find tid ths = Some (existT _ lang th)),
      Memory.le th.(Thread.local) mem.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) Memory.init.
  Definition is_terminal (conf:t): Prop := Threads.is_terminal conf.(threads).

  Inductive step (e:option Event.t) (c1:t): forall (c2:t), Prop :=
  | step_intro
      tid lang th1 th2 memory2 th3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some (existT _ lang th1))
      (STEPS: rtc (@Thread.internal_step lang) (th1, c1.(memory)) (th2, memory2))
      (STEP: Thread.step e th2 memory2 th3 memory3)
      (CONSISTENT: Thread.consistent th3 memory3):
      step e c1 (mk (IdentMap.add tid (existT _ _ th3) c1.(threads)) memory3)
  .

  Definition consistent (conf:t): Prop :=
    forall tid lang th1 mem1
      (FIND: IdentMap.find tid conf.(threads) = Some (existT _ lang th1))
      (LOCAL: Memory.le th1.(Thread.local) mem1)
      (FUTURE: Memory.future conf.(memory) mem1),
    exists th2 mem2,
      <<STEPS: rtc (@Thread.internal_step lang) (th1, mem1) (th2, mem2)>> /\
      <<DECLARE: th2.(Thread.local) = Memory.init>>.
End Configuration.
