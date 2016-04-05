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


Module Configuration.
  Definition syntax := IdentMap.t State.syntax.

  Structure t := mk {
    threads: IdentMap.t Thread.t;
    memory: Memory.t;
  }.

  Definition init (s:syntax): t :=
    mk (IdentMap.map Thread.init s) Memory.init.

  Definition is_terminal (conf:t): Prop :=
    forall tid th (FIND: IdentMap.find tid conf.(threads) = Some th),
      Thread.is_terminal th.

  Inductive step (e:option Event.t) (c1:t): forall (c2:t), Prop :=
  | step_intro
      tid th1 th2 memory2 th3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some th1)
      (STEPS: rtc Thread.internal_step (th1, c1.(memory)) (th2, memory2))
      (STEP: Thread.step e th2 memory2 th3 memory3)
      (CONSISTENT: Thread.consistent th3 memory3):
      step e c1 (mk (IdentMap.add tid th3 c1.(threads)) memory3)
  .

  Definition consistent (conf:t): Prop :=
    forall tid th1 mem1
      (FIND: IdentMap.find tid conf.(threads) = Some th1)
      (LOCAL: Memory.le th1.(Thread.local) mem1)
      (FUTURE: Memory.future conf.(memory) mem1),
    exists th2 mem2,
      <<STEPS: rtc Thread.internal_step (th1, mem1) (th2, mem2)>> /\
      <<DECLARE: th2.(Thread.local) = Memory.init>>.
End Configuration.
