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
  Definition syntax := IdentMap.t {lang:Language.t & lang.(Language.syntax)}.

  Structure t := mk {
    threads: IdentMap.t {lang:Language.t & Thread.t lang};
    memory: Memory.t;
  }.

  Definition init (s:syntax): t :=
    mk (IdentMap.map (fun s => existT _ _ (Thread.init _ s.(projT2))) s)
       Memory.init.

  Definition is_terminal (conf:t): Prop :=
    forall tid lang st (FIND: IdentMap.find tid conf.(threads) = Some (existT _ lang st)),
      Thread.is_terminal st.

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
