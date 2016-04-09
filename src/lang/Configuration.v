Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
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

  Definition consistent (ths:t): Prop :=
    forall tid1 lang1 th1
      tid2 lang2 th2
      (TID: tid1 <> tid2)
      (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 th1))
      (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 th2)),
      Memory.disjoint th1.(Thread.local) th2.(Thread.local).

  Inductive disjoint (ths1 ths2:t): Prop :=
  | disjoint_intro
      (THREAD:
         forall tid lth1 lth2
           (TH1: IdentMap.find tid ths1 = Some lth1)
           (TH2: IdentMap.find tid ths2 = Some lth2),
           False)
      (MEMORY:
         forall tid1 lang1 th1
           tid2 lang2 th2
           (TH1: IdentMap.find tid1 ths1 = Some (existT _ lang1 th1))
           (TH2: IdentMap.find tid2 ths2 = Some (existT _ lang2 th2)),
           Memory.disjoint th1.(Thread.local) th2.(Thread.local))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs; i.
    - eapply THREAD; eauto.
    - symmetry. eapply MEMORY; eauto.
  Qed.

  Definition le (ths:t) (mem:Memory.t): Prop :=
    forall tid lang th
      (TH: IdentMap.find tid ths = Some (existT _ lang th)),
      Memory.le th.(Thread.local) mem.

  Definition compose_option {A} (th1 th2:option A) :=
    match th1 with
    | None => th2
    | Some _ => th1
    end.

  Definition compose (ths1 ths2:t): t :=
    IdentMap.map2 compose_option ths1 ths2.

  Lemma compose_spec ths1 ths2 tid:
    IdentMap.find tid (compose ths1 ths2) = compose_option (IdentMap.find tid ths1) (IdentMap.find tid ths2).
  Proof. apply IdentMap.Facts.map2_1bis; auto. Qed.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) Memory.init.
  Definition is_terminal (conf:t): Prop := Threads.is_terminal conf.(threads).

  Inductive consistent (conf:t): Prop :=
  | consistent_intro
      (THREADS: Threads.consistent conf.(threads))
      (LE: Threads.le conf.(threads) conf.(memory))
      (VALID:
         forall tid lang th1
           (FIND: IdentMap.find tid conf.(threads) = Some (existT _ lang th1))
           mem1
           (LOCAL: Memory.le th1.(Thread.local) mem1)
           (FUTURE: Memory.future conf.(memory) mem1),
         exists th2 mem2,
           <<STEPS: rtc (@Thread.internal_step lang) (th1, mem1) (th2, mem2)>> /\
           <<DECLARE: th2.(Thread.local) = Memory.init>>)
  .

  Inductive step (e:option Event.t) (c1:t): forall (c2:t), Prop :=
  | step_intro
      tid lang th1 th2 memory2 th3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some (existT _ lang th1))
      (STEPS: rtc (@Thread.internal_step lang) (th1, c1.(memory)) (th2, memory2))
      (STEP: Thread.step e th2 memory2 th3 memory3)
      (CONSISTENT: Thread.consistent th3 memory3):
      step e c1 (mk (IdentMap.add tid (existT _ _ th3) c1.(threads)) memory3)
  .

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           end;
       ss; subst).

  Lemma consistent_step
        e c1 c2
        (STEP: step e c1 c2)
        (CONSISTENT1: consistent c1):
    <<CONSISTENT2: consistent c2>> /\
    <<FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv STEP. s.
    exploit Thread.future_rtc_internal_step; eauto.
    { s. inv CONSISTENT1. eapply LE; eauto. }
    s. i. des.
    exploit Thread.future_step; eauto. i. des.
    splits.
    - econs; s.
      + ii. simplify.
        * congruence.
        * inv CONSISTENT1. exploit THREADS; eauto. i.
          exploit Thread.disjoint_rtc_internal_step; eauto. s. i. des.
          exploit Thread.disjoint_step; eauto. i. des.
          symmetry. auto.
        * inv CONSISTENT1. exploit THREADS; eauto. i.
          exploit Thread.disjoint_rtc_internal_step; eauto. s. i. des.
          exploit Thread.disjoint_step; eauto. i. des.
          auto.
        * inv CONSISTENT1. eapply THREADS; [|eauto|eauto]. auto.
      + ii. simplify.
        inv CONSISTENT1. exploit LE1; eauto. i.
        exploit Thread.disjoint_rtc_internal_step; eauto. s. i. des.
        exploit Thread.disjoint_step; eauto. i. des.
        auto.
      + admit.
    - etransitivity; eauto.
  Admitted.

  Lemma consistent_rtc_step
        c1 c2
        (STEPS: rtc (step None) c1 c2)
        (CONSISTENT1: consistent c1):
    <<CONSISTENT2: consistent c2>> /\
    <<FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    revert CONSISTENT1. induction STEPS; i.
    - splits; auto. reflexivity.
    - exploit consistent_step; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto. etransitivity; eauto.
  Qed.

  Lemma disjoint_step
        e c1 c2 ths
        (STEP: step e c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (CONSISTENT1: consistent c1)
        (CONSISTENT: consistent (mk ths c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<CONSISTENT: consistent (mk ths c2.(memory))>>.
  Proof.
    inv STEP. inv CONSISTENT. ss. splits.
    - econs; i; simplify.
      + inv DISJOINT. eapply THREAD; eauto.
      + inv DISJOINT. eapply THREAD; eauto.
      + exploit Thread.disjoint_rtc_internal_step; eauto.
        { s. inv DISJOINT. eapply MEMORY; eauto. }
        s. i. des.
        exploit Thread.disjoint_step; eauto. i. des.
        auto.
      + inv DISJOINT. eapply MEMORY; eauto.
    - econs; s; eauto.
      + ii.
        exploit Thread.disjoint_rtc_internal_step; eauto.
        { s. inv DISJOINT. eapply MEMORY; eauto. }
        i. des.
        exploit Thread.disjoint_step; eauto. i. des.
        auto.
      + i. exploit VALID; eauto.
        exploit Thread.future_rtc_internal_step; eauto.
        { s. inv CONSISTENT1. eapply LE0. eauto. }
        i. des.
        exploit Thread.future_step; eauto. i. des.
        repeat (etransitivity; eauto).
  Qed.

  Lemma disjoint_rtc_step
        c1 c2 ths
        (STEPS: rtc (step None) c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (CONSISTENT1: consistent c1)
        (CONSISTENT: consistent (mk ths c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<CONSISTENT: consistent (mk ths c2.(memory))>>.
  Proof.
    revert DISJOINT CONSISTENT1 CONSISTENT. induction STEPS; auto. i.
    exploit consistent_step; eauto. i. des.
    exploit disjoint_step; eauto. i. des.
    apply IHSTEPS; auto.
  Qed.
End Configuration.
