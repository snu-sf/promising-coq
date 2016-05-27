Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma read_read
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.read commit1 loc2 ts2 released2 ord2 commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.read commit0 loc2 ts2 released2 ord2 (CommitFacts.read_min loc2 ts2 released2 ord2 commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.read_min loc2 ts2 released2 ord2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.read_min_spec.
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. }
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. eauto. }
  { auto. }
  { inv COMMIT2. apply WF_REL. }
  i.
  exploit CommitFacts.read_min_spec.
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - etrans; eauto. apply WF1.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. apply WF1.
Admitted.

Lemma read_write
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.write commit1 loc2 ts2 released2 ord2 commit2)
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write commit0 loc2 ts2 released2 ord2 (CommitFacts.write_min loc2 ts2 released2 commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.write_min loc2 ts2 released2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.write_min_spec.
  { inv COMMIT2. apply REL. }
  { eapply TimeFacts.le_lt_lt. inv COMMIT1. apply MON. apply COMMIT2. }
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. }
  { i. splits.
    - etrans. inv COMMIT1. apply MON. apply COMMIT2. eauto.
    - apply COMMIT2. auto.
  }
  { auto. }
  { apply COMMIT2. }
  i.
  exploit CommitFacts.read_min_spec.
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find. condtac; committac.
    etrans; eauto.
  - etrans; eauto. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. inv WF1. etrans; apply CUR1.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; apply WF1.
  - etrans; eauto. etrans; try apply WF1. etrans; apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; apply WF1.
Admitted.

Lemma read_read_fence
      loc1 ts1 released1 ord1
      ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.read_fence commit1 ord2 commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.read_fence commit0 ord2 (CommitFacts.read_fence_min ord2 commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.read_fence_min ord2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.read_fence_min_spec; eauto. i.
  exploit CommitFacts.read_min_spec.
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - condtac; etrans; eauto.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. apply WF1.
Admitted.

Lemma read_write_fence
      loc1 ts1 released1 ord1
      ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.write_fence commit1 ord2 commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write_fence commit0 ord2 (CommitFacts.write_fence_min ord2 commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.write_fence_min ord2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.write_fence_min_spec; eauto. i.
  exploit CommitFacts.read_min_spec.
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.find. condtac; committac.
    + etrans; eauto.
    + etrans; eauto.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. apply WF1.
Admitted.

Lemma write_read
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.write commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.read commit1 loc2 ts2 released2 ord2 commit2)
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.read commit0 loc2 ts2 released2 ord2 (CommitFacts.read_min loc2 ts2 released2 ord2 commit0)>> /\
  <<COMMIT2': Commit.write (CommitFacts.read_min loc2 ts2 released2 ord2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.read_min_spec.
  { inv COMMIT1. etrans. apply MON. apply COMMIT2. }
  { inv COMMIT1. etrans. apply MON. apply COMMIT2. eauto. }
  { apply WF0. }
  { inv COMMIT2. apply WF_REL. }
  i.
  exploit CommitFacts.write_min_spec.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.write_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find. condtac; committac.
    + etrans; eauto.
    + etrans; eauto.
  - etrans; eauto. etrans; [apply REL3|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. inv WF1. etrans; apply CUR1.
  - etrans; eauto. etrans; [apply REL3|]. etrans; apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. etrans; apply WF1.
Admitted.

Lemma write_write
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.write commit0 loc1 ts1 released1 ord1 commit1)
      (COMMIT2: Commit.write commit1 loc2 ts2 released2 ord2 commit2)
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write commit0 loc2 ts2 released2 ord2 (CommitFacts.write_min loc2 ts2 released2 commit0)>> /\
  <<COMMIT2': Commit.write (CommitFacts.write_min loc2 ts2 released2 commit0) loc1 ts1 released1 ord1 commit2>>.
Proof.
  exploit CommitFacts.write_min_spec.
  { inv COMMIT2. apply REL. }
  { eapply TimeFacts.le_lt_lt. inv COMMIT1. apply MON. apply COMMIT2. }
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. }
  { i. splits.
    - etrans. inv COMMIT1. apply MON. apply COMMIT2. eauto.
    - apply COMMIT2. auto.
  }
  { auto. }
  { apply COMMIT2. }
  i.
  exploit CommitFacts.write_min_spec.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { apply x0. }
  { inv COMMIT1. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.write_mon2; eauto; try refl; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find. repeat condtac; committac.
    + etrans; eauto.
    + etrans; eauto.
  - etrans; eauto. etrans; [apply REL6|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. inv WF1. etrans; [apply CUR1|]. apply CUR1.
  - etrans; eauto. apply CUR0.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. inv WF1. etrans; [apply CUR1|]. apply CUR1.
  - etrans; eauto. etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply CUR0|]. etrans; [apply WF1|]. etrans; [apply WF1|]. apply WF1.
Admitted.

Lemma read_fence_write
      ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read_fence commit0 ord1 commit1)
      (COMMIT2: Commit.write commit1 loc2 ts2 released2 ord2 commit2)
      (ORD1: Ordering.le ord1 Ordering.acqrel)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write commit0 loc2 ts2 released2 ord2 (CommitFacts.write_min loc2 ts2 released2 commit0)>> /\
  <<COMMIT2': Commit.read_fence (CommitFacts.write_min loc2 ts2 released2 commit0) ord1 commit2>>.
Proof.
  exploit CommitFacts.write_min_spec.
  { inv COMMIT2. apply REL. }
  { eapply TimeFacts.le_lt_lt. inv COMMIT1. apply MON. apply COMMIT2. }
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. }
  { i. splits.
    - etrans. inv COMMIT1. apply MON. apply COMMIT2. eauto.
    - apply COMMIT2. auto.
  }
  { auto. }
  { apply COMMIT2. }
  i.
  exploit CommitFacts.read_fence_min_spec.
  { apply x0. }
  i.
  splits; eauto. eapply CommitFacts.read_fence_mon2;
                   try match goal with
                       | [|- is_true (Ordering.le _ _)] => refl
                       end;
                   eauto; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find. condtac; committac. etrans; eauto.
  - condtac; committac; try by etrans; eauto.
    + etrans; eauto. apply WF1.
    + rewrite RA; auto.
    + etrans; eauto. apply WF1.
    + etrans; eauto. inv WF1. etrans; [apply CUR1|]. apply CUR1.
    + etrans; eauto. apply WF1.
    + etrans; eauto. apply WF1.
    + etrans; eauto. inv WF1. etrans; [apply CUR1|]. apply CUR1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. etrans; [apply WF1|]. apply WF1.
Qed.

Lemma write_fence_write
      ord1
      loc2 ts2 released2 ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.write_fence commit0 ord1 commit1)
      (COMMIT2: Commit.write commit1 loc2 ts2 released2 ord2 commit2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write commit0 loc2 ts2 released2 ord2 (CommitFacts.write_min loc2 ts2 released2 commit0)>> /\
  <<COMMIT2': Commit.write_fence (CommitFacts.write_min loc2 ts2 released2 commit0) ord1 commit2>>.
Proof.
  exploit CommitFacts.write_min_spec.
  { inv COMMIT2. apply REL. }
  { eapply TimeFacts.le_lt_lt. inv COMMIT1. apply MON. apply COMMIT2. }
  { etrans. inv COMMIT1. apply MON. apply COMMIT2. }
  { i. splits.
    - etrans. inv COMMIT1. apply MON. apply COMMIT2. eauto.
    - apply COMMIT2. auto.
  }
  { auto. }
  { apply COMMIT2. }
  i.
  exploit CommitFacts.write_fence_min_spec.
  { apply x0. }
  i.
  splits; eauto. eapply CommitFacts.write_fence_mon2;
                   try match goal with
                       | [|- is_true (Ordering.le _ _)] => refl
                       end;
                   eauto; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find.
    repeat condtac; committac;
      try by destruct ord1; inv ORD1; inv COND.
    etrans; [apply REL0|]. eauto.
  - etrans; eauto. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. inv WF1. etrans; [apply CUR1|]. apply CUR1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. apply WF1.
  - etrans; eauto. etrans; [apply WF1|]. etrans; [apply WF1|]. apply WF1.
Qed.

Lemma read_fence_write_fence
      ord1
      ord2
      commit0 commit1 commit2
      (COMMIT1: Commit.read_fence commit0 ord1 commit1)
      (COMMIT2: Commit.write_fence commit1 ord2 commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write_fence commit0 ord2 (CommitFacts.write_fence_min ord2 commit0)>> /\
  <<COMMIT2': Commit.read_fence (CommitFacts.write_fence_min ord2 commit0) ord1 commit2>>.
Proof.
  exploit CommitFacts.write_fence_min_spec; eauto. i.
  exploit CommitFacts.read_fence_min_spec; try apply x0; eauto. i.
  splits; eauto. eapply CommitFacts.read_fence_mon2;
                   try match goal with
                       | [|- is_true (Ordering.le _ _)] => refl
                       end;
                   eauto; try apply COMMIT2.
  inv COMMIT1. inv COMMIT2. inv MON. inv MON0.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.find. condtac; committac.
    + etrans; eauto.
    + etrans; eauto.
  - condtac; committac.
    + rewrite RA; auto.
    + etrans; eauto.
Qed.
