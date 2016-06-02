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
      loc ts released ord1 ord2 ord
      commit0 commit2
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (COMMIT: Commit.read commit0 loc ts released ord commit2)
      (WF0: Commit.wf commit0)
      (TS: Time.le (released.(Capability.rw) loc) ts):
  <<COMMIT1': Commit.read commit0 loc ts released ord1 (CommitFacts.read_min loc ts released ord1 commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.read_min loc ts released ord1 commit0) loc ts released ord2 commit2>>.
Proof.
  exploit CommitFacts.read_min_spec.
  { inv COMMIT. apply UR1. }
  { i. apply COMMIT. etrans. apply H. apply ORD1. }
  { auto. }
  { inv COMMIT. apply WF_REL. }
  i.
  exploit (@CommitFacts.read_min_spec loc ts released ord (CommitFacts.read_min loc ts released ord1 commit0)); s.
  { unfold Capability.join_if. condtac; committac; try apply COMMIT.
    etrans; eauto. apply COMMIT.
  }
  { i. unfold Capability.join_if. condtac; committac.
    - unfold TimeMap.incr. unfold LocFun.add. rewrite Reg.eq_dec_eq.
      apply Time.join_spec; try refl. apply COMMIT. auto.
    - unfold TimeMap.incr. unfold LocFun.add. rewrite Reg.eq_dec_eq.
      apply Time.join_spec; try refl. apply COMMIT. auto.
  }
  { apply x0. }
  { inv COMMIT. apply WF_REL. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2; eauto; try apply COMMIT.
  inv COMMIT. inv MON.
  econs; committac; try by etrans; eauto.
  - apply RA. etrans; eauto.
  - etrans; eauto. apply WF.
  - etrans; eauto. apply WF.
  - apply ACQ. etrans; eauto.
  - etrans; eauto. apply WF.
  - etrans; eauto. etrans; apply WF.
  - etrans; eauto. apply WF.
  - etrans; eauto. etrans; apply WF.
Qed.

(* NOTE: the `ORD2` condition is stronger than what can be proved.  In
   addition to the current criteria, [ord1 = ord2 = SC] is also
   sufficient to prove the memory access merge.
 *)
Lemma write_read
      loc ts released ord1 ord2
      commit0 commit2
      (ORD2: Ordering.le ord2 Ordering.acqrel)
      (COMMIT: Commit.write commit0 loc ts released ord1 commit2)
      (WF0: Commit.wf commit0)
      (TS: Time.le (released.(Capability.rw) loc) ts):
  <<COMMIT1': Commit.write commit0 loc ts released ord1 (CommitFacts.write_min loc ts released commit0)>> /\
  <<COMMIT2': Commit.read (CommitFacts.write_min loc ts released commit0) loc ts released ord2 commit2>>.
Proof.
  exploit CommitFacts.write_min_spec.
  { inv COMMIT. apply REL. }
  { inv COMMIT. apply RW1. }
  { apply COMMIT. }
  { i. apply COMMIT. eauto. }
  { auto. }
  { inv COMMIT. apply WF_REL. }
  i.
  exploit (@CommitFacts.read_min_spec loc ts released ord2 (CommitFacts.write_min loc ts released commit0)); s.
  { committac.
    - etrans; eauto. apply COMMIT.
    - unfold TimeMap.incr. unfold LocFun.add. rewrite Reg.eq_dec_eq.
      apply Time.join_spec; try refl. etrans.
      + inv WF0. apply CUR.
      + apply Time.le_lteq. left. apply COMMIT.
  }
  { i. committac. unfold TimeMap.incr. unfold LocFun.add. rewrite Reg.eq_dec_eq.
    apply Time.join_spec; try refl. apply Time.le_lteq. left. apply COMMIT.
  }
  { apply x0. }
  { apply COMMIT. }
  i.
  splits; eauto. eapply CommitFacts.read_mon2;
                   try match goal with
                       | [|- is_true (Ordering.le _ _)] => refl
                       end;
                   eauto; try apply COMMIT.
  inv COMMIT. inv MON.
  econs; committac; try by etrans; eauto.
  - unfold LocFun.add, LocFun.find. condtac; committac.
    etrans; eauto. refl.
  - etrans; eauto. apply WF.
  - etrans; eauto. apply WF.
  - etrans; eauto. apply WF.
  - etrans; eauto. inv WF. etrans; apply CUR0.
  - etrans; eauto. apply WF.
  - etrans; eauto. inv WF. etrans; apply CUR0.
  - etrans; eauto. etrans; apply WF.
  - etrans; eauto. etrans; apply WF.
  - etrans; eauto. apply WF.
  - etrans; eauto. etrans; apply WF.
  - etrans; eauto. etrans; [apply WF|]. etrans; apply WF.
  - etrans; eauto. etrans; apply WF.
  - etrans; eauto. etrans; [apply WF|]. etrans; apply WF.
Qed.


(* TODO: WW merge *)


Lemma read_fence_read_fence
      ord1 ord2 ord
      commit0 commit2
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (COMMIT: Commit.read_fence commit0 ord commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.read_fence commit0 ord1 (CommitFacts.read_fence_min ord1 commit0)>> /\
  <<COMMIT2': Commit.read_fence (CommitFacts.read_fence_min ord1 commit0) ord2 commit2>>.
Proof.
  exploit CommitFacts.read_fence_min_spec; eauto. i.
  exploit CommitFacts.read_fence_min_spec; try apply x0; eauto. i.
  splits; eauto.
  eapply CommitFacts.read_fence_mon2;
    try apply x1; try refl; try apply COMMIT; eauto.
  inv COMMIT. inv MON.
  econs; committac; try by etrans; eauto.
  repeat condtac; committac.
  + apply RA. etrans; eauto.
  + apply RA. etrans; eauto.
Qed.

Lemma write_fence_write_fence
      ord1 ord2 ord
      commit0 commit2
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (COMMIT: Commit.write_fence commit0 ord commit2)
      (WF0: Commit.wf commit0):
  <<COMMIT1': Commit.write_fence commit0 ord1 (CommitFacts.write_fence_min ord1 commit0)>> /\
  <<COMMIT2': Commit.write_fence (CommitFacts.write_fence_min ord1 commit0) ord2 commit2>>.
Proof.
  exploit CommitFacts.write_fence_min_spec; eauto. i.
  exploit CommitFacts.write_fence_min_spec; try apply x0; eauto. i.
  splits; eauto.
  eapply CommitFacts.write_fence_mon2;
    try apply x1; try refl; try apply COMMIT; eauto.
  inv COMMIT. inv MON.
  econs; committac; try by etrans; eauto.
  unfold LocFun.find. repeat condtac; committac.
  - rewrite RA. refl. etrans; eauto.
  - rewrite RA. refl. etrans; eauto.
  - etrans; eauto. refl.
Qed.
