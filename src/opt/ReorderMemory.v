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

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma reorder_memory_get_promise_iff
      promise0 mem0 loc from to msg promise1 mem1
      (LE: Memory.le promise0 mem0)
      (PROMISE: Memory.promise promise0 mem0 loc from to msg promise1 mem1):
  forall l t m,
    (Memory.get l t mem0 = Some m /\ Memory.get l t promise0 = None) <->
    (Memory.get l t mem1 = Some m /\ Memory.get l t promise1 = None).
Proof.
  inv LE. inv PROMISE; memtac.
  - i. econs; i; des; memtac; try congruence.
    + splits.
      * apply Memory.join_get; memtac.
        rewrite Memory.join_comm.
        apply Memory.join_get; memtac.
      * apply Memory.join_get_None; memtac.
        eapply Memory.disjoint_get_None; eauto. memtac.
    + apply Memory.join_get_None_inv in H0; memtac.
      apply Memory.join_get_inv in H; memtac.
      congruence.
  - rewrite Memory.join_assoc in GLOBAL1.
    rewrite (Memory.join_comm _ promise1_ctx) in GLOBAL1.
    rewrite <- ? Memory.join_assoc in GLOBAL1.
    apply Memory.join2_cancel in GLOBAL1; repeat (splits; memtac).
    rewrite (Memory.join_comm global1_ctx _) in GLOBAL1.
    apply Memory.join2_cancel in GLOBAL1; repeat (splits; memtac).
    generalize (Memory.splits_intro loc msg msg0 LT1 LT2). i. des.
    exploit Memory.splits_disjoint; try apply SPLIT; eauto; i.
    { symmetry. apply GLOBAL0. }
    i. econs; i; des; memtac; try congruence.
    + apply Memory.join_get_inv in H; memtac; try congruence.
      splits.
      * apply Memory.join_get; repeat (splits; memtac).
      * apply Memory.join_get_None; memtac.
        apply Memory.join_get_None; memtac.
        { eapply Memory.disjoint_get_None; eauto. }
        { eapply Memory.disjoint_get_None; eauto. }
    + apply Memory.join_get_None_inv in H0; memtac.
      apply Memory.join_get_inv in H; repeat (splits; memtac).
      * rewrite Memory.join_comm.
        apply Memory.join_get; memtac.
      * apply Memory.join_get_inv in H; repeat (splits; memtac); try congruence.
      * apply Memory.join_get_None; memtac.
        eapply Memory.disjoint_get_None; eauto.
      * apply Memory.join_get_inv in H; repeat (splits; memtac); try congruence.
Qed.

Lemma reorder_memory_get_promise
      promise0 mem0 loc from to msg promise1 mem1
      l t m
      (LE: Memory.le promise0 mem0)
      (GET1: Memory.get l t mem1 = Some m)
      (GET2: Memory.get l t promise1 = None)
      (PROMISE: Memory.promise promise0 mem0 loc from to msg promise1 mem1):
  Memory.get l t mem0 = Some m /\
  Memory.get l t promise0 = None.
Proof.
  exploit reorder_memory_get_promise_iff; eauto. intros [X1 X2].
  apply X2. auto.
Qed.

Lemma reorder_memory_fulfill_promise
      promise1 loc1 from1 to1 msg1
      promise2 loc2 from2 to2 msg2
      promise3
      mem1 mem3
      (LE: Memory.le promise1 mem1)
      (FULFILL: Memory.fulfill promise1 loc1 from1 to1 msg1 promise2)
      (PROMISE: Memory.promise promise2 mem1 loc2 from2 to2 msg2 promise3 mem3):
  exists promise2',
    Memory.promise promise1 mem1 loc2 from2 to2 msg2 promise2' mem3 /\
    Memory.fulfill promise2' loc1 from1 to1 msg1 promise3.
Proof.
  inv FULFILL. inv PROMISE; memtac.
  - eexists. splits.
    + econs 1; eauto. repeat (splits; memtac).
    + econs; repeat (splits; memtac).
      * rewrite <- ? Memory.join_assoc. f_equal. apply Memory.join_comm.
      * symmetry. auto.
      * symmetry. auto.
  - rewrite <- ? Memory.join_assoc in JOIN.
    rewrite (Memory.join_assoc global1_ctx _ _) in JOIN.
    rewrite (Memory.join_comm global1_ctx _) in JOIN.
    rewrite <- ? Memory.join_assoc in JOIN.
    apply Memory.join2_cancel in JOIN; repeat (splits; memtac).
    rewrite (Memory.join_comm global1_ctx _) in JOIN.
    apply Memory.join2_cancel in JOIN; repeat (splits; memtac).
    eexists. splits.
    + econs 2.
      * rewrite <- Memory.join_assoc.
        rewrite (Memory.join_comm (Memory.singleton _ _ _) _).
        rewrite Memory.join_assoc. eauto.
      * repeat (splits; memtac).
      * rewrite <- Memory.join_assoc.
        rewrite Memory.join_comm.
        rewrite ? Memory.join_assoc. f_equal.
      * repeat (splits; memtac).
      * repeat (splits; memtac).
      * rewrite <- Memory.join_assoc.
        rewrite Memory.join_comm.
        rewrite <- Memory.join_assoc. f_equal.
        rewrite <- ? Memory.join_assoc. f_equal.
        rewrite Memory.join_comm.
        rewrite <- ? Memory.join_assoc.
        rewrite Memory.join_comm.
        rewrite <- ? Memory.join_assoc. auto.
      * auto.
    + generalize (Memory.splits_intro loc2 msg2 msg0 LT1 LT2). i. des.
      econs; repeat (splits; memtac).
      * rewrite <- ? Memory.join_assoc. f_equal.
        rewrite Memory.join_comm.
        rewrite <- ? Memory.join_assoc. eauto.
      * exploit Memory.splits_disjoint; try apply SPLIT; eauto.
      * exploit Memory.splits_disjoint;
          try apply SPLIT; try (symmetry; apply PROMISE1); eauto.
        i. memtac.
      * exploit Memory.splits_disjoint;
          try apply SPLIT; try (symmetry; apply PROMISE1); eauto.
        i. memtac.
Qed.

Lemma reorder_memory_get_fulfill
      promise0 mem0 loc from to msg promise1
      l t m
      (LOC: loc <> l)
      (LE: Memory.le promise0 mem0)
      (GET: Memory.get l t mem0 = Some m)
      (FULFILL: Memory.fulfill promise0 loc from to msg promise1):
  Memory.get l t promise0 = Memory.get l t promise1.
Proof.
  inv FULFILL.
  destruct (Memory.get l t promise1) eqn:G.
  - apply Memory.join_get; memtac.
  - apply Memory.join_get_None; memtac.
    destruct (Memory.get l t (Memory.singleton loc msg LT)) eqn:G'; auto.
    apply Memory.singleton_get_inv in G'. des. subst. congruence.
Qed.

Lemma reorder_memory_cell_fulfill
      promise0 loc from to msg promise1
      l
      (LOC: loc <> l)
      (FULFILL: Memory.fulfill promise0 loc from to msg promise1):
  promise0 l = promise1 l.
Proof.
  inv FULFILL. unfold Memory.join, Cell.join, Memory.singleton in *.
  unfold LocFun.add, LocFun.find in *. destruct (Loc.eq_dec l loc); [congruence|].
  unfold LocFun.init, Cell.bot, Cell.Raw.bot in *. s.
  apply Cell.extensionality'; ss.
  - i. destruct (Cell.Raw.messages (Cell.raw (promise1 l)) to0); auto.
  - i. destruct (Cell.Raw.ownership (Cell.raw (promise1 l)) to0); auto.
Qed.

Lemma reorder_memory_fulfill_fulfill
      promise1 loc1 from1 to1 msg1
      promise2 loc2 from2 to2 msg2
      promise3
      (FULFILL1: Memory.fulfill promise1 loc1 from1 to1 msg1 promise2)
      (FULFILL2: Memory.fulfill promise2 loc2 from2 to2 msg2 promise3):
  exists promise2',
    Memory.fulfill promise1 loc2 from2 to2 msg2 promise2' /\
    Memory.fulfill promise2' loc1 from1 to1 msg1 promise3.
Proof.
  inv FULFILL1. inv FULFILL2. memtac.
  eexists. splits.
  - econs.
    + rewrite <- Memory.join_assoc.
      rewrite (Memory.join_comm (Memory.singleton _ _ _) _).
      rewrite Memory.join_assoc. eauto.
    + repeat (splits; memtac).
  - econs; eauto. memtac.
Qed.
