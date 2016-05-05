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


Ltac committac :=
  repeat
    (try match goal with
         | [|- Snapshot.le (Snapshot.join _ _) _] =>
           apply Snapshot.join_spec
         | [|- Snapshot.le (Snapshot.incr_reads _ _ _) _] =>
           apply Snapshot.incr_reads_spec
         end; ss).  

Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.release)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.read_step th1 mem0 loc2 ts2 val2 released2 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.read_step th0 mem0 loc2 ts2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
  inv STEP1. inv STEP2.
  exploit CommitFacts.read_min_spec; try apply WF0; try apply GET0; eauto.
  { eapply Snapshot.readable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  i. des.
  exploit CommitFacts.read_min_spec; try apply WF; try apply GET; eauto.
  { eapply Snapshot.le_on_readable; eauto. apply COMMIT. }
  { apply WF0. }
  i. des.
  eexists _, _. splits.
  - econs; eauto.
  - econs; eauto.
  - s. econs; s; try apply MemInv.sem_bot.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.read_min.
    destruct (Ordering.le Ordering.acquire ord2) eqn:ORD2'.
    { destruct ord2; ss. }
    econs.
    + destruct (Ordering.le Ordering.acquire ord1) eqn:ORD1; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
    + ss. i. rewrite RELEASED. auto.
    + ss. committac.
      * rewrite ACQUIRABLE. auto.
      * rewrite ACQUIRABLE1. auto.
Qed.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      th0 mem0
      th1
      th2 mem2
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 th2 mem2):
  exists th1' th2',
    <<STEP1: Local.promise_step th0 mem0 th1' mem2>> /\
    <<STEP2: Local.read_step th1' mem2 loc1 ts1 val1 released1 ord1 th2'>> /\
    <<LOCAL: sim_local th2' th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit Memory.future_get; eauto. i.
  exploit CommitFacts.read_min_spec; try apply COMMIT; eauto. i. des.
  eexists _, _. splits.
  - econs; try reflexivity; try apply MEMORY; eauto.
  - econs; eauto. s.
    match goal with
    | [|- ?x = None] => destruct x eqn:X; auto
    end.
    eapply Memory.promise_get_inv in X; try apply MEMORY; try apply WF0; eauto.
    des; [congruence|]. subst.
    exploit Memory.promise_get1; try apply MEMORY; try apply WF0; eauto. i.
    congruence.
  - s. econs; s; try apply MemInv.sem_bot.
    rewrite <- COMMIT0. apply CommitFacts.read_min_min. auto.
Qed.

Lemma reorder_read_fulfill
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.sc ord2 -> Ordering.le Ordering.sc ord1 -> False)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1 mem1
      th2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.sc ord2 -> Ordering.le Ordering.sc ord1 -> False)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem1):
  exists th1' th2',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem1>> /\
    <<STEP2: Local.read_step th1' mem1 loc1 ts1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_read_fence
      loc1 ts1 val1 released1 ord1
      ord2
      th0 mem0
      th1
      th2
      (ORD2: Ordering.le ord2 Ordering.release)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.fence_step th1 mem0 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.fence_step th0 mem0 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fulfill_read
      loc1 from1 to1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (ORD2: Ordering.le ord2 Ordering.release)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.read_step th1 mem0 loc2 ts2 val2 released2 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.read_step th0 mem0 loc2 ts2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fulfill_step th1' mem0 loc1 from1 to1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fulfill_promise
      loc1 from1 to1 val1 released1 ord1
      th0 mem0
      th1
      th2 mem2
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 th2 mem2):
  exists th1' th2',
    <<STEP1: Local.promise_step th0 mem0 th1' mem2>> /\
    <<STEP2: Local.fulfill_step th1' mem2 loc1 from1 to1 val1 released1 ord1 th2'>> /\
    <<LOCAL: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fulfill_fulfill
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fulfill_step th1' mem0 loc1 from1 to1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fulfill_write
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem2):
  exists th1' th2',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem2>> /\
    <<STEP2: Local.fulfill_step th1' mem2 loc1 from1 to1 val1 released1 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fence_promise
      ord1
      th0 mem0
      th1
      th2 mem2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 th2 mem2):
  exists th1' th2',
    <<STEP1: Local.promise_step th0 mem0 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fence_fulfill
      ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1' th2',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fence_step th1' mem0 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.

Lemma reorder_fence_write
      ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem2):
  exists th1' th2',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ord1 th2'>> /\
    <<SIM: sim_local th2' th2>>.
Proof.
Admitted.




(* Lemma sim_fulfill_promise *)
(*       loc from to val released ord *)
(*       th1_src mem1_src *)
(*       th1_tgt mem1_tgt *)
(*       th2_tgt mem2_tgt *)
(*       (ORD: Ordering.le ord Ordering.relaxed) *)
(*       (LOCAL1: sim_fulfill loc from to val released ord th1_src th1_tgt) *)
(*       (MEMORY1: sim_memory mem1_src mem1_tgt) *)
(*       (WF1_SRC: Local.wf th1_src mem1_src) *)
(*       (WF1_TGT: Local.wf th1_tgt mem1_tgt) *)
(*       (STEP_TGT: Local.promise_step th1_tgt mem1_tgt th2_tgt mem2_tgt): *)
(*   exists th2_src mem2_src, *)
(*     <<STEP_SRC: Local.promise_step th1_src mem1_src th2_src mem2_src>> /\ *)
(*     <<LOCAL2: sim_fulfill loc from to val released ord th2_src th2_tgt>> /\ *)
(*     <<MEMORY2: sim_memory mem2_src mem2_tgt>>. *)
(* Proof. *)
(*   inv LOCAL1. inv STEP_TGT. *)
(*   exploit MemInv.promise; eauto. *)
(*   { apply WF1_SRC. } *)
(*   { apply WF1_TGT. } *)
(*   i. des. *)
(*   exploit Memory.promise_future; try apply PROMISE_SRC; eauto. *)
(*   { apply WF1_SRC. } *)
(*   { apply WF1_SRC. } *)
(*   i. des. *)
(*   eexists _, _. splits; eauto. *)
(*   - econs; eauto. *)
(*     + reflexivity. *)
(*     + eapply Commit.future_wf; eauto. apply WF1_SRC. *)
(*   - econs; s; eauto. etransitivity; eauto. *)
(* Qed. *)

(* Lemma sim_fulfill_read *)
(*       loc1 from1 to1 val1 released1 ord1 *)
(*       loc2 ts2 val2 released2 ord2 *)
(*       th1_src mem1_src *)
(*       th1_tgt mem1_tgt *)
(*       th2_tgt *)
(*       (LOC: loc1 <> loc2) *)
(*       (ORD1: Ordering.le ord1 Ordering.relaxed) *)
(*       (ORD2: Ordering.le ord2 Ordering.release) *)
(*       (LOCAL1: sim_fulfill loc1 from1 to1 val1 released1 ord1 th1_src th1_tgt) *)
(*       (MEMORY1: sim_memory mem1_src mem1_tgt) *)
(*       (WF1_SRC: Local.wf th1_src mem1_src) *)
(*       (WF1_TGT: Local.wf th1_tgt mem1_tgt) *)
(*       (STEP_TGT: Local.read_step th1_tgt mem1_tgt loc2 ts2 val2 released2 ord2 th2_tgt): *)
(*   exists th2_src, *)
(*     <<STEP_SRC: Local.read_step th1_src mem1_src loc2 ts2 val2 released2 ord2 th2_src>> /\ *)
(*     <<LOCAL2: sim_fulfill loc1 from1 to1 val1 released1 ord1 th2_src th2_tgt>>. *)
(* Proof. *)
(*   inv LOCAL1. inv STEP_TGT. *)
(*   exploit Memory.le_get. *)
(*   { apply WF1_SRC. } *)
(*   { inv PROMISE. eapply Memory.le_get. *)
(*     - apply Memory.le_join_r. memtac. *)
(*     - apply Memory.singleton_get. *)
(*   } *)
(*   intro GET1_SRC. *)
(*   exploit Memory.splits_get; try apply GET; eauto. *)
(*   { apply MEMORY1. } *)
(*   intro GET2_SRC. *)
(*   exploit CommitFacts.read_min_spec; try apply GET2_SRC; eauto. *)
(*   { inv COMMIT. eapply Snapshot.readable_mon; eauto. *)
(*     etransitivity; [|apply COMMIT2]. apply COMMIT1. *)
(*   } *)
(*   { apply WF1_SRC. } *)
(*   { apply WF1_SRC. } *)
(*   i. des. *)
(*   destruct (Ordering.le Ordering.release ord1) eqn:ORD1'. *)
(*   { destruct ord1; ss. } *)
(*   assert (RELEASED_SRC: Memory.wf_snapshot released1 mem1_src). *)
(*   { inv WF1_SRC. inv MEMORY. exploit WF0; try apply GET1_SRC; eauto. } *)
(*   exploit CommitFacts.write_min_spec; try apply RELEASED_SRC; eauto. *)
(*   { eapply Snapshot.le_on_writable; eauto. apply COMMIT1. } *)
(*   { ss. inv COMMIT1. etransitivity; eauto. apply MONOTONE. } *)
(*   { instantiate (1 := ord1). destruct ord1; ss. } *)
(*   { apply WF1_SRC. } *)
(*   i. des. *)
(*   eexists _. splits; eauto. *)
(*   - econs; eauto. inv PROMISE. *)
(*     match goal with *)
(*     | [|- ?x = None] => destruct x eqn:X; auto *)
(*     end. *)
(*     apply Memory.join_get in X; memtac; try congruence. *)
(*     apply Memory.singleton_get_inv in X. des. congruence. *)
(*   - econs; eauto. s. *)
(*     exploit CommitFacts.write_min_min; try apply COMMIT1; eauto. i. *)
(*     exploit CommitFacts.read_min_min; try apply COMMIT; eauto. i. *)
(*     unfold CommitFacts.read_min in *. *)
(*     destruct (Ordering.le Ordering.acquire ord2) eqn:ORD2'. *)
(*     { destruct ord2; ss. } *)
(*     inv x0. inv x1. *)
(*     apply Snapshot.incr_writes_inv in CURRENT1. *)
(*     apply Snapshot.incr_reads_inv in CURRENT2. des. *)
(*     econs; ss. *)
(*     + apply Snapshot.incr_writes_spec. *)
(*       * apply Snapshot.incr_reads_spec; ss. *)
(*         etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*       * etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*     + i. unfold LocFun.add, LocFun.find. *)
(*       destruct (Loc.eq_dec loc loc1). *)
(*       * subst. rewrite ORD1'. *)
(*         etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*       * etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*     + etransitivity; eauto. *)
(*       apply Snapshot.join_spec. *)
(*       * apply Snapshot.join_l. *)
(*       * etransitivity; [|apply Snapshot.join_r]. *)
(*         etransitivity; [apply COMMIT1|]. *)
(*         apply COMMIT2. *)
(* Qed. *)

(* Lemma sim_fulfill_write *)
(*       loc1 from1 to1 val1 released1 ord1 *)
(*       loc2 from2 to2 val2 released2 ord2 *)
(*       th1_src mem1_src *)
(*       th1_tgt mem1_tgt *)
(*       th2_tgt mem2_tgt *)
(*       (LOC: loc1 <> loc2) *)
(*       (ORD1: Ordering.le ord1 Ordering.relaxed) *)
(*       (LOCAL1: sim_fulfill loc1 from1 to1 val1 released1 ord1 th1_src th1_tgt) *)
(*       (MEMORY1: sim_memory mem1_src mem1_tgt) *)
(*       (WF1_SRC: Local.wf th1_src mem1_src) *)
(*       (WF1_TGT: Local.wf th1_tgt mem1_tgt) *)
(*       (STEP_TGT: Local.write_step th1_tgt mem1_tgt loc2 from2 to2 val2 released2 ord2 th2_tgt mem2_tgt): *)
(*   exists th2_src mem2_src, *)
(*     <<STEP_SRC: Local.write_step th1_src mem1_src loc2 from2 to2 val2 released2 ord2 th2_src mem2_src>> /\ *)
(*     <<LOCAL2: sim_fulfill loc1 from1 to1 val1 released1 ord1 th2_src th2_tgt>> /\ *)
(*     <<MEMORY2: sim_memory mem2_src mem2_tgt>>. *)
(* Proof. *)
(*   destruct (Ordering.le Ordering.release ord1) eqn:ORD1'. *)
(*   { destruct ord1; ss. } *)
(*   inv LOCAL1. inv STEP_TGT. *)
(*   exploit MemInv.write; eauto. *)
(*   { apply WF1_SRC. } *)
(*   { apply WF1_TGT. } *)
(*   { inv PROMISE. unfold Memory.join. *)
(*     unfold Memory.singleton, LocFun.add, LocFun.find. *)
(*     destruct (Loc.eq_dec loc2 loc1); [congruence|]. *)
(*     unfold LocFun.init. rewrite Cell.bot_join. auto. *)
(*   } *)
(*   i. des. *)
(*   exploit Memory.write_future; try apply WRITE_SRC; eauto. *)
(*   { apply WF1_SRC. } *)
(*   { apply WF1_SRC. } *)
(*   i. des. *)
(*   exploit Memory.write_get; try apply WRITE_SRC; eauto. *)
(*   { apply WF1_SRC. } *)
(*   intro GET2_SRC. *)
(*   exploit CommitFacts.write_min_spec; eauto. *)
(*   { eapply Snapshot.writable_mon; [|apply COMMIT]. *)
(*     etransitivity; [|apply COMMIT2]. apply COMMIT1. *)
(*   } *)
(*   { etransitivity; [apply COMMIT1|]. *)
(*     etransitivity; [apply COMMIT2|]. *)
(*     etransitivity; [apply COMMIT|]. apply COMMIT. *)
(*   } *)
(*   { instantiate (1 := ord2). inv COMMIT. i. *)
(*     rewrite <- RELEASED, <- RELEASE; auto. *)
(*     apply Snapshot.incr_writes_spec; auto. *)
(*     etransitivity; [apply COMMIT1|]. *)
(*     etransitivity; [apply COMMIT2|]. *)
(*     apply MONOTONE. *)
(*   } *)
(*   { eapply Commit.future_wf; eauto. apply WF1_SRC. } *)
(*   { inv WF2. exploit WF; eauto. } *)
(*   i. des. *)
(*   exploit Memory.le_get. *)
(*   { apply WF1_SRC. } *)
(*   { inv PROMISE. eapply Memory.le_get. *)
(*     - apply Memory.le_join_r. memtac. *)
(*     - apply Memory.singleton_get. *)
(*   } *)
(*   intro GET1_SRC. *)
(*   exploit Memory.future_get; try apply GET1_SRC; eauto. *)
(*   intro GET1_SRC'. *)
(*   exploit CommitFacts.write_min_spec; try apply GET1_SRC'; eauto. *)
(*   { eapply Snapshot.le_on_writable; eauto. apply COMMIT1. } *)
(*   { inv COMMIT1. rewrite <- RELEASED, RELEASED1; auto. *)
(*     apply MONOTONE. *)
(*   } *)
(*   { instantiate (1 := ord1). destruct ord1; ss. } *)
(*   { inv WF2. exploit WF0; eauto. } *)
(*   i. des. *)
(*   eexists _, _. splits; eauto. *)
(*   - econs; eauto. *)
(*   - econs; eauto. s. *)
(*     exploit CommitFacts.write_min_min; try apply COMMIT1; eauto. i. *)
(*     exploit CommitFacts.write_min_min; try apply COMMIT; eauto. i. *)
(*     inv x0. inv x1. *)
(*     apply Snapshot.incr_writes_inv in CURRENT1. *)
(*     apply Snapshot.incr_writes_inv in CURRENT2. des. *)
(*     econs; ss. *)
(*     + repeat apply Snapshot.incr_writes_spec; ss. *)
(*       * etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*       * etransitivity; [apply COMMIT1|]. *)
(*         etransitivity; [apply COMMIT2|]. *)
(*         apply COMMIT. *)
(*     + i. unfold LocFun.add, LocFun.find. rewrite ORD1'. *)
(*       etransitivity; [|apply RELEASED2]. *)
(*       unfold LocFun.add, LocFun.find. *)
(*       destruct (Loc.eq_dec loc loc1). *)
(*       * subst. destruct (Loc.eq_dec loc1 loc2); [congruence|]. *)
(*         etransitivity; [apply COMMIT1|]. apply COMMIT2. *)
(*       * destruct (Loc.eq_dec loc loc2). *)
(*         { subst. *)
(*           match goal with *)
(*           | [|- context[if ?c then _ else _]] => destruct c *)
(*           end. *)
(*           - apply Snapshot.join_spec. *)
(*             + etransitivity; [|apply Snapshot.join_l]. *)
(*               apply Snapshot.incr_writes_mon. *)
(*               etransitivity; [apply COMMIT1|]. apply COMMIT2. *)
(*             + etransitivity; [|apply Snapshot.join_r]. *)
(*               etransitivity; [apply COMMIT1|]. apply COMMIT2. *)
(*           - etransitivity; [apply COMMIT1|]. apply COMMIT2. *)
(*         } *)
(*         { etransitivity; [apply COMMIT1|]. apply COMMIT2. } *)
(*     + etransitivity; [apply COMMIT1|]. *)
(*       etransitivity; [apply COMMIT2|]. eauto. *)
(* Qed. *)
