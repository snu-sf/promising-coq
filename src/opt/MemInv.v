Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.
Require Import Simulation.

Set Implicit Arguments.

Module MemInv.
  Definition t := Memory.t.

  Inductive sem (inv:t): forall (promise_src promise_tgt:Memory.t), Prop :=
  | sem_intro
      promise_tgt
      (DISJOINT: Memory.disjoint promise_tgt inv):
      sem inv (Memory.join promise_tgt inv) promise_tgt
  .

  Lemma promise
        inv
        loc from to msg
        promise1_src global1_src
        promise1_tgt global1_tgt promise2_tgt global2_tgt
        (LE1_SRC: Memory.le promise1_src global1_src)
        (LE1_TGT: Memory.le promise1_tgt global1_tgt)
        (SIM1: sim_memory global1_src global1_tgt)
        (INV1: sem inv promise1_src promise1_tgt)
        (PROMISE_TGT: Memory.promise promise1_tgt global1_tgt loc from to msg promise2_tgt global2_tgt):
    exists promise2_src global2_src,
      <<LE1_SRC: Memory.le promise2_src global2_src>> /\
      <<SIM2: sim_memory global2_src global2_tgt>> /\
      <<INV2: sem inv promise2_src promise2_tgt>> /\
      <<PROMISE_SRC: Memory.promise promise1_src global1_src loc from to msg promise2_src global2_src>>.
  Proof.
    inv SIM1. inv INV1. inv PROMISE_TGT; memtac.
    - rewrite <- Memory.join_assoc in SPLITS.
      apply Memory.splits_join_inv2 in SPLITS; repeat (splits; memtac).
      exists (Memory.join (Memory.join promise1_tgt inv) (Memory.singleton loc msg LT)).
      exists (Memory.join (Memory.join (Memory.join promise1_tgt inv) (Memory.singleton loc msg LT)) ohs).
      splits.
      + apply Memory.le_join_l. repeat (splits; memtac).
        symmetry in DISJOINT3. eapply Memory.splits_disjoint in DISJOINT3; [|eauto].
        memtac.
      + econs. rewrite <- ? Memory.join_assoc.
        apply Memory.splits_join; (repeat (splits; memtac)).
        rewrite (Memory.join_comm _ ohs), Memory.join_assoc.
        apply Memory.splits_join; (repeat (splits; memtac)).
      + rewrite <- ? Memory.join_assoc, (Memory.join_comm inv _).
        rewrite Memory.join_assoc. econs. repeat (splits; memtac).
        symmetry in DISJOINT3. eapply Memory.splits_disjoint in DISJOINT3; [|eauto].
        memtac.
      + econs 1; eauto.
        * symmetry in DISJOINT3. eapply Memory.splits_disjoint in DISJOINT3; [|eauto].
          repeat (splits; memtac).
        * rewrite <- (Memory.join_assoc _ (Memory.singleton _ _ _) ohs).
          rewrite (Memory.join_comm (Memory.singleton _ _ _) ohs).
          rewrite Memory.join_assoc.
          auto.
        * admit. (* wf_snapshot *)
    - rewrite Memory.join_assoc, (Memory.join_comm _ promise1_ctx) in SPLITS.
      rewrite <- ? Memory.join_assoc in SPLITS.
      apply Memory.splits_join_inv2 in SPLITS; repeat (splits; memtac).
      rewrite (Memory.join_comm global1_ctx _) in SPLITS.
      apply Memory.splits_join_inv2 in SPLITS; repeat (splits; memtac).
      rewrite ? Memory.join_assoc, (Memory.join_comm _ promise1_ctx) in JOIN.
      rewrite <- ? Memory.join_assoc in JOIN. repeat (splits; memtac).
      rewrite (Memory.join_comm global1_ctx _) in JOIN. memtac.
      generalize (Memory.splits_intro loc msg msg0 LT1 LT2). i. des.
      exists (Memory.join (Memory.join inv promise1_ctx)
                     (Memory.join (Memory.singleton loc msg LT1) (Memory.singleton loc msg0 LT2))).
      exists (Memory.join (Memory.join (Memory.join inv ohs0) promise1_ctx)
                     (Memory.join (Memory.singleton loc msg LT1) (Memory.singleton loc msg0 LT2))).
      splits.
      + symmetry in DISJOINT5. symmetry in PROMISE2. symmetry in DISJOINT3.
        exploit Memory.splits_disjoint; try apply SPLIT; try apply DISJOINT5; eauto. i. memtac.
        exploit Memory.splits_disjoint; try apply SPLIT; try apply PROMISE2; eauto. i. memtac.
        exploit Memory.splits_disjoint; try apply SPLIT; try apply DISJOINT3; eauto. i. memtac.
        repeat apply Memory.le_join;
          try reflexivity;
          repeat (splits; memtac).
        apply Memory.le_join_l. memtac.
      + econs. rewrite <- Memory.join_assoc.
        apply Memory.splits_join; (repeat (splits; memtac)).
      + rewrite <- ? Memory.join_assoc, (Memory.join_comm inv _).
        econs. repeat (splits; memtac).
      + econs 2.
        * rewrite Memory.join_comm, ? Memory.join_assoc. auto.
        * repeat (splits; memtac).
        * instantiate (1 := ohs0).
          rewrite ? Memory.join_assoc, (Memory.join_comm ohs0 _).
          rewrite <- ? Memory.join_assoc. f_equal.
          rewrite (Memory.join_comm ohs0 _).
          rewrite ? Memory.join_assoc. auto.
        * repeat (splits; memtac).
        * auto.
        * rewrite ? Memory.join_assoc, (Memory.join_comm ohs0 _). auto.
        * admit. (* wf_snapshot *)
  Admitted.

  Lemma confirm_tgt
        inv promise1_src promise1_tgt promise2_tgt
        loc from to msg
        (INV: sem inv promise1_src promise1_tgt)
        (CONFIRM: Memory.confirm promise1_tgt loc from to msg promise2_tgt):
    exists (LT: Time.lt from to),
      <<DISJOINT: Memory.disjoint inv (Memory.singleton loc msg LT)>> /\
      <<INV: sem (Memory.join inv (Memory.singleton loc msg LT)) promise1_src promise2_tgt>>.
  Proof.
    inv INV. inv CONFIRM. memtac.
    exists LT. splits; memtac.
    rewrite <- Memory.join_assoc, Memory.join_comm.
    econs. memtac. splits; memtac.
  Qed.

  Lemma confirm_src
        inv1 inv2 promise1_src promise1_tgt
        loc from to msg
        (INV: sem inv1 promise1_src promise1_tgt)
        (CONFIRM: Memory.confirm inv1 loc from to msg inv2):
    exists (LT: Time.lt from to) promise2_src,
      <<CONFIRM: Memory.confirm promise1_src loc from to msg promise2_src>> /\
      <<INV: sem inv2 promise2_src promise1_tgt>>.
  Proof.
    inv INV. inv CONFIRM. memtac.
    exists LT. eexists. splits; memtac.
    rewrite Memory.join_assoc. econs; memtac. splits; memtac.
  Qed.

  Lemma confirm
        inv
        loc from to msg
        promise1_src global1_src
        promise1_tgt global1_tgt promise2_tgt
        (LE1_SRC: Memory.le promise1_src global1_src)
        (LE1_TGT: Memory.le promise1_tgt global1_tgt)
        (SIM1: sim_memory global1_src global1_tgt)
        (INV1: sem inv promise1_src promise1_tgt)
        (CONFIRM_TGT: Memory.confirm promise1_tgt loc from to msg promise2_tgt):
    exists promise2_src,
      <<LE1_SRC: Memory.le promise2_src global1_src>> /\
      <<INV2: sem inv promise2_src promise2_tgt>> /\
      <<CONFIRM_SRC: Memory.confirm promise1_src loc from to msg promise2_src>>.
  Proof.
    exploit confirm_tgt; eauto. i. des.
    exploit confirm_src; eauto.
    { econs; eauto. }
    i. des.
    exploit Memory.confirm_future; try apply CONFIRM; eauto.
  Qed.

  Lemma add
        inv
        loc from to msg
        promise1_src global1_src
        promise1_tgt global1_tgt promise2_tgt global2_tgt
        (LE1_SRC: Memory.le promise1_src global1_src)
        (LE1_TGT: Memory.le promise1_tgt global1_tgt)
        (SIM1: sim_memory global1_src global1_tgt)
        (INV1: sem inv promise1_src promise1_tgt)
        (ADD_TGT: Memory.add promise1_tgt global1_tgt loc from to msg promise2_tgt global2_tgt):
    exists (LT: Time.lt from to) promise2_src global2_src,
      <<LE1_SRC: Memory.le promise2_src global2_src>> /\
      <<SIM2: sim_memory global2_src global2_tgt>> /\
      <<DISJOINT: Memory.disjoint inv (Memory.singleton loc msg LT)>> /\
      <<INV2: sem (Memory.join inv (Memory.singleton loc msg LT)) promise2_src promise2_tgt>> /\
      <<PROMISE_SRC: Memory.promise promise1_src global1_src loc from to msg promise2_src global2_src>>.
  Proof.
    inv ADD_TGT.
    exploit promise; try apply SIM1; eauto. i. des.
    exploit confirm_tgt; try apply SIM2; eauto. i. des.
    eexists _, _, _. splits; eauto.
  Qed.

  Lemma write
        inv
        loc from to msg ord
        promise1_src global1_src
        promise1_tgt global1_tgt promise2_tgt global2_tgt
        (LE1_SRC: Memory.le promise1_src global1_src)
        (LE1_TGT: Memory.le promise1_tgt global1_tgt)
        (SIM1: sim_memory global1_src global1_tgt)
        (INV1: sem inv promise1_src promise1_tgt)
        (RELEASE: Ordering.le Ordering.release ord -> promise1_tgt loc = Cell.bot -> promise1_src loc = Cell.bot)
        (WRITE_TGT: Memory.write promise1_tgt global1_tgt loc from to msg ord promise2_tgt global2_tgt):
    exists promise2_src global2_src,
      <<LE1_SRC: Memory.le promise2_src global2_src>> /\
      <<SIM2: sim_memory global2_src global2_tgt>> /\
      <<INV2: sem inv promise2_src promise2_tgt>> /\
      <<WRITE_SRC: Memory.write promise1_src global1_src loc from to msg ord promise2_src global2_src>>.
  Proof.
    inv WRITE_TGT.
    - exploit confirm; try apply SIM1; eauto. i. des.
      eexists _, _. splits; try apply INV2; eauto.
      econs 1; eauto.
    - exploit add; try apply SIM1; eauto. i. des.
      exploit confirm_src; eauto.
      { econs; eauto. }
      i. des.
      eexists _, _. splits; try apply INV; eauto.
      + eapply Memory.confirm_future; eauto.
      + econs 2; eauto. econs; eauto.
  Qed.

  Lemma sem_bot promise:
    sem Memory.bot promise promise.
  Proof.
    rewrite <- (Memory.bot_join promise) at 1.
    econs. memtac.
  Qed.

  Lemma sem_bot_inv
        promise_src promise_tgt
        (SEM: sem Memory.bot promise_src promise_tgt):
    promise_src = promise_tgt.
  Proof.
    inv SEM. apply Memory.bot_join.
  Qed.
End MemInv.
