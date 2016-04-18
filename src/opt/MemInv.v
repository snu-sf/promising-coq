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

  Inductive sem (inv:t): forall (local_src local_tgt:Memory.t), Prop :=
  | sem_intro
      local_tgt
      (DISJOINT: Memory.disjoint local_tgt inv):
      sem inv (Memory.join local_tgt inv) local_tgt
  .

  Lemma add
        inv
        local1_src global1_src
        local1_tgt global1_tgt local2_tgt global2_tgt
        (LE1_SRC: Memory.le local1_src global1_src)
        (LE1_TGT: Memory.le local1_tgt global1_tgt)
        (SIM1: sim_memory global1_src global1_tgt)
        (INV1: sem inv local1_src local1_tgt)
        (ADD_TGT: Memory.add local1_tgt global1_tgt local2_tgt global2_tgt):
    exists local2_src global2_src,
      <<LE1_SRC: Memory.le local2_src global2_src>> /\
      <<SIM2: sim_memory global2_src global2_tgt>> /\
      <<INV2: sem inv local2_src local2_tgt>> /\
      <<ADD_SRC: Memory.add local1_src global1_src local2_src global2_src>>.
  Proof.
    inv SIM1. inv INV1. inv ADD_TGT. memtac.
    rewrite <- Memory.join_assoc in SPLITS.
    apply Memory.splits_join_inv in SPLITS; memtac.
    exploit Memory.join2_splits; try apply JOINC; memtac.
    { splits; memtac. }
    { eapply Memory.splits_disjoint; [|eauto].
      symmetry. eapply Memory.splits_disjoint; [|eauto].
      memtac.
    }
    i. des. subst. clear JOINC SPLITSA.
    exists (Memory.join local2_tgt inv).
    exists (Memory.join (Memory.join (Memory.join local2_tgt inv) addendum) ohs0).
    splits.
    - rewrite <- Memory.join_assoc.
      econs; memtac. repeat (splits; memtac).
      eapply Memory.splits_disjoint in SPLITSB; memtac.
    - econs.
      rewrite <- ? Memory.join_assoc.
      apply Memory.splits_join; (repeat (splits; memtac)).
      rewrite (Memory.join_comm _ ohs0).
      rewrite Memory.join_assoc.
      apply Memory.splits_join; (repeat (splits; memtac)).
    - econs. memtac.
    - rewrite <- (Memory.join_assoc _ addendum ohs0).
      rewrite (Memory.join_comm addendum ohs0).
      rewrite (Memory.join_assoc _ ohs0 addendum).
      econs; (repeat (splits; memtac)).
      + apply Memory.splits_join; (repeat (splits; memtac)).
      + eapply Memory.splits_disjoint in SPLITSB; memtac.
      + eapply Memory.splits_disjoint in SPLITSB; memtac.
  Qed.

  Lemma remove_tgt
        inv local1_src local1_tgt local2_tgt
        loc from to msg
        (INV: sem inv local1_src local1_tgt)
        (REMOVE: Memory.remove loc from to msg local1_tgt local2_tgt):
    exists (LT: Time.lt from to),
      <<DISJOINT: Memory.disjoint inv (Memory.singleton loc msg LT)>> /\
      <<INV: sem (Memory.join inv (Memory.singleton loc msg LT)) local1_src local2_tgt>>.
  Proof.
    inv INV. memtac.
    exists LT. splits; memtac.
    rewrite <- Memory.join_assoc, Memory.join_comm.
    econs. memtac. splits; memtac.
  Qed.

  Lemma remove_src
        inv1 inv2 local1_src local1_tgt
        loc from to msg
        (INV: sem inv1 local1_src local1_tgt)
        (REMOVE: Memory.remove loc from to msg inv1 inv2):
    exists (LT: Time.lt from to) local2_src,
      <<REMOVE: Memory.remove loc from to msg local1_src local2_src>> /\
      <<INV: sem inv2 local2_src local1_tgt>>.
  Proof.
    inv INV. memtac.
    exists LT. eexists. splits; memtac.
    rewrite Memory.join_assoc. econs; memtac. splits; memtac.
  Qed.

  Lemma sem_bot local:
    sem Memory.bot local local.
  Proof.
    rewrite <- (Memory.bot_join local) at 1.
    econs. memtac.
  Qed.

  Lemma sem_bot_inv
        local_src local_tgt
        (SEM: sem Memory.bot local_src local_tgt):
    local_src = local_tgt.
  Proof.
    inv SEM. apply Memory.bot_join.
  Qed.
End MemInv.
