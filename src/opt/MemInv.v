Require Import RelationClasses.
Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import DenseOrder.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (SPLITS: Memory.splits mem_tgt mem_src)
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation. ii. econs. reflexivity. Qed.
Next Obligation. ii. inv H. inv H0. econs. etrans; eauto. Qed.

Lemma sim_memory_get
      mem_src mem_tgt
      loc from to msg
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.get loc to mem_tgt = Some (from, msg)):
  exists from', Memory.get loc to mem_src = Some (from', msg).
Proof.
  eapply Memory.splits_get; eauto. apply SIM.
Qed.

Module MemInv.
  Definition t := Promises.t.

  Inductive sem (inv:t) (promises_src promises_tgt:Promises.t): Prop :=
  | sem_intro
      (DISJOINT: Promises.disjoint promises_tgt inv)
      (JOIN: promises_src = Promises.join inv promises_tgt)
  .

  Lemma promise
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        (PROMISES_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (WF1_PROMISES_SRC: Memory.closed_promises promises1_src mem1_src)
        (WF1_PROMISES_TGT: Memory.closed_promises promises1_tgt mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISES_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<WF1_PROMISES_SRC: Memory.closed_promises promises2_src mem2_src>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
  Admitted.

  Lemma fulfill_tgt
        inv
        promises1_src
        promises1_tgt mem1_tgt promises2_tgt
        loc from to msg
        (FULFILL_TGT: Memory.fulfill promises1_tgt mem1_tgt loc from to msg promises2_tgt)
        (INV1: sem inv promises1_src promises1_tgt):
    <<DISJOINT: ~ Promises.mem loc to inv>> /\
    <<INV2: sem (Promises.set loc to inv) promises1_src promises2_tgt>>.
  Proof.
    inv INV1. inv FULFILL_TGT.
    splits.
    - ii. eapply DISJOINT; eauto.
    - econs.
      + admit.
      + admit.
  Admitted.

  Lemma fulfill_src
        inv1 inv2
        promises1_src mem1_src
        promises1_tgt
        loc from to msg
        (FULFILL_INV: Memory.fulfill inv1 mem1_src loc from to msg inv2)
        (INV1: sem inv1 promises1_src promises1_tgt):
    exists promises2_src,
      <<FULFILL_SRC: Memory.fulfill promises1_src mem1_src loc from to msg promises2_src>> /\
      <<INV2: sem inv2 promises2_src promises1_tgt>>.
  Proof.
    inv INV1. eexists. splits.
    - inv FULFILL_INV. econs; eauto. admit.
    - econs.
      + admit.
      + admit.
  Admitted.

  Lemma fulfill
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (FULFILL_TGT: Memory.fulfill promises1_tgt mem1_tgt loc from to msg promises2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (WF1_PROMISES_SRC: Memory.closed_promises promises1_src mem1_src)
        (WF1_PROMISES_TGT: Memory.closed_promises promises1_tgt mem1_tgt)
        (WF1_SRC: Memory.closed mem1_src):
    exists promises2_src,
      <<FULFILL_SRC: Memory.fulfill promises1_src mem1_src loc from to msg promises2_src>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<WF1_PROMISES_SRC: Memory.closed_promises promises2_src mem1_src>>.
  Proof.
    exploit fulfill_tgt; eauto. i. des.
    exploit fulfill_src; try apply INV2; eauto.
    { econs.
      - inv FULFILL_TGT. eauto.
      - rewrite Promises.set_o.
        destruct (Loc.eq_dec loc loc); [|congruence].
        destruct (Time.eq_dec to to); [|congruence].
        auto.
    }
    i. des.
    exploit Memory.fulfill_mon; eauto; i.
    { apply Memory.splits_future. apply SIM1. }
    { admit. }
    eexists. splits; eauto.
    - admit.
    - eapply Memory.fulfill_future; eauto.
  Admitted.

  Lemma future
        inv
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (INV1: sem inv promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (WF1_PROMISES_SRC: Memory.closed_promises promises_src mem1_src)
        (WF1_PROMISES_TGT: Memory.closed_promises promises_tgt mem1_tgt)
        (WF2_PROMISES_SRC: Memory.closed_promises promises_src mem2_src):
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_src>> /\
      <<WF2_PROMISES_TGT: Memory.closed_promises promises_tgt mem2_src>>.
  Proof.
    revert INV1 SIM1 WF1_PROMISES_SRC WF1_PROMISES_TGT WF2_PROMISES_SRC.
    revert inv mem1_tgt promises_src promises_tgt.
    induction FUTURE_SRC; i.
    - splits.
      + apply Memory.splits_future. apply SIM1.
      + admit.
    - inv H.
      + admit.
      + eapply IHFUTURE_SRC; eauto.
        * admit.
        * admit.
  Admitted.

  Lemma sem_bot promise:
    sem Promises.bot promise promise.
  Proof.
    econs.
    - admit.
    - admit.
  Admitted.

  Lemma sem_bot_inv
        promises_src promises_tgt
        (SEM: sem Promises.bot promises_src promises_tgt):
    promises_src = promises_tgt.
  Proof.
    inv SEM. admit.
  Admitted.
End MemInv.
