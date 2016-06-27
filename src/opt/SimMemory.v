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
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
    (MSG: forall loc from_tgt to val released_tgt
            (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.mk val released_tgt)),
        exists from_src released_src,
          <<GET: Memory.get loc to mem_src = Some (from_src, Message.mk val released_src)>> /\
          <<RELEASED: Capability.le released_src released_tgt>>)
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation.
  econs; try refl. i. esplits; eauto. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto. i.
  exploit MSG0; eauto. i. des.
  exploit MSG; eauto. i. des.
  esplits; eauto. etrans; eauto.
Qed.


Lemma sim_memory_get
      loc from_tgt to val released_tgt mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.mk val released_tgt)):
  exists from_src released_src,
    <<GET: Memory.get loc to mem_src = Some (from_src, Message.mk val released_src)>> /\
    <<RELEASED: Capability.le released_src released_tgt>>.
Proof.
  eapply SIM. eauto.
Qed.

Lemma sim_memory_max_timemap
      mem_src mem_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt):
  TimeMap.le (Memory.max_timemap mem_src) (Memory.max_timemap mem_tgt).
Proof.
Admitted.

Lemma sim_memory_add
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to val released
      (SRC: Memory.add mem1_src loc from to val released mem2_src)
      (TGT: Memory.add mem1_tgt loc from to val released mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
Admitted.

Lemma sim_memory_update
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from1 from2 to val released1 released2
      (SRC: Memory.update mem1_src loc from1 from2 to val released1 released2 mem2_src)
      (TGT: Memory.update mem1_tgt loc from1 from2 to val released1 released2 mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
Admitted.

Lemma sim_memory_promise
      loc from to val released kind
      promises1_src mem1_src promises2_src mem2_src
      promises1_tgt mem1_tgt promises2_tgt mem2_tgt
      (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released promises2_src mem2_src kind)
      (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to val released promises2_tgt mem2_tgt kind)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv PROMISE_SRC; inv PROMISE_TGT.
  - eapply sim_memory_add; eauto.
  - eapply sim_memory_update; eauto.
Qed.

Lemma sim_memory_closed_timemap
      mem_src mem_tgt
      tm
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_timemap tm mem_tgt):
  Memory.closed_timemap tm mem_src.
Proof.
  ii. exploit TGT; eauto. i. des.
  exploit sim_memory_get; eauto. i. des. eauto.
Qed.

Lemma sim_memory_closed_capability
      mem_src mem_tgt
      capability
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_capability capability mem_tgt):
  Memory.closed_capability capability mem_src.
Proof.
  econs.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
Qed.
