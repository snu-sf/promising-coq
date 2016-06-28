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
  apply Memory.max_timemap_spec'; try by apply CLOSED_TGT; auto. i.
  destruct (Time.le_lt_dec (Memory.max_timemap mem_src loc) Time.bot).
  { esplits; eauto. apply CLOSED_TGT. }
  exploit Memory.max_timemap_closed; try apply CLOSED_SRC; eauto.
  instantiate (1 := loc). i. des.
  inv SIM. destruct (COVER loc (Memory.max_timemap mem_src loc)) as [C1 C2].
  exploit C1; eauto.
  { econs; eauto. apply Interval.mem_ub.
    destruct (mem_src loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
    inv x. rewrite H1 in *. inv l.
  }
  i. inv x. inv ITV. destruct msg. ss.
  esplits; eauto.
Qed.

Lemma sim_memory_add
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to val released
      (SRC: Memory.add mem1_src loc from to val released mem2_src)
      (TGT: Memory.add mem1_tgt loc from to val released mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs.
  - econs; i.
    + inv H.
      exploit Memory.add_get_inv; try exact GET; eauto. i. des.
      * subst. exploit Memory.add_get2; try exact TGT; eauto. i.
        econs; eauto.
      * destruct (COVER loc0 ts) as [C1 C2]. exploit C1; eauto.
        { econs; eauto. }
        i. inv x. exploit Memory.add_get1; try exact GET0; eauto. i. econs; eauto.
    + inv H.
      exploit Memory.add_get_inv; try exact GET; eauto. i. des.
      * subst. exploit Memory.add_get2; try exact SRC; eauto. i.
        econs; eauto.
      * destruct (COVER loc0 ts) as [C1 C2]. exploit C2; eauto.
        { econs; eauto. }
        i. inv x. exploit Memory.add_get1; try exact GET0; eauto. i. econs; eauto.
  - i. exploit Memory.add_get_inv; eauto. i. des.
    + inv x3. esplits.
      * eapply Memory.add_get2. eauto.
      * refl.
    + exploit MSG; eauto. i. des.
      esplits; eauto. eapply Memory.add_get1; eauto.
Qed.

Lemma sim_memory_update
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from1 from2 to val released1 released2
      (SRC: Memory.update mem1_src loc from1 from2 to val released1 released2 mem2_src)
      (TGT: Memory.update mem1_tgt loc from1 from2 to val released1 released2 mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs.
  - econs; i.
    + inv H. destruct msg.
      exploit Memory.update_get_inv; try exact GET; eauto. i. des.
      * subst. exploit Memory.update_get2; try exact TGT; eauto. i.
        econs; eauto.
      * destruct (COVER loc0 ts) as [C1 C2]. exploit C1; eauto.
        { econs; eauto. }
        i. inv x. exploit Memory.update_get1; try exact GET0; eauto. i. des.
        { subst. contradict x0. splits; auto.
          exploit Memory.update_get0; try exact SRC; eauto. i.
          destruct (mem1_src loc).(Cell.WF).
          destruct (Time.eq_dec to0 to); auto. exfalso.
          eapply DISJOINT; try exact n; eauto.
        }
        { econs; eauto. }
    + inv H. destruct msg.
      exploit Memory.update_get_inv; try exact GET; eauto. i. des.
      * subst. exploit Memory.update_get2; try exact SRC; eauto. i.
        econs; eauto.
      * destruct (COVER loc0 ts) as [C1 C2]. exploit C2; eauto.
        { econs; eauto. }
        i. inv x. exploit Memory.update_get1; try exact GET0; eauto. i. des.
        { subst. contradict x0. splits; auto.
          exploit Memory.update_get0; try exact TGT; eauto. i.
          destruct (mem1_tgt loc).(Cell.WF).
          destruct (Time.eq_dec to0 to); auto. exfalso.
          eapply DISJOINT; try exact n; eauto.
        }
        { econs; eauto. }
  - i. exploit Memory.update_get_inv; eauto. i. des.
    + subst. esplits.
      * eapply Memory.update_get2. eauto.
      * refl.
    + exploit MSG; eauto. i. des.
      exploit Memory.update_get1; try exact GET0; eauto. i. des.
      * inv x5. esplits; eauto. etrans; eauto.
        inv SRC. inv UPDATE. auto.
      * esplits; eauto.
Qed.

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

Lemma sim_memory_lower
      mem1 loc from to val released1 released2 mem2
      (UPDATE: Memory.update mem1 loc from from to val released1 released2 mem2):
  sim_memory mem2 mem1.
Proof.
  econs.
  - econs; i.
    + inv H. destruct msg.
      exploit Memory.update_get_inv; eauto. i. des.
      * subst. exploit Memory.update_get0; eauto. i.
        econs; eauto.
      * econs; eauto.
    + inv H. destruct msg.
      exploit Memory.update_get1; eauto. i. des.
      * subst. econs; eauto.
      * econs; eauto.
  - i. exploit Memory.update_get1; eauto. i. des.
    + inv x3. esplits; eauto.
      inv UPDATE. inv UPDATE0. auto.
    + esplits; eauto. refl.
Qed.

Lemma sim_memory_promise_lower
      promises1 mem1 loc from to val released1 released2 promises2 mem2
      (PROMISE: Memory.promise promises1 mem1 loc from to val released2 promises2 mem2 (Memory.promise_kind_update from released1)):
  sim_memory mem2 mem1.
Proof.
  inv PROMISE. eapply sim_memory_lower. eauto.
Qed.

Lemma sim_memory_split
      mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1 mem2
      (STEP1: Memory.update mem0 loc ts1 ts2 ts3 val3 released3 released3 mem1)
      (STEP2: Memory.add mem1 loc ts1 ts2 val2 released2 mem2):
  sim_memory mem2 mem0.
Proof.
  econs.
  - econs; i.
    + inv H. destruct msg.
      exploit Memory.update_get0; eauto. i.
      exploit Memory.add_get_inv; eauto. i. des.
      { inv x3. econs; eauto. eapply Interval.le_mem; eauto.
        econs; try refl. inv STEP1. inv UPDATE. left. auto.
      }
      exploit Memory.update_get_inv; eauto. i. des.
      { subst. econs; eauto. eapply Interval.le_mem; eauto.
        econs; try refl. inv STEP1. inv UPDATE. auto.
      }
      econs; eauto.
    + inv H. destruct msg.
      exploit Memory.update_get1; eauto. i. des.
      { inv x3. destruct (Time.le_lt_dec ts ts2).
        - exploit Memory.add_get2; eauto. i.
          econs; eauto. inv ITV. econs; auto.
        - exploit Memory.add_get1; eauto. i.
          econs; eauto. inv ITV. econs; auto.
      }
      exploit Memory.add_get1; eauto. i.
      econs; eauto.
  - i. exploit Memory.update_get1; eauto. i. des.
    + inv x3. exploit Memory.add_get1; eauto. i. esplits; eauto. refl.
    + exploit Memory.add_get1; eauto. i. esplits; eauto. refl.
Qed.
