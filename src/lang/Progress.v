Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import Commit.
Require Import Thread.

Set Implicit Arguments.


Lemma write_step_promise
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP. rewrite PROMISES in *. s.
  apply Memory.ext. i.
  inv WRITE.
  erewrite MemoryFacts.remove_o; eauto.
  inv PROMISE.
  - erewrite MemoryFacts.add_o; eauto. condtac; ss.
    rewrite Memory.bot_get. auto.
  - erewrite MemoryFacts.update_o; eauto. condtac; ss.
    rewrite Memory.bot_get. auto.
Qed.

Lemma program_step_promise
      lang e
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP; (try by inv LOCAL); eauto.
  - eapply write_step_promise; eauto.
  - eapply write_step_promise; eauto.
    inv LOCAL1. auto.
Qed.

Lemma closed_timemap_max_ts
      loc tm mem
      (CLOSED: Memory.closed_timemap tm mem):
  Time.le (tm loc) (Memory.max_ts loc mem).
Proof.
  specialize (CLOSED loc). des.
  eapply Memory.max_ts_spec. eauto.
Qed.

Lemma progress_promise_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (WF_REL: Capability.wf releasedm)
      (CLOSED_REL: Memory.closed_capability releasedm mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc (Memory.max_ts loc mem1) to val
                       (Capability.join
                          releasedm
                          (Commit.rel
                             (Commit.write_commit (Local.commit lc1) sc1 loc to ord) loc))
                       (Local.mk lc1.(Local.commit) promises2) mem2 Memory.promise_kind_add.
Proof.
  exploit (@Memory.add_exists_max_ts mem1 loc to val (Capability.join releasedm (Commit.rel (Commit.write_commit (Local.commit lc1) sc1 loc to ord) loc))); eauto.
  { committac; try apply WF1. repeat condtac; committac; try apply WF1. }
  i. des.
  exploit Memory.add_exists_le; try apply WF1; eauto. i. des.
  assert (FUTURE: Memory.future mem1 mem2).
  { econs 2; [|econs 1]. econs 1. eauto. }
  hexploit Memory.add_inhabited; try apply x0; [committac|]. i. des.
  esplits. econs.
  - econs; eauto.
    committac; repeat (condtac; committac);
      (try by apply Time.bot_spec);
      (try by unfold TimeMap.singleton, LocFun.add; condtac; [refl|congr]);
      (try by left; eapply TimeFacts.le_lt_lt; [|eauto];
       eapply closed_timemap_max_ts; apply WF1).
    left. eapply TimeFacts.le_lt_lt; [|eauto].
    eapply closed_timemap_max_ts. apply CLOSED_REL.
  - committac;
      repeat condtac; committac;
        (try eapply Memory.future_closed_capability; eauto);
        (try apply WF1).
    + eapply Memory.add_get2. eauto.
    + econs; try apply Memory.closed_timemap_bot; committac.
    + eapply Memory.add_get2. eauto.
Qed.

Lemma progress_read_step
      lc1 mem1
      loc ord
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists val released lc2,
    Local.read_step lc1 mem1 loc (Memory.max_ts loc mem1) val released ord lc2.
Proof.
  exploit (Memory.max_ts_spec loc); try apply MEM1; eauto. i. des.
  esplits; eauto. econs; eauto.
  econs; try by i; eapply Memory.max_ts_spec2; apply WF1.
  i. eapply Memory.max_ts_spec2. eapply MEM1. eauto.
Qed.

Lemma progress_write_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (WF_REL: Capability.wf releasedm)
      (CLOSED_REL: Memory.closed_capability releasedm mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists released lc2 sc2 mem2,
    Local.write_step lc1 sc1 mem1 loc (Memory.max_ts loc mem1) to val releasedm released ord lc2 sc2 mem2 Memory.promise_kind_add.
Proof.
  exploit progress_promise_step; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des. inv x0.
  assert (PROMISES2:
            promises2 = Memory.singleton
                          loc val
                          (Capability.join releasedm (Commit.rel (Commit.write_commit (Local.commit lc1) sc1 loc to ord) loc))
                          LT).
  { apply Memory.ext. i.
    inv PROMISE. erewrite MemoryFacts.add_o; eauto.
    rewrite PROMISES1, Memory.bot_get, Memory.singleton_get.
    repeat (condtac; unfold fst, snd in *; des; subst; auto; try congr).
  }
  esplits. econs; eauto.
  - econs; i; (try eapply TimeFacts.le_lt_lt; [|eauto]).
    + apply Memory.max_ts_spec2. apply WF1.
    + apply Memory.max_ts_spec2. apply WF1.
    + apply Memory.max_ts_spec2. auto.
  - econs; eauto. subst promises2. apply Memory.remove_singleton.
  - rewrite PROMISES1. auto.
Qed.

Lemma progress_fence_step
      lc1 sc1
      ordr ordw
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists lc2 sc2,
    Local.fence_step lc1 sc1 ordr ordw lc2 sc2.
Proof.
  esplits. econs; eauto.
Qed.
