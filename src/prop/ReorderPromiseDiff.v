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
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Set Implicit Arguments.


Lemma reorder_promise_read_diff
      lc1 lc1'
      lc2 lc2'
      mem0
      mem1
      loc1 from1 to1 val1 released1 kind1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc1 mem0 loc1 from1 to1 val1 released1 lc1' mem1 kind1)
      (STEP2: Local.read_step lc2 mem1 loc2 to2 val2 released2 ord2 lc2')
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  <<STEP1: Local.read_step lc2 mem0 loc2 to2 val2 released2 ord2 lc2'>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
  econs; eauto.
Qed.

Lemma reorder_promise_promise_diff
      lc1 lc1'
      lc2 lc2'
      mem0 sc0
      mem1
      mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 released2 kind2
      (STEP1: Local.promise_step lc1 mem0 loc1 from1 to1 val1 released1 lc1' mem1 kind1)
      (STEP2: Local.promise_step lc2 mem1 loc2 from2 to2 val2 released2 lc2' mem2 kind2)
      (LOCAL1: Local.wf lc1 mem0)
      (LOCAL2: Local.wf lc2 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (DISJ: Local.disjoint lc1 lc2)
      (REL_CLOSED: forall promises2' mem1' kind1' (PROMISE1: Memory.promise (Local.promises lc2) mem0 loc2 from2 to2 val2 released2 promises2' mem1' kind1'),
          Memory.closed_opt_view released2 mem1'):
  exists mem1',
    <<STEP1: Local.promise_step lc2 mem0 loc2 from2 to2 val2 released2 lc2' mem1' kind2>> /\
    <<STEP2: Local.promise_step lc1 mem1' loc1 from1 to1 val1 released1 lc1' mem2 kind1>>.
Proof.
  exploit Local.promise_step_disjoint; try exact STEP1; eauto. i. des.
  inv STEP1. inv STEP2. ss.
  inv PROMISE.
  { inv PROMISE0.
    - exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.add_closed_opt_view; eauto.
    - exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des.
      { subst. exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; s; cycle 1.
        - eapply Memory.split_get0. eauto.
        - erewrite Memory.add_o; eauto. condtac; [|des; congr]. ss.
      }
      esplits.
      + econs.
        * econs 2; eauto.
        * eapply REL_CLOSED. econs 2; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.split_closed_opt_view; eauto.
    - exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des.
      { subst. exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; s; cycle 1.
        - eapply Memory.lower_get0. eauto.
        - erewrite Memory.add_o; eauto. condtac; [|des; congr]. ss.
      }
      esplits.
      + econs.
        * econs 3; eauto.
        * eapply REL_CLOSED. econs 3; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.lower_closed_opt_view; eauto.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.split_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.add_closed_opt_view; eauto.
    - exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
      { ii. inv H. exfalso. eapply Memory.disjoint_get; try apply DISJ.
        - eapply Memory.split_get0. eauto.
        - eapply Memory.split_get0. eauto.
      }
      i. des.
      { subst. exfalso. eapply Memory.disjoint_get'; try (symmetry; apply DISJ).
        - inv MEM. inv SPLIT. apply TS12.
        - inv PROMISES. inv SPLIT. apply TS23.
        - eapply Memory.split_get0. eauto.
        - eapply Memory.split_get0. eauto.
      }
      esplits.
      + econs.
        * econs 2; eauto.
        * eapply REL_CLOSED. econs 2; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.split_closed_opt_view; eauto.
    - exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
      { ii. inv H. exfalso. eapply Memory.disjoint_get; try apply DISJ.
        - eapply Memory.split_get0. eauto.
        - eapply Memory.lower_get0. eauto.
      }
      i. des.
      { subst. exfalso. eapply Memory.disjoint_get'; try (symmetry; apply DISJ).
        - inv MEM1. inv LOWER. eauto.
        - inv MEM. inv SPLIT. eauto.
        - eapply Memory.lower_get0. eauto.
        - eapply Memory.split_get0. eauto.
      }
      esplits.
      + econs.
        * econs 3; eauto.
        * eapply REL_CLOSED. econs 3; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.lower_closed_opt_view; eauto.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.lower_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.add_closed_opt_view; eauto.
    - exploit MemoryReorder.lower_split; try exact MEM; try exact MEM0; eauto. i. des.
      unguardH FROM1. des.
      { inv FROM1. exfalso. eapply Memory.disjoint_get; try apply DISJ.
        - eapply Memory.lower_get0. eauto.
        - eapply Memory.split_get0. eauto.
      }
      inv FROM0.
      esplits.
      + econs.
        * econs 2; eauto.
        * eapply REL_CLOSED. econs 2; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.split_closed_opt_view; eauto.
    - exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des.
      { subst. exfalso. eapply Memory.disjoint_get; try apply DISJ.
        - eapply Memory.lower_get0. eauto.
        - eapply Memory.lower_get0. eauto.
      }
      esplits.
      + econs.
        * econs 3; eauto.
        * eapply REL_CLOSED. econs 3; eauto.
      + econs.
        * econs; eauto.
        * eapply Memory.lower_closed_opt_view; eauto.
  }
Qed.

Lemma reorder_promise_write_diff
      lc1 lc1'
      lc2 lc2'
      sc0 mem0
      mem1
      sc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc1 mem0 loc1 from1 to1 val1 released1 lc1' mem1 kind1)
      (STEP2: Local.write_step lc2 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2' sc2 mem2 kind2)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL1: Local.wf lc1 mem0)
      (LOCAL2: Local.wf lc2 mem0)
      (DISJ: Local.disjoint lc1 lc2)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  exists mem1',
    <<STEP1: Local.write_step lc2 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2' sc2 mem1' kind2>> /\
    <<STEP2: Local.promise_step lc1 mem1' loc1 from1 to1 val1 released1 lc1' mem2 kind1>>.
Proof.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.promise_step_disjoint; eauto. i. des.
  exploit write_promise_fulfill; eauto.
  { inv STEP1. eapply Memory.promise_closed_opt_view; eauto. }
  i. des.
  exploit reorder_promise_promise_diff; try exact STEP1; try exact STEP0; eauto.
  { i. subst.
    exploit Memory.promise_op; eauto. i.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    apply LOCAL2.
  }
  i. des.
  esplits; eauto.
  eapply promise_fulfill_write_exact; eauto.
Qed.

Lemma reorder_promise_program_diff
      loc from to val released kind lc1 lc1'
      e2 lang2 st2 st2' lc2 lc2'
      sc0 mem0
      mem1
      sc2 mem2
      (STEP1: Local.promise_step lc1 mem0 loc from to val released lc1' mem1 kind)
      (STEP2: Thread.program_step e2 (Thread.mk lang2 st2 lc2 sc0 mem1) (Thread.mk lang2 st2' lc2' sc2 mem2))
      (E2: forall val released ord, ThreadEvent.is_reading e2 <> Some (loc, to, val, released, ord))
      (LOCAL1: Local.wf lc1 mem0)
      (LOCAL2: Local.wf lc2 mem0)
      (DISJ: Local.disjoint lc1 lc2)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  exists mem1',
    <<STEP1: Thread.program_step e2 (Thread.mk lang2 st2 lc2 sc0 mem0) (Thread.mk lang2 st2' lc2' sc2 mem1')>> /\
    <<STEP2: Local.promise_step lc1 mem1' loc from to val released lc1' mem2 kind>>.
Proof.
  inv STEP2; ss.
  - (* silent *)
    esplits; eauto. econs; eauto.
  - (* read *)
    exploit reorder_promise_read_diff; eauto.
    { ii. inv H. eapply E2. eauto. }
    i. des. esplits; eauto. econs 2; eauto.
  - (* write *)
    exploit reorder_promise_write_diff; eauto; try by viewtac. i. des.
    esplits; eauto. econs 3; eauto.
  - (* update *)
    exploit reorder_promise_read_diff; eauto.
    { ii. inv H. eapply E2. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.read_step_disjoint; try symmetry; eauto. i.
    exploit reorder_promise_write_diff; try symmetry; eauto. i. des.
    esplits; eauto. econs 4; eauto.
  - inv LOCAL.
    esplits; eauto. econs 5; eauto. econs; eauto.
  - inv LOCAL.
    esplits; eauto. econs 6; eauto. econs; eauto.
Qed.
