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
Require Import ThreadView.
Require Import Thread.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Require Import PromiseConsistent.

Set Implicit Arguments.


Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 val1 released1 kind1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 val1 released1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
  + econs; eauto.
  + econs; eauto.
Qed.

Lemma reorder_promise_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 released2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 val2 released2 lc2 mem2 kind2)
      (REL_CLOSED: forall promises1' mem1' kind1' (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 val2 released2 promises1' mem1' kind1'),
          Memory.closed_view released2 mem1')
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' val1' released1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          to1' <> to2 /\ forall val2' released2', kind2 <> Memory.promise_kind_split to1' val2' released2'):
  exists lc1' mem1' kind2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2) = (lc1', mem1') \/
                (exists from1' kind1',
                    (loc1, to1) <> (loc2, to2) /\
                    (forall to1' val1' released1'
                       (LOC: loc1 = loc2)
                       (KIND: kind1' = Memory.promise_kind_split to1' val1' released1'),
                        to1' <> to2 /\ forall val2' released2', kind2 <> Memory.promise_kind_split to1' val2' released2') /\
                    Local.promise_step lc1' mem1' loc1 from1' to1 val1 released1 lc2 mem2 kind1'))>> /\
    <<KIND2: kind2 = Memory.promise_kind_add -> kind2' = Memory.promise_kind_add>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE.
  { inv PROMISE0.
    - exploit MemoryReorder.add_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + right. esplits; eauto.
        refine (Local.step_promise _ _ _); eauto.
        econs; eauto.
        eapply Memory.add_closed_view; eauto.
      + auto.
    - exploit MemoryReorder.add_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs.
          { econs; eauto. }
          { eapply REL_CLOSED. econs; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. inv ADD3. inv ADD. eapply Time.lt_strorder. eauto. }
          { congr. }
        * auto.
      + exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET2. erewrite Memory.add_o; eauto. condtac; ss. des; congr.
          }
          { congr. }
        * auto.
    - exploit MemoryReorder.add_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto. econs; eauto.
        * left. auto.
        * auto.
      + exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs.
          { econs 3; eauto. }
          { eapply REL_CLOSED. econs 3; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs; eauto.
            - eapply Memory.lower_closed_view; eauto.
          }
          { auto. }
          { congr. }
        * auto.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.split_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + right. esplits; eauto; cycle 1.
        refine (Local.step_promise _ _ _); eauto.
        econs 2; eauto.
        eapply Memory.add_closed_view; eauto.
      + auto.
    - exploit MemoryReorder.split_split; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. eapply LOCTS; eauto. }
      i. des.
      + subst. exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. inv SPLIT2. inv SPLIT. eapply Time.lt_strorder. eauto. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 2; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. inv SPLIT2. inv SPLIT. eapply Time.lt_strorder. eauto. }
          { i. inv KIND. splits.
            - ii. subst. inv SPLIT2. inv SPLIT. eapply Time.lt_strorder. etrans; try exact TS12; eauto.
            - ii. inv H. inv SPLIT3. inv SPLIT. eapply Time.lt_strorder. eauto.
          }
        * congr.
      + exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. eapply LOCTS; eauto. }
        i. des; [congr|].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 2; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET2. erewrite Memory.split_o; eauto. repeat condtac; ss.
            guardH o0. des; congr.
          }
          { i. inv KIND. splits.
            - ii. subst. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
              revert GET2. erewrite Memory.split_o; eauto. repeat condtac; ss.
              guardH o. des; congr.
            - ii. inv H. eapply LOCTS; eauto.
          }
        * auto.
    - exploit MemoryReorder.split_lower; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
      i. des.
      + subst. exploit MemoryReorder.split_lower; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
        i. des; [|congr].
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * left. auto.
        * congr.
      + subst. exploit MemoryReorder.split_lower; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
        i. des; [congr|].
        esplits.
        * econs.
          { econs 3; eauto. }
          { eapply REL_CLOSED. econs 3; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 2; eauto.
            - eapply Memory.lower_closed_view; eauto.
          }
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. }
          { i. inv KIND. splits.
            - ii. subst. exploit LOCTS; eauto. i. des. congr.
            - ii. inv H.
          }
        * congr.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.lower_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs.
        * econs; eauto.
        * eapply REL_CLOSED. econs; eauto.
      + right. esplits; eauto.
        refine (Local.step_promise _ _ _); eauto.
        econs; eauto.
        eapply Memory.add_closed_view; eauto.
      + auto.
    - exploit MemoryReorder.lower_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_split; try exact MEM; try exact MEM0; eauto. i. des.
      unguardH FROM1. des.
      + inv FROM1. unguardH FROM0. des; [|congr]. inv FROM0.
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 3; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. inv SPLIT1. inv SPLIT.
            exfalso. eapply Time.lt_strorder. eauto.
          }
          { auto. }
        * congr.
      + inv FROM2. unguardH FROM0. des; [congr|]. inv FROM2.
        esplits.
        * econs.
          { econs 2; eauto. }
          { eapply REL_CLOSED. econs 2; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 3; eauto.
            - eapply Memory.split_closed_view; eauto.
          }
          { ii. inv H. exploit Memory.lower_get0; try exact MEM; eauto.
            exploit Memory.split_get0; try exact SPLIT0; eauto. i. des. congr.
          }
          { congr. }
        * auto.
    - exploit MemoryReorder.lower_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto. econs 3; eauto.
        * left. auto.
        * congr.
      + exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs.
          { econs 3; eauto. }
          { eapply REL_CLOSED. econs 3; eauto. }
        * right. esplits; cycle 2.
          { refine (Local.step_promise _ _ _); eauto.
            - econs 3; eauto.
            - eapply Memory.lower_closed_view; eauto.
          }
          { auto. }
          { auto. }
        * auto.
  }
Qed.

Lemma reorder_promise_fulfill
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS1: (loc1, to1) <> (loc2, to2))
      (LOCTS2: forall to1' val1' released1'
                 (LOC: loc1 = loc2)
                 (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          to1' <> to2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 val1 released1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE.
  - exploit MemoryReorder.add_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.split_remove; try exact PROMISES; try exact REMOVE; eauto.
    { ii. inv H. eapply LOCTS2; eauto. }
    i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.lower_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
Qed.

Lemma reorder_promise_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (REL_WF: View.wf releasedm2)
      (REL_CLOSED: Memory.closed_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' val1' released1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          to1' <> to2 /\ forall val2' released2', kind2 <> Memory.promise_kind_split to1' val2' released2'):
  exists kind2' lc1' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2) = (lc1', mem1') \/
                ((loc1, to1) <> (loc2, to2) /\
                 exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 val1 released1 lc2 mem2 kind1'>>))>> /\
    <<KIND2: kind2 = Memory.promise_kind_add -> kind2' = Memory.promise_kind_add>>.
Proof.
  exploit Local.promise_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto; try by viewtac. i. des.
  exploit reorder_promise_promise; try exact STEP1; eauto.
  { i. subst. eapply Local.promise_closed_view; try exact PROMISE1; try apply LOCAL0; eauto.
    inv STEP1. apply LOCAL0.
  }
  i. des.
  unguardH STEP5. des.
  - inv STEP5.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto.
    { i. exploit ORD; eauto. i. des. splits; auto.
      apply Cell.ext. i. rewrite Cell.bot_get.
      destruct (Cell.get ts (Local.promises lc0 loc2)) as [[? []]|] eqn:X; auto.
      inv STEP1. exploit Memory.promise_promises_get1; eauto. i. des.
      ss. unfold Memory.get in GET. rewrite x, Cell.bot_get in *. congr.
    }
    { condtac; [|auto]. do 3 f_equal. inv STEP1. ss. }
    i. esplits; eauto. left; eauto.
  - exploit Local.promise_step_future; try exact STEP4; eauto. i. des.
    exploit reorder_promise_fulfill; try exact STEP6; eauto.
    { i. eapply STEP6; eauto. }
    i. des.
    exploit fulfill_step_future; try exact STEP7; try exact WF0; eauto; try by viewtac. i. des.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto; try by viewtac.
    { i. exploit ORD; eauto. i. des. splits; auto.
      apply Cell.ext. i. rewrite Cell.bot_get.
      destruct (Cell.get ts (Local.promises lc0 loc2)) as [[? []]|] eqn:X; auto.
      inv STEP1. exploit Memory.promise_promises_get1; eauto. i. des.
      ss. unfold Memory.get in GET. rewrite x, Cell.bot_get in *. congr.
    }
    { condtac; [|auto]. do 3 f_equal. inv STEP1. ss. }
    i. esplits; eauto. right. esplits; eauto.
Qed.

Lemma reorder_promise_write'
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (REL_WF: View.wf releasedm2)
      (REL_CLOSED: Memory.closed_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  (loc1 = loc2 /\ Time.lt to1 to2) \/
  (exists kind2' lc1' mem1',
     <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
     <<STEP2: __guard__
                ((lc2, mem2) = (lc1', mem1') \/
                 ((loc1, to1) <> (loc2, to2) /\
                  exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 val1 released1 lc2 mem2 kind1'>>))>> /\
     <<KIND2: kind2 = Memory.promise_kind_add -> kind2' = Memory.promise_kind_add>>).
Proof.
  destruct (classic (loc1 = loc2 /\ Time.lt to1 to2)); auto.
  right. eapply reorder_promise_write; eauto. i. subst. splits.
  - ii. subst. apply H. splits; auto.
    inv STEP1. inv PROMISE. inv MEM. inv SPLIT. auto.
  - ii. subst. apply H. splits; auto.
    inv STEP2. inv WRITE. inv PROMISE. exploit Memory.split_get0; eauto. i. des.
    inv STEP1. inv PROMISE. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + i. des. inv GET3. inv MEM1. inv SPLIT.
      exfalso. eapply Time.lt_strorder. eauto.
    + guardH o. i. des. inv GET3. inv MEM. inv SPLIT. auto.
    + guardH o. des; congr.
Qed.

Lemma reorder_promise_program
      lang
      e1 e2 th0 th1 th2
      (STEP1: @Thread.promise_step lang e1 th0 th1)
      (STEP2: @Thread.program_step lang e2 th1 th2)
      (CONS2: promise_consistent th2.(Thread.local))
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  exists th1',
     <<STEP1: @Thread.program_step lang e2 th0 th1'>> /\
     <<STEP2: __guard__ (th2 = th1' \/ exists e2', @Thread.promise_step lang e2' th1' th2)>>.
Proof.
  exploit Thread.promise_step_future; eauto. i. des.
  inv STEP1. inv STEP2; ss.
  - (* silent *)
    esplits; eauto.
    right. esplits. econs. eauto.
  - (* read *)
    exploit reorder_promise_read; try exact LOCAL0; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto. i.
      exploit promise_consistent_promise_read; eauto. i.
      eapply Time.lt_strorder. eauto.
    }
    i. des. esplits.
    + econs 2; eauto.
    + right. esplits. econs; eauto.
  - (* write *)
    exploit reorder_promise_write'; try exact LOCAL0; eauto; try by viewtac. i. des.
    { subst. inv LOCAL0. exploit Memory.promise_get2; eauto. i.
      exploit promise_consistent_promise_write; eauto. i.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    }
    esplits.
    + econs 3; eauto.
    + unguardH STEP2. des.
      * inv STEP2. left. auto.
      * right. esplits. econs; eauto.
  - (* update *)
    exploit reorder_promise_read; try exact LOCAL1; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto. i.
      exploit promise_consistent_promise_read; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. eapply Time.lt_strorder. eauto.
    }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit reorder_promise_write'; try exact LOCAL2; eauto; try by viewtac. i. des.
    { subst. inv STEP2. exploit Memory.promise_get2; eauto. i.
      exploit promise_consistent_promise_write; eauto. i.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    }
    i. des. esplits.
    + econs 4; eauto.
    + unguardH STEP3. des.
      * inv STEP3. left. auto.
      * right. esplits. econs; eauto.
  - inv LOCAL0. inv LOCAL1.
    esplits; eauto.
    + econs 5; eauto. econs; eauto.
    + right. esplits. econs. econs; eauto.
  - inv LOCAL0. inv LOCAL1.
    esplits; eauto.
    + econs 6; eauto. econs; eauto.
    + right. esplits. econs. econs; eauto.
Qed.
