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
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryFacts.
  Lemma merge_add_update_add
        mem0 loc from1 from2 to val released1 released2 mem1 mem2
        (ADD1: Memory.add mem0 loc from1 to val released1 mem1)
        (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
    Memory.add mem0 loc from2 to val released2 mem2.
  Proof.
    inv ADD1. inv ADD. inv UPDATE2. inv UPDATE.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.add, Cell.update in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto. i.
    hexploit DISJOINT; eauto. ii. eapply H; eauto.
    eapply Interval.le_mem; try eexact LHS; eauto. econs; eauto. refl.
  Qed.

  Lemma merge_update_update_update
        mem0 loc from0 from1 from2 to val released0 released1 released2 mem1 mem2
        (UPDATE1: Memory.update mem0 loc from0 from1 to val released0 released1 mem1)
        (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
    Memory.update mem0 loc from0 from2 to val released0 released2 mem2.
  Proof.
    inv UPDATE1. inv UPDATE. inv UPDATE2. inv UPDATE.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.update in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
    - etrans; eauto.
    - etrans; eauto.
  Qed.

  Lemma merge_promise_promise_promise
        loc from1 from2 to val released1 released2 promises0 promises1 promises2 mem0 mem1 mem2 kind
        (PROMISE1: Memory.promise promises0 mem0 loc from1 to val released1 promises1 mem1 kind)
        (PROMISE2: Memory.promise promises1 mem1 loc from2 to val released2 promises2 mem2 (Memory.promise_kind_update from1 released1)):
    Memory.promise promises0 mem0 loc from2 to val released2 promises2 mem2 kind.
  Proof.
    inv PROMISE2. inv PROMISE1.
    - econs; eauto.
      + eapply merge_add_update_add; eauto.
      + eapply merge_add_update_add; eauto.
    - econs; eauto.
      + eapply merge_update_update_update; eauto.
      + eapply merge_update_update_update; eauto.
  Qed.

  Lemma split_remove_update_remove
        mem0 loc from1 from2 to val released1 released2 mem2
        (REL_LE: Capability.le released2 released1)
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REMOVE: Memory.remove mem0 loc from1 to val released1 mem2):
    exists mem1',
      <<UPDATE: Memory.update mem0 loc from1 from2 to val released1 released2 mem1'>> /\
      <<REMOVE: Memory.remove mem1' loc from2 to val released2 mem2>>.
  Proof.
    exploit Memory.remove_get0; eauto. i.
    inv REMOVE. inv REMOVE0.
    erewrite <- LocFun.add_add_eq.
    destruct r. ss. subst.
    esplits.
    - econs. instantiate (1 := Cell.mk _). econs; eauto.
    - econs; eauto. unfold LocFun.add. condtac; [|congr].
      unfold Cell.remove. s.
      replace (DOMap.remove to (Cell.raw (mem0 loc))) with
      (DOMap.remove to
                    (DOMap.add to
                               (from2,
                                {|
                                  Message.val := val;
                                  Message.released := released2 |})
                               (Cell.raw (mem0 loc)))).
      + econs. rewrite DOMap.gss. auto.
      + apply DOMap.eq_leibniz. ii.
        rewrite ? DOMap.grspec, DOMap.gsspec. condtac; auto.
        Grab Existential Variables.
        { eapply Cell.Raw.update_wf; eauto.
          - econs; eauto.
          - apply mem0.
        }
  Qed.

  Lemma split_remove_promise_remove
        promises0 mem0 loc from1 from2 to val released1 released2 promises2
        (PROMISES: Memory.le promises0 mem0)
        (REL_LE: Capability.le released2 released1)
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (REL_TO: Time.le (Capability.rw released1 loc) to)
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REMOVE: Memory.remove promises0 loc from1 to val released1 promises2):
    exists promises1' mem1',
      <<PROMISE: Memory.promise promises0 mem0 loc from2 to val released2 promises1' mem1' (Memory.promise_kind_update from1 released1)>> /\
      <<REMOVE: Memory.remove promises1' loc from2 to val released2 promises2>>.
  Proof.
    exploit split_remove_update_remove; eauto. i. des.
    exploit Memory.update_exists_le; eauto. i. des.
    esplits; eauto.
    - econs; eauto. etrans; eauto. apply REL_LE.
  Qed.

  Lemma reorder_remove_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2)
        (ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.add_get1; try eexact ADD1; eauto. i.
    exploit Memory.remove_exists; try eexact x1; eauto. i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    destruct (Memory.get loc ts mem3) as [[? []]|] eqn:X.
    { exploit Memory.remove_get_inv; try eexact x2; eauto. i. des.
      exploit Memory.add_get_inv; try eexact ADD1; eauto. i. des.
      { inv x8. symmetry. eapply Memory.add_get2; eauto. }
      exploit Memory.remove_get1; try eexact REMOVE1; eauto. i. des.
      { inv x10. contradict x3. auto. }
      symmetry. eapply Memory.add_get1; eauto.
    }
    destruct (Memory.get loc ts mem2) as [[? []]|] eqn:Y.
    { exploit Memory.add_get_inv; try eexact ADD2; eauto. i. des.
      { inv x6. exploit Memory.add_get2; try eexact ADD1; eauto. i.
        exploit Memory.remove_get1; try eexact x2; eauto. i. des; [|congr].
        inv x7. exploit Memory.add_get0; try eexact ADD1; eauto. i. congr.
      }
      exploit Memory.remove_get_inv; try eexact REMOVE1; eauto. i. des.
      exploit Memory.add_get1; try eexact ADD1; eauto. i.
      exploit Memory.remove_get1; try eexact x2; eauto. i. des; [|congr].
      inv x11. contradict x5. auto.
    }
    auto.
  Qed.

  Lemma reorder_remove_update
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2' from2 to2 val2 released2' released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (UPDATE2: Memory.update mem1 loc2 from2' from2 to2 val2 released2' released2 mem2)
        (UPDATE1: Memory.update mem0 loc2 from2' from2 to2 val2 released2' released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.update_get1; try eexact UPDATE1; eauto. i. des.
    { inv x4. exploit Memory.remove_get2; try eexact REMOVE1; eauto. i.
      exploit Memory.update_get0; try eexact UPDATE2; eauto. i. congr.
    }
    exploit Memory.remove_exists; try eexact x2; eauto. i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    destruct (Memory.get loc ts mem3) as [[? []]|] eqn:X.
    { exploit Memory.remove_get_inv; try eexact x3; eauto. i. des.
      exploit Memory.update_get_inv; try eexact UPDATE1; eauto. i. des.
      { inv x8. symmetry. eapply Memory.update_get2; eauto. }
      exploit Memory.remove_get1; try eexact REMOVE1; eauto. i. des.
      { inv x10. contradict x3. auto. }
      symmetry. exploit Memory.update_get1; try eexact UPDATE2; eauto. i. des; auto.
      inv x12. contradict x6. auto.
    }
    destruct (Memory.get loc ts mem2) as [[? []]|] eqn:Y.
    { exploit Memory.update_get_inv; try eexact UPDATE2; eauto. i. des.
      { subst. exploit Memory.update_get2; try eexact UPDATE1; eauto. i.
        exploit Memory.remove_get1; try eexact x3; eauto. i. des; [|congr].
        inv x8. contradict x1. auto.
      }
      exploit Memory.remove_get_inv; try eexact REMOVE1; eauto. i. des.
      exploit Memory.update_get1; try eexact UPDATE1; eauto. i. des.
      { inv x11. contradict x4. auto. }
      exploit Memory.remove_get1; try eexact x3; eauto. i. des; [|congr].
      inv x13. contradict x6. auto.
    }
    auto.
  Qed.

  Lemma reorder_remove_promise
        promises1 loc1 from1 to1 val1 released1
        promises2 loc2 from2 to2 val2 released2
        promises3
        mem1 mem3
        kind
        (LE: Memory.le promises1 mem1)
        (REMOVE: Memory.remove promises1 loc1 from1 to1 val1 released1 promises2)
        (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 val2 released2 promises3 mem3 kind):
    exists promises2',
      Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2' mem3 kind /\
      Memory.remove promises2' loc1 from1 to1 val1 released1 promises3.
  Proof.
    inv PROMISE.
    - exploit Memory.add_exists_le; eauto. i. des.
      exploit reorder_remove_add; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.update_get0; try eexact PROMISES; eauto. i.
      exploit Memory.remove_get_inv; try eexact REMOVE; eauto. i. des.
      exploit Memory.update_exists; eauto; try by inv PROMISES; inv UPDATE; eauto. i. des.
      exploit reorder_remove_update; eauto. i.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma reorder_promise_promise
        promises1 mem1 loc1 from1 to1 val1 released1 kind1
        promises2 mem2 loc2 from2 to2 val2 released2 kind2
        promises3 mem3
        (LE: Memory.le promises1 mem1)
        (PROMISE1: Memory.promise promises1 mem1 loc1 from1 to1 val1 released1 promises2 mem2 kind1)
        (PROMISE2: Memory.promise promises2 mem2 loc2 from2 to2 val2 released2 promises3 mem3 kind2):
    exists promises2' mem2',
      <<PROMISE1: Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2' mem2' kind2>> /\
      <<PROMISE2: Memory.promise promises2' mem2' loc1 from1 to1 val1 released1 promises3 mem3 kind1>>.
  Proof.
  Admitted. (* reorder promise & promise; WRONG: need a condition *)

  Lemma reorder_remove_remove
        promises0 loc1 from1 to1 val1 released1
        promises1 loc2 from2 to2 val2 released2
        promises2
        (REMOVE1: Memory.remove promises0 loc1 from1 to1 val1 released1 promises1)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<REMOVE2: Memory.remove promises1' loc1 from1 to1 val1 released1 promises2>>.
  Proof.
    exploit Memory.remove_get0; try apply REMOVE2; eauto. i.
    exploit Memory.remove_get_inv; try apply REMOVE1; eauto. i. des.
    exploit Memory.remove_exists; eauto. i. des.
    exploit Memory.remove_get0; try apply REMOVE1; eauto. i.
    exploit Memory.remove_get1; try apply x3; eauto. i. des; [by contradict x1|].
    exploit Memory.remove_exists; eauto. i. des.
    cut (mem0 = promises2).
    { esplits; subst; eauto. }
    apply Memory.ext. i.
    destruct (Memory.get loc ts mem0) as [[]|] eqn:X.
    { exploit Memory.remove_get_inv; try apply x6; eauto. i. des.
      exploit Memory.remove_get_inv; try apply x3; eauto. i. des.
      exploit Memory.remove_get1; try apply REMOVE1; eauto. i. des; [by contradict x7|].
      exploit Memory.remove_get1; try apply REMOVE2; eauto. i. des; [by contradict x9|].
      auto.
    }
    destruct (Memory.get loc ts promises2) as [[]|] eqn:Y.
    { exploit Memory.remove_get_inv; try apply REMOVE2; eauto. i. des.
      exploit Memory.remove_get_inv; try apply REMOVE1; eauto. i. des.
      exploit Memory.remove_get1; try apply x3; eauto. i. des; [by contradict x7|].
      exploit Memory.remove_get1; try apply x6; eauto. i. des; [by contradict x9|].
      congr.
    }
    auto.
  Qed.  

  Lemma promise_time_lt
        promises1 mem1 loc from to val released promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
    Time.lt from to.
  Proof.
    inv PROMISE.
    - inv MEM. inv ADD. auto.
    - inv MEM. inv UPDATE. auto.
  Qed.

  Lemma write_time_lt
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind):
    Time.lt from to.
  Proof.
    inv WRITE. eapply promise_time_lt. eauto.
  Qed.

  Lemma promise_get1_diff
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: Memory.get l t mem1 = Some (f, Message.mk v r))
        (DIFF: (loc, to) <> (l, t)):
    Memory.get l t mem2 = Some (f, Message.mk v r).
  Proof.
    inv PROMISE.
    - exploit Memory.add_get1; eauto.
    - exploit Memory.update_get1; eauto. i. des; auto.
      inv x3. congr.
  Qed.

  Lemma promise_get_inv_diff
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: Memory.get l t mem2 = Some (f, Message.mk v r))
        (DIFF: (loc, to) <> (l, t)):
    Memory.get l t mem1 = Some (f, Message.mk v r).
  Proof.
    inv PROMISE.
    - exploit Memory.add_get_inv; eauto. i. des; auto.
      inv x3. congr.
    - exploit Memory.update_get_inv; eauto. i. des; auto.
      subst. congr.
  Qed.

  Lemma remove_get_diff
        promises0 mem0 loc from to val released promises1
        l t
        (LOC: loc <> l)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc from to val released promises1):
    Memory.get l t promises1 = Memory.get l t promises0.
  Proof.
    destruct (Memory.get l t promises1) as [[]|] eqn:Y.
    { exploit Memory.remove_get_inv; try apply REMOVE; eauto. i. des. congr. }
    destruct (Memory.get l t promises0) as [[]|] eqn:X.
    { exploit Memory.remove_get1; try apply REMOVE; eauto. i. des; congr. }
    auto.
  Qed.

  Lemma remove_cell_diff
        promises0 loc from to val released promises1
        l
        (LOC: loc <> l)
        (REMOVE: Memory.remove promises0 loc from to val released promises1):
    promises1 l = promises0 l.
  Proof.
    apply Cell.ext. i. eapply remove_get_diff; eauto. refl.
  Qed.
End MemoryFacts.
