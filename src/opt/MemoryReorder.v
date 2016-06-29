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
Require Import MemoryFacts.

Set Implicit Arguments.


Module MemoryReorder.
  Lemma remove_add
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
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.add_o; eauto.
    erewrite (@MemoryFacts.add_o mem2); eauto.
    erewrite (@MemoryFacts.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. congr.
  Qed.

  Lemma remove_update
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
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.update_o; eauto.
    erewrite (@MemoryFacts.update_o mem2); eauto.
    erewrite (@MemoryFacts.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    contradict x1. auto.
  Qed.

  Lemma remove_promise
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
      exploit remove_add; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.update_get0; try eexact PROMISES; eauto. i.
      exploit Memory.remove_get_inv; try eexact REMOVE; eauto. i. des.
      exploit Memory.update_exists; eauto; try by inv PROMISES; inv UPDATE; eauto. i. des.
      exploit remove_update; eauto. i.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma remove_remove
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
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite (@MemoryFacts.remove_o promises2); eauto.
    erewrite (@MemoryFacts.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.
End MemoryReorder.
