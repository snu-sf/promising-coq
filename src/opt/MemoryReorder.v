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
  Lemma add_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2).
    { i. inv ADD2. inv ADD. eapply DISJOINT.
      etrans; [eapply Memory.add_o; eauto|]. condtac; ss; eauto.
      des. subst. erewrite Memory.add_get0 in GET2; eauto. congr.
    }
    { inv ADD2. inv ADD. auto. }
    { inv ADD2. inv ADD. eauto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1).
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        exploit Memory.add_get0; try exact ADD2; eauto.
        inv ADD2. inv ADD. symmetry. eapply DISJOINT.
        etrans; [eapply Memory.add_o; eauto|]. condtac; ss. des; congr.
      - guardH o. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact ADD2; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
  Qed.

  Lemma promise_add_promise_add
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2 mem2
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.promise_kind_add)
        (PROMISE2: Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2 mem2 Memory.promise_kind_add):
    exists promises1' mem1',
      <<PROMISE1: Memory.promise promises0 mem0 loc2 from2 to2 val2 released2 promises1' mem1' Memory.promise_kind_add>> /\
      <<PROMISE2: Memory.promise promises1' mem1' loc1 from1 to1 val1 released1 promises2 mem2 Memory.promise_kind_add>>.
  Proof.
    inv PROMISE1. inv PROMISE2.
    exploit add_add; try exact PROMISES; eauto. i. des.
    exploit add_add; try exact MEM; eauto. i. des.
    esplits.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma add_remove
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (DIFF: (loc1, to1) <> (loc2, to2))
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>.
  Proof.
    exploit Memory.remove_get0; try exact REMOVE2; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
    { des. subst. congr. }
    guardH o. i.
    exploit Memory.remove_exists; eauto. i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1); eauto.
    { i. revert GET2. erewrite Memory.remove_o; eauto. condtac; ss. i.
      inv ADD1. inv ADD. eapply DISJOINT. eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact x0; eauto. congr.
  Qed.

  Lemma promise_add_remove
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2
        (DIFF: (loc1, to1) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.promise_kind_add)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 val1 released1 promises2 mem1 Memory.promise_kind_add>>.
  Proof.
    inv PROMISE1.
    exploit add_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto. econs; eauto.
  Qed.

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
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. erewrite Memory.add_get0 in x0; eauto. congr.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. congr.
  Qed.

  Lemma remove_split
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem2)
        (SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.split_o; eauto. repeat condtac; ss.
      - des. subst. congr.
      - guardH o. des. subst. rewrite GET3 in x0. inv x0.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.split_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss).
    - des; congr.
    - guardH o. des. repeat subst. rewrite GET3 in x0. inv x0.
      exploit Memory.remove_get0; try exact x1; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss. i. inv x0.
      inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma remove_lower
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2' released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2' released2 mem2)
        (LOWER1: Memory.lower mem0 loc2 from2 to2 val2 released2' released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.lower_o; eauto. condtac; ss.
      des. subst.
      exploit Memory.lower_get0; try exact LOWER2; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.lower_get0; try exact LOWER2; eauto.
    erewrite Memory.remove_o; eauto. condtac; ss.
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
    - exploit Memory.split_get0; try eexact PROMISES; eauto. i. des.
      revert GET3. erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.split_exists; eauto; try by inv PROMISES; inv SPLIT; eauto. i. des.
      exploit remove_split; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.lower_get0; try eexact PROMISES; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.lower_exists; eauto; try by inv PROMISES; inv LOWER; eauto. i. des.
      exploit remove_lower; eauto. i.
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
    exploit Memory.remove_get0; try apply REMOVE2; eauto.
    erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
    exploit Memory.remove_exists; eauto. i. des.
    exploit Memory.remove_get0; try apply REMOVE1; eauto. i.
    exploit (@Memory.remove_exists mem2 loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss. des. subst. congr. }
    i. des.
    esplits; eauto.
    cut (mem0 = promises2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o promises2); eauto. erewrite (@Memory.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.
End MemoryReorder.
