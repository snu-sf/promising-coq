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
  Lemma promise_time_lt
        promises1 mem1 loc from to val released promises2 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
    Time.lt from to.
  Proof.
    inv PROMISE.
    - inv MEM. inv ADD. auto.
    - inv MEM. inv SPLIT. auto.
    - inv MEM. inv LOWER. auto.
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
    exists f', Memory.get l t mem2 = Some (f', Message.mk v r).
  Proof.
    inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst.
        exploit Memory.split_get0; eauto. i. des.
        rewrite GET3 in GET. inv GET. esplits; eauto.
      + esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. congr.
      + esplits; eauto.
  Qed.        

  Lemma promise_get_inv_diff
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: Memory.get l t mem2 = Some (f, Message.mk v r))
        (DIFF: (loc, to) <> (l, t)):
    exists f', Memory.get l t mem1 = Some (f', Message.mk v r).
  Proof.
    revert GET. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. i. inv GET.
        exploit Memory.split_get0; eauto. i. des. esplits; eauto.
      + i. esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
  Qed.        

  Lemma remove_get_diff
        promises0 mem0 loc from to val released promises1
        l t
        (LOC: loc <> l)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc from to val released promises1):
    Memory.get l t promises1 = Memory.get l t promises0.
  Proof.
    erewrite Memory.remove_o; eauto. condtac; ss.
    des. subst. congr.
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
