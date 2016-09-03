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

  Lemma promise_get_promises_inv_diff
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: Memory.get l t promises2 = Some (f, Message.mk v r))
        (DIFF: (loc, to) <> (l, t)):
    exists f', Memory.get l t promises1 = Some (f', Message.mk v r).
  Proof.
    revert GET. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + des. subst. congr.
      + i. inv GET. esplits; eauto.
    - erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. i. inv GET.
        exploit Memory.split_get0; try exact PROMISES; eauto. i. des. esplits; eauto.
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

  Lemma get_same_from_aux
        l f t1 t2 m msg1 msg2
        (GET1: Memory.get l t1 m = Some (f, msg1))
        (GET2: Memory.get l t2 m = Some (f, msg2))
        (LE: Time.le t1 t2)
        (T1: t1 <> Time.bot):
    t1 = t2 /\ msg1 = msg2.
  Proof.
    inv LE; cycle 1.
    { inv H. rewrite GET1 in GET2. inv GET2. ss. }
    destruct (m l).(Cell.WF). exfalso.
    assert (t1 <> t2).
    { ii. subst. eapply Time.lt_strorder. eauto. }
    eapply DISJOINT; try exact H0; eauto.
    - apply Interval.mem_ub. exploit VOLUME; try exact GET1; eauto. i. des; ss.
      inv x. congr.
    - econs; ss.
      + exploit VOLUME; try exact GET1; eauto. i. des; ss. inv x. congr.
      + left. ss.
  Qed.

  Lemma get_same_from
        l f t1 t2 m msg1 msg2
        (GET1: Memory.get l t1 m = Some (f, msg1))
        (GET2: Memory.get l t2 m = Some (f, msg2))
        (T1: t1 <> Time.bot)
        (T2: t2 <> Time.bot):
    t1 = t2 /\ msg1 = msg2.
  Proof.
    destruct (Time.le_lt_dec t1 t2).
    - eapply get_same_from_aux; eauto.
    - exploit get_same_from_aux; (try by left; eauto); eauto. i. des. ss.
  Qed.

  Lemma write_not_bot
        pm1 mem1 loc from to val released pm2 mem2 kind
        (WRITE: Memory.write pm1 mem1 loc from to val released pm2 mem2 kind):
    to <> Time.bot.
  Proof.
    ii. subst. inv WRITE. inv PROMISE.
    - inv MEM. inv ADD. inv TO.
    - inv MEM. inv SPLIT. inv TS12.
    - inv MEM. inv LOWER. inv TS0.
  Qed.

  Lemma promise_exists_None
        promises1 mem1 loc from to val released
        (LE: Memory.le promises1 mem1)
        (GET: Memory.get loc to promises1 = Some (from, Message.mk val released))
        (LT: Time.lt from to):
    exists promises2 mem2,
      Memory.promise promises1 mem1 loc from to val None promises2 mem2 (Memory.op_kind_lower released).
  Proof.
    exploit Memory.lower_exists; eauto; try by econs. i. des.
    exploit LE; eauto. i.
    exploit Memory.lower_exists; eauto; try by econs. i. des.
    esplits. econs; eauto. apply Time.bot_spec.
  Qed.

  Lemma some_released_time_lt
  mem loc from to val released
  (CLOSED: Memory.closed mem)
  (GET: Memory.get loc to mem = Some (from, Message.mk val (Some released))):
    Time.lt from to.
  Proof.
    destruct (mem loc).(Cell.WF). exploit VOLUME; eauto. i. des; ss. inv x.
    inv CLOSED. rewrite INHABITED in GET. inv GET.
  Qed.
End MemoryFacts.
