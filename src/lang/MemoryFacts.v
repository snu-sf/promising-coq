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


Lemma add_update_add
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

Lemma update_update_update
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

Lemma promise_promise_promise
      loc from1 from2 to val released1 released2 promises0 promises1 promises2 mem0 mem1 mem2 kind
      (PROMISE1: Memory.promise promises0 mem0 loc from1 to val released1 promises1 mem1 kind)
      (PROMISE2: Memory.promise promises1 mem1 loc from2 to val released2 promises2 mem2 (Memory.promise_kind_update from1 released1)):
  Memory.promise promises0 mem0 loc from2 to val released2 promises2 mem2 kind.
Proof.
  inv PROMISE2. inv PROMISE1.
  - econs; eauto.
    + eapply add_update_add; eauto.
    + eapply add_update_add; eauto.
  - econs; eauto.
    + eapply update_update_update; eauto.
    + eapply update_update_update; eauto.
Qed.

Lemma remove_update_remove
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

Lemma remove_promise_remove
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
  exploit remove_update_remove; eauto. i. des.
  exploit Memory.update_exists_le; eauto. i. des.
  esplits; eauto.
  - econs; eauto. etrans; eauto. apply REL_LE.
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
