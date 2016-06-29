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
  Lemma add_o
        mem2 mem1 loc from to val released
        l t
        (ADD: Memory.add mem1 loc from to val released mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, Message.mk val released)
    else Memory.get l t mem1.
  Proof.
    condtac; ss.
    - des. subst. eapply Memory.add_get2; eauto.
    - destruct (Memory.get l t mem1) as [[? []]|] eqn:X.
      { erewrite Memory.add_get1; eauto. }
      destruct (Memory.get l t mem2) as [[? []]|] eqn:Y.
      { exploit Memory.add_get_inv; eauto. i. des; congr. }
      auto.
  Qed.

  Lemma update_o
        mem2 mem1 loc from1 from2 to val released1 released2
        l t
        (UPDATE: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from2, Message.mk val released2)
    else Memory.get l t mem1.
  Proof.
    condtac; ss.
    - des. subst. eapply Memory.update_get2; eauto.
    - guardH o. destruct (Memory.get l t mem1) as [[? []]|] eqn:X.
      { exploit Memory.update_get1; eauto. i. des; auto.
        inv x3. unguardH o. des; congr.
      }
      destruct (Memory.get l t mem2) as [[? []]|] eqn:Y.
      { exploit Memory.update_get_inv; eauto. i. des; try congr.
        subst. unguardH o. des; congr.
      }
      auto.
  Qed.

  Lemma remove_o
        mem2 mem1 loc from to val released
        l t
        (UPDATE: Memory.remove mem1 loc from to val released mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else Memory.get l t mem1.
  Proof.
    condtac; ss.
    - des. subst. eapply Memory.remove_get2; eauto.
    - guardH o. destruct (Memory.get l t mem1) as [[? []]|] eqn:X.
      { exploit Memory.remove_get1; eauto. i. des; auto.
        inv x3. unguardH o. des; congr.
      }
      destruct (Memory.get l t mem2) as [[? []]|] eqn:Y.
      { exploit Memory.remove_get_inv; eauto. i. des; congr. }
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
