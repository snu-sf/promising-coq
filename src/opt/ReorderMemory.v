Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma fulfill_promise
      promises1 loc1 from1 to1 msg1
      promises2 loc2 from2 to2 msg2
      promises3
      mem1 mem3
      kind
      (LE: Memory.le promises1 mem1)
      (FULFILL: Memory.fulfill promises1 loc1 from1 to1 msg1 promises2)
      (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 msg2 promises3 mem3 kind):
  exists promises2',
    Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2' mem3 kind /\
    Memory.fulfill promises2' loc1 from1 to1 msg1 promises3.
Proof.
Admitted.

Lemma get_fulfill
      promises0 mem0 loc from to msg promises1
      l t
      (LOC: loc <> l)
      (LE: Memory.le promises0 mem0)
      (FULFILL: Memory.fulfill promises0 loc from to msg promises1):
  Memory.get l t promises0 = Memory.get l t promises1.
Proof.
  destruct (Memory.get l t promises0) as [[]|] eqn:X.
  { exploit Memory.remove_get1; try apply FULFILL; eauto. i. des; auto.
    subst. congr.
  }
  destruct (Memory.get l t promises1) as [[]|] eqn:Y.
  { exploit Memory.remove_get_inv; try apply FULFILL; eauto. i. des. congr. }
  auto.
Qed.

Lemma cell_fulfill
      promises0 loc from to msg promises1
      l
      (LOC: loc <> l)
      (FULFILL: Memory.fulfill promises0 loc from to msg promises1):
  promises0 l = promises1 l.
Proof.
  apply Cell.ext. i. eapply get_fulfill; eauto. refl.
Qed.

Lemma fulfill_fulfill
      promises1 loc1 from1 to1 msg1
      promises2 loc2 from2 to2 msg2
      promises3
      (FULFILL1: Memory.fulfill promises1 loc1 from1 to1 msg1 promises2)
      (FULFILL2: Memory.fulfill promises2 loc2 from2 to2 msg2 promises3):
  exists promises2',
    Memory.fulfill promises1 loc2 from2 to2 msg2 promises2' /\
    Memory.fulfill promises2' loc1 from1 to1 msg1 promises3.
Proof.
  exploit Memory.remove_disjoint; try apply FULFILL2; eauto. i.
  exploit Memory.remove_get_inv; try apply FULFILL1; eauto. i. des.
  exploit Memory.remove_exists; eauto. i. des.
  exploit Memory.remove_disjoint; try apply FULFILL1; eauto. i.
  exploit Memory.remove_get1; try apply x3; eauto. i. des; [by contradict x1|].
  exploit Memory.remove_exists; eauto. i. des.
  assert (mem0 = promises3).
  { apply Memory.ext. i.
    destruct (Memory.get loc ts mem0) as [[]|] eqn:X.
    { exploit Memory.remove_get_inv; try apply x6; eauto. i. des.
      exploit Memory.remove_get_inv; try apply x3; eauto. i. des.
      exploit Memory.remove_get1; try apply FULFILL1; eauto. i. des; [by contradict x7|].
      exploit Memory.remove_get1; try apply FULFILL2; eauto. i. des; [by contradict x9|].
      auto.
    }
    destruct (Memory.get loc ts promises3) as [[]|] eqn:Y.
    { exploit Memory.remove_get_inv; try apply FULFILL2; eauto. i. des.
      exploit Memory.remove_get_inv; try apply FULFILL1; eauto. i. des.
      exploit Memory.remove_get1; try apply x3; eauto. i. des; [by contradict x7|].
      exploit Memory.remove_get1; try apply x6; eauto. i. des; [by contradict x9|].
      congr.
    }
    auto.
  }
  subst. eexists. splits; econs; eauto.
Qed.
