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
      (LE: Memory.le promises1 mem1)
      (FULFILL: Memory.fulfill promises1 loc1 from1 to1 msg1 promises2)
      (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 msg2 promises3 mem3):
  exists promises2',
    Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2' mem3 /\
    Memory.fulfill promises2' loc1 from1 to1 msg1 promises3.
Proof.
Admitted.

Lemma get_fulfill
      promises0 mem0 loc from to msg promises1
      l t m
      (LOC: loc <> l)
      (LE: Memory.le promises0 mem0)
      (GET: Memory.get l t mem0 = Some m)
      (FULFILL: Memory.fulfill promises0 loc from to msg promises1):
  Memory.get l t promises0 = Memory.get l t promises1.
Proof.
Admitted.

Lemma cell_fulfill
      promises0 loc from to msg promises1
      l
      (LOC: loc <> l)
      (FULFILL: Memory.fulfill promises0 loc from to msg promises1):
  promises0 l = promises1 l.
Proof.
Admitted.

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
Admitted.
