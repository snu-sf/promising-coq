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


Lemma fulfill_promise_fulfill_fulfill
      promises1 loc ts1 ts2 ts3 msg1 msg2 promises4
      mem1
      (LE: Memory.le promises1 mem1)
      (FULFILL: Memory.fulfill promises1 loc ts1 ts3 msg2 promises4):
  exists promises2 mem2 promises3,
    <<SPLIT: Memory.promise promises1 mem1 loc ts1 ts2 msg1 promises2 mem2 Memory.promise_kind_split>> /\
    <<FULFILL1: Memory.fulfill promises2 loc ts1 ts2 msg1 promises3>> /\
    <<FULFILL2: Memory.fulfill promises3 loc ts2 ts3 msg2 promises4>>.
Proof.
Admitted.

Lemma promise_fulfill_promise_fulfill_promise_fulfill
      promises1 loc ts1 ts2 ts3 msg1 msg2 promises4 promises5
      mem1 mem4
      (LE: Memory.le promises1 mem1)
      (PROMISE: Memory.promise promises1 mem1 loc ts1 ts3 msg2 promises4 mem4 Memory.promise_kind_add)
      (FULFILL: Memory.fulfill promises4 loc ts1 ts3 msg2 promises5):
  exists promises2 mem2 promises3 promises4 mem4,
    <<PROMISE1: Memory.promise promises1 mem1 loc ts1 ts2 msg1 promises2 mem2 Memory.promise_kind_add>> /\
    <<FULFILL1: Memory.fulfill promises2 loc ts1 ts2 msg1 promises3>> /\
    <<PROMISE2: Memory.promise promises3 mem2 loc ts2 ts3 msg2 promises4 mem4 Memory.promise_kind_add>> /\
    <<FULFILL2: Memory.fulfill promises4 loc ts2 ts3 msg2 promises5>>.
Proof.
Admitted.
