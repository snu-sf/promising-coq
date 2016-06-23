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
Require Import View.
Require Import Cell.
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


Lemma remove_promise_remove_remove
      promises1 loc ts1 ts2 ts3 val1 released1 val2 released2 promises4
      mem1
      (LE: Memory.le promises1 mem1)
      (REMOVE: Memory.remove promises1 loc ts1 ts3 val2 released2 promises4):
  exists promises2 mem2 promises3,
    <<SPLIT: Memory.promise promises1 mem1 loc ts1 ts2 val1 released1 promises2 mem2 (Memory.promise_kind_split ts3)>> /\
    <<REMOVE1: Memory.remove promises2 loc ts1 ts2 val1 released1 promises3>> /\
    <<REMOVE2: Memory.remove promises3 loc ts2 ts3 val2 released2 promises4>>.
Proof.
Admitted.

Lemma promise_remove_promise_remove_promise_remove
      promises1 loc ts1 ts2 ts3 val1 released1 val2 released2 promises4 promises5
      mem1 mem4
      (LE: Memory.le promises1 mem1)
      (PROMISE: Memory.promise promises1 mem1 loc ts1 ts3 val2 released2 promises4 mem4 Memory.promise_kind_add)
      (REMOVE: Memory.remove promises4 loc ts1 ts3 val2 released2 promises5):
  exists promises2 mem2 promises3 promises4 mem4,
    <<PROMISE1: Memory.promise promises1 mem1 loc ts1 ts2 val1 released1 promises2 mem2 Memory.promise_kind_add>> /\
    <<REMOVE1: Memory.remove promises2 loc ts1 ts2 val1 released1 promises3>> /\
    <<PROMISE2: Memory.promise promises3 mem2 loc ts2 ts3 val2 released2 promises4 mem4 Memory.promise_kind_add>> /\
    <<REMOVE2: Memory.remove promises4 loc ts2 ts3 val2 released2 promises5>>.
Proof.
Admitted.
