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

Require Import SimPromises.
Require Import Compatibility.
Require Import Simulation.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma remove_promise_remove_remove
      loc ts1 ts2 ts3 val2 released2
      promises0 mem0
      promises4
      (LE: Memory.le promises0 mem0)
      (REMOVE: Memory.remove promises0 loc ts1 ts3 val2 released2 promises4):
  exists promises1 mem1 promises3,
    <<STEP1: Memory.promise promises0 mem0 loc ts2 ts3 val2 released2 promises1 mem1 (Memory.promise_kind_update ts1 released2)>> /\
    <<STEPS:
      forall val1 released1,
      exists promises2 mem2,
        <<STEP2: Memory.promise promises1 mem1 loc ts1 ts2 val1 released1 promises2 mem2 Memory.promise_kind_add>> /\
        <<STEP3: Memory.remove promises2 loc ts1 ts2 val1 released1 promises3>> /\
        <<STEP4: Memory.remove promises3 loc ts2 ts3 val2 released2 promises4>>>>.
Proof.
Admitted.

Lemma promise_remove_promise_remove_promise_remove
      loc ts1 ts2 ts3 val2 val1 released1 released2
      promises0 mem0
      mem4 promises4
      promises5
      (LE: Memory.le promises0 mem0)
      (PROMISE: Memory.promise promises0 mem0 loc ts1 ts3 val2 released2 promises4 mem4 Memory.promise_kind_add)
      (REMOVE: Memory.remove promises4 loc ts1 ts3 val2 released2 promises5):
  exists promises1 promises2 promises3 mem1 mem3,
    <<STEP1: Memory.promise promises0 mem0 loc ts1 ts2 val1 released1 promises1 mem1 Memory.promise_kind_add>> /\
    <<STEP2: Memory.remove promises1 loc ts1 ts2 val1 released1 promises2>> /\
    <<STEP3: Memory.promise promises2 mem1 loc ts2 ts3 val2 released2 promises3 mem3 Memory.promise_kind_add>> /\
    <<STEP4: Memory.remove promises3 loc ts2 ts3 val2 released2 promises4>>.
Proof.
Admitted.
