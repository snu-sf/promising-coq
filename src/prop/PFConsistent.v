From Stdlib Require Import Lia.
From Stdlib Require Import RelationClasses.
From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
Require Import lang.Event.
Require Import lang.Time.
From PromisingLib Require Import Language.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import lang.TView.
Require Import lang.Thread.

Require Import opt.SimMemory.
Require Import opt.SimPromises.
Require Import opt.SimLocal.
Require Import opt.FulfillStep.
Require Import prop.MemoryReorder.

Require Import drf.PromiseConsistent.
Require Import prop.ReorderPromises.

Set Implicit Arguments.


Definition pf_consistent lang (e:Thread.t lang): Prop :=
  forall sc1 mem1
    (FUTURE: Memory.future e.(Thread.memory) mem1)
    (FUTURE: TimeMap.le e.(Thread.sc) sc1)
    (WF: Local.wf e.(Thread.local) mem1)
    (SC: Memory.closed_timemap sc1 mem1)
    (MEM: Memory.closed mem1),
  exists e2,
    <<STEPS: rtc (tau (Thread.step true)) (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
    <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.

Lemma consistent_pf_consistent:
  Thread.consistent <2= pf_consistent.
Proof.
  s. ii. exploit PR; eauto. i. des.
  exploit tau_steps_pf_tau_steps; eauto.
  { ii. rewrite PROMISES, Memory.bot_get in *.  congr. }
  i. des.
  exploit rtc_union_step_nonpf_bot; [|eauto|].
  { eapply rtc_implies; [|eauto]. apply tau_union. }
  i. subst. esplits; eauto.
Qed.
