From Stdlib Require Import Bool.
From Stdlib Require Import List.
From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import lang.Event.
From PromisingLib Require Import Language.
Require Import lang.Time.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import lang.TView.
Require Import lang.Thread.
Require Import lang.Configuration.
Require Import lang.Progress.

Require Import opt.SimPromises.
Require Import opt.Compatibility.
Require Import opt.SimThread.

Require Import while.Syntax.
Require Import while.Semantics.

Set Implicit Arguments.


Lemma read_read_tview
      loc ts released ord
      tview0
      (WF0: TView.wf tview0)
      (WF_REL: View.opt_wf released):
  TView.le
    (TView.read_tview (TView.read_tview tview0 loc ts released ord) loc ts released ord)
    (TView.read_tview tview0 loc ts released ord).
Proof.
  econs; aggrtac;
    (try sfby apply WF0);
    repeat condtac; aggrtac.
Qed.

Lemma write_read_tview
      loc ts ord1 ord2
      tview0 sc0
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (WF0: TView.wf tview0):
  TView.le
    (TView.read_tview (TView.write_tview tview0 sc0 loc ts ord1) loc ts
                        (Some ((TView.write_tview tview0 sc0 loc ts ord1).(TView.rel) loc))
                        ord2)
    (TView.write_tview tview0 sc0 loc ts ord1).
Proof.
  econs; repeat (try condtac; aggrtac; try apply WF0).
Qed.

Lemma write_write_tview
      loc ts1 ts2 ord
      (TS: Time.lt ts1 ts2)
      tview0 sc0
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_tview (TView.write_tview tview0 sc0 loc ts1 ord)
                         sc0
                         loc ts2 ord)
    (TView.write_tview tview0 sc0 loc ts2 ord).
Proof.
  econs; repeat (try condtac; aggrtac).
  all: try sfby apply WF0.
Qed.

Lemma read_fence_read_fence_tview
      ord
      tview0
      (WF0: TView.wf tview0):
  TView.le
    (TView.read_fence_tview (TView.read_fence_tview tview0 ord) ord)
    (TView.read_fence_tview tview0 ord).
Proof.
  econs; aggrtac;
    (try sfby apply WF0).
  repeat condtac; viewtac.
Qed.

Lemma write_fence_write_fence_sc
      ord
      tview0 sc0
      (WF0: TView.wf tview0):
  TimeMap.le
    (TView.write_fence_sc (TView.write_fence_tview tview0 sc0 ord) (TView.write_fence_sc tview0 sc0 ord) ord)
    (TView.write_fence_sc tview0 sc0 ord).
Proof.
  unfold TView.write_fence_tview, TView.write_fence_sc.
  repeat (condtac; aggrtac).
Qed.

Lemma write_fence_write_fence_tview
      ord
      tview0 sc0
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_fence_tview (TView.write_fence_tview tview0 sc0 ord) (TView.write_fence_sc tview0 sc0 ord) ord)
    (TView.write_fence_tview tview0 sc0 ord).
Proof.
  econs; aggrtac;
    (try sfby apply WF0);
    (repeat condtac; aggrtac);
    rewrite <- ? View.join_r; viewtac.
  - apply write_fence_write_fence_sc; auto.
  - apply write_fence_write_fence_sc; auto.
  - apply write_fence_write_fence_sc; auto.
Qed.
