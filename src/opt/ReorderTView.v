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
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimPromises.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma read_read_tview
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      tview0
      (WF0: TView.wf tview0)
      (WF1: View.opt_wf released1)
      (WF2: View.opt_wf released2):
  TView.le
    (TView.read_tview
       (TView.read_tview tview0 loc2 ts2 released2 ord2)
       loc1 ts1 released1 ord1)
    (TView.read_tview
       (TView.read_tview tview0 loc1 ts1 released1 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
Qed.

Lemma read_write_tview
      loc1 ts1 released1 ord1
      loc2 ts2 ord2
      tview0 sc0
      (WF0: TView.wf tview0)
      (WF1: View.opt_wf released1):
  TView.le
    (TView.read_tview
       (TView.write_tview tview0 sc0 loc2 ts2 ord2)
       loc1 ts1 released1 ord1)
    (TView.write_tview
       (TView.read_tview tview0 loc1 ts1 released1 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  repeat condtac; aggrtac; try apply WF0.
Qed.

Lemma read_read_fence_tview
      loc1 ts1 released1 ord1
      ord2
      tview0
      (WF0: TView.wf tview0)
      (WF1: View.opt_wf released1):
  TView.le
    (TView.read_tview
       (TView.read_fence_tview tview0 ord2)
       loc1 ts1 released1 ord1)
    (TView.read_fence_tview
       (TView.read_tview tview0 loc1 ts1 released1 ord1)
       ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  - repeat condtac; aggrtac; try apply WF0.
  - repeat condtac; aggrtac; try apply WF0.
    destruct ord1; inv COND; inv COND1.
Qed.

Lemma read_write_fence_tview
      loc1 ts1 released1 ord1
      ord2
      tview0 sc0
      (WF0: TView.wf tview0)
      (WF1: View.opt_wf released1):
  TView.le
    (TView.read_tview
       (TView.write_fence_tview tview0 sc0 ord2)
       loc1 ts1 released1 ord1)
    (TView.write_fence_tview
       (TView.read_tview tview0 loc1 ts1 released1 ord1)
       sc0 ord2).
Proof.
  unfold TView.write_fence_tview, TView.write_fence_sc.
  econs; repeat (try condtac; aggrtac; try apply WF0).
Qed.

Lemma write_read_tview
      loc1 ts1 ord1
      loc2 ts2 released2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0)
      (WF2: View.opt_wf released2):
  TView.le
    (TView.write_tview
       (TView.read_tview tview0 loc2 ts2 released2 ord2)
       sc0 loc1 ts1 ord1)
    (TView.read_tview
       (TView.write_tview tview0 sc0 loc1 ts1 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  condtac; aggrtac. condtac.
  - destruct ord1; inv ORD1; inv COND0.
  - aggrtac; try apply WF0.
Qed.

Lemma write_write_tview
      loc1 ts1 ord1
      loc2 ts2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_tview
       (TView.write_tview tview0 sc0 loc2 ts2 ord2)
       sc0 loc1 ts1 ord1)
    (TView.write_tview
       (TView.write_tview tview0 sc0 loc1 ts1 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; repeat (try condtac; aggrtac).
  all: try by apply WF0.
Qed.

Lemma write_read_fence_tview
      loc1 ts1 ord1
      ord2
      tview0 sc0
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_tview
       (TView.read_fence_tview tview0 ord2)
       sc0 loc1 ts1 ord1)
    (TView.read_fence_tview
       (TView.write_tview tview0 sc0 loc1 ts1 ord1)
       ord2).
Proof.
  econs; repeat (try condtac; aggrtac; try apply WF0).
Qed.

Lemma write_write_fence_tview
      loc1 ts1 ord1
      ord2
      tview0 sc0
      (ORD2: Ordering.le ord2 Ordering.acqrel)
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_tview
       (TView.write_fence_tview tview0 sc0 ord2)
       (TView.write_fence_sc tview0 sc0 ord2)
       loc1 ts1 ord1)
    (TView.write_fence_tview
       (TView.write_tview tview0 sc0 loc1 ts1 ord1)
       sc0 ord2).
Proof.
  unfold TView.write_fence_tview, TView.write_fence_sc.
  econs; repeat (try condtac; aggrtac; try apply WF0).
Qed.

Lemma read_fence_read_tview
      ord1
      loc2 ts2 released2 ord2
      tview0
      (ORD2: Ordering.le ord2 Ordering.plain \/ Ordering.le Ordering.acqrel ord2)
      (WF0: TView.wf tview0):
  TView.le
    (TView.read_fence_tview
       (TView.read_tview tview0 loc2 ts2 released2 ord2)
       ord1)
    (TView.read_tview
       (TView.read_fence_tview tview0 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; repeat (try condtac; aggrtac; try apply WF0).
  des; [|congr]. destruct ord2; inv ORD2; inv COND0.
Qed.

Lemma read_fence_write_tview
      ord1
      loc2 ts2 ord2
      tview0 sc0
      (WF0: TView.wf tview0):
  TView.le
    (TView.read_fence_tview
       (TView.write_tview tview0 sc0 loc2 ts2 ord2)
       ord1)
    (TView.write_tview
       (TView.read_fence_tview tview0 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; repeat (try condtac; aggrtac; try apply WF0).
Qed.

Lemma write_fence_read_tview
      ord1
      loc2 ts2 released2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0)
      (WF2: View.opt_wf released2):
  TView.le
    (TView.write_fence_tview
       (TView.read_tview tview0 loc2 ts2 released2 ord2) sc0 ord1)
    (TView.read_tview
       (TView.write_fence_tview tview0 sc0 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat (condtac; aggrtac; try apply WF0)).
Qed.

Lemma write_fence_read_sc
      ord1
      loc2 ts2 released2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0):
  TimeMap.le
    (TView.write_fence_sc
       (TView.read_tview tview0 loc2 ts2 released2 ord2) sc0 ord1)
    (TView.write_fence_sc tview0 sc0 ord1).
Proof.
  ii. unfold TView.write_fence_sc.
  repeat condtac; aggrtac.
Qed.

Lemma write_fence_write_tview
      ord1
      loc2 ts2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0):
  TView.le
    (TView.write_fence_tview
       (TView.write_tview tview0 sc0 loc2 ts2 ord2)
       sc0 ord1)
    (TView.write_tview
       (TView.write_fence_tview tview0 sc0 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat (condtac; aggrtac; try apply WF0)).
Qed.

Lemma write_fence_write_sc
      ord1
      loc2 ts2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: TView.wf tview0):
  TimeMap.le
    (TView.write_fence_sc
       (TView.write_tview tview0 sc0 loc2 ts2 ord2)
       sc0 ord1)
    (TView.write_fence_sc tview0 sc0 ord1).
Proof.
  ii. unfold TView.write_fence_sc.
  repeat condtac; aggrtac.
Qed.

Lemma read_fence_write_fence_tview
      ord1
      ord2
      tview0 sc0
      (WF0: TView.wf tview0):
  TView.le
    (TView.read_fence_tview
       (TView.write_fence_tview tview0 sc0 ord2)
       ord1)
    (TView.write_fence_tview
       (TView.read_fence_tview tview0 ord1)
       sc0 ord2).
Proof.
  unfold TView.write_fence_tview, TView.write_fence_sc.
  econs; repeat (try condtac; aggrtac; try apply WF0).
  - rewrite <- TimeMap.join_r. apply WF0.
  - rewrite <- TimeMap.join_r. apply WF0.
  - rewrite <- TimeMap.join_r. apply WF0.
  - rewrite <- View.join_r. viewtac.
    rewrite <- TimeMap.join_r. apply WF0.
  - rewrite <- View.join_r. viewtac.
    rewrite <- TimeMap.join_r. apply WF0.
Qed.

Lemma read_write_tview_eq
      loc1 ts1 released1 ord1
      loc2 ts2 ord2
      tview0 sc0
      (ORD1: Ordering.le ord2 Ordering.relaxed)
      (WF0: TView.wf tview0)
      (WF1: View.opt_wf released1):
  (TView.read_tview
     (TView.write_tview tview0 sc0 loc2 ts2 ord2)
     loc1 ts1 released1 ord1) =
  (TView.write_tview
     (TView.read_tview tview0 loc1 ts1 released1 ord1)
     sc0 loc2 ts2 ord2).
Proof.
  apply TView.antisym.
  - apply read_write_tview; auto.
  - apply write_read_tview; auto.
Qed.
