Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import FulfillStep.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Definition VIEW_CMP := forall (loc:Loc.t) (ts:Time.t) (lhs rhs:option View.t), Prop.

Definition loctmeq: VIEW_CMP := fun _ _ (r1 r2: option View.t) => r1 = r2.
#[export]
Hint Unfold loctmeq: core.

Definition mem_sub (cmp: VIEW_CMP) (m1 m2: Memory.t) : Prop :=
  forall loc ts from val rel1
    (IN: Memory.get loc ts m1 = Some (from, Message.mk val rel1)),
  exists rel2,
  <<IN: Memory.get loc ts m2 = Some (from, Message.mk val rel2)>> /\
  <<CMP: cmp loc ts rel1 rel2>>.

Definition mem_eqrel (cmp: VIEW_CMP) (m1 m2: Memory.t) : Prop :=
  <<LR: mem_sub cmp m1 m2>> /\
  <<RL: mem_sub (fun l t x y => cmp l t y x) m2 m1>>.
#[export]
Hint Unfold mem_eqrel: core.

Definition mem_eqlerel (m1 m2: Memory.t) : Prop :=
  mem_eqrel (fun _ _ => View.opt_le) m1 m2.
#[export]
Hint Unfold mem_eqlerel: core.

Program Instance mem_eqlerel_PreOrder: PreOrder mem_eqlerel.
Next Obligation.
  ii. econs; ii; esplits; eauto; refl.
Qed.
Next Obligation.
  ii. inv H. inv H0. des. econs; ii.
  - exploit H1; eauto. i. des.
    exploit H; eauto. i. des.
    esplits; eauto. etrans; eauto.
  - exploit H3; eauto. i. des.
    exploit H2; eauto. i. des.
    esplits; eauto. etrans; eauto.
Qed.

Lemma mem_eqlerel_get
      m1 m2
      l f t v r2
      (LE: mem_eqlerel m1 m2)
      (GET2: Memory.get l t m2 = Some (f, Message.mk v r2)):
  exists r1,
    <<GET1: Memory.get l t m1 = Some (f, Message.mk v r1)>> /\
    <<REL: View.opt_le r1 r2>>.
Proof. inv LE. des. exploit H0; eauto. Qed.

Lemma mem_eqrel_closed_timemap
      cmp tm m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: Memory.closed_timemap tm m1):
  Memory.closed_timemap tm m2.
Proof.
  ii. specialize (CLOSED loc). des.
  apply EQMEM in CLOSED. des.
  esplits; eauto.
Qed.

Lemma mem_eqrel_closed_view
      cmp cap m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: Memory.closed_view cap m1):
  Memory.closed_view cap m2.
Proof.
  inv CLOSED. econs; eapply mem_eqrel_closed_timemap; eauto.
Qed.

Lemma mem_eqrel_closed_opt_view
      cmp cap m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: Memory.closed_opt_view cap m1):
  Memory.closed_opt_view cap m2.
Proof.
  inv CLOSED; econs. eapply mem_eqrel_closed_view; eauto.
Qed.

Lemma mem_eqrel_closed_tview
      cmp tview m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: TView.closed tview m1):
  TView.closed tview m2.
Proof.
  inv CLOSED. econs; i; eapply mem_eqrel_closed_view; eauto.
Qed.

Lemma lower_mem_eqlerel
      m1 loc from to val r1 r2 m2
      (LOWER: Memory.lower m1 loc from to val r1 r2 m2):
  mem_eqlerel m2 m1.
Proof.
  econs; ii.
  - revert IN. erewrite Memory.lower_o; eauto. condtac; ss.
    + i. des. inv IN. exploit Memory.lower_get0; eauto. i. esplits; eauto.
      inv LOWER. inv LOWER0. auto.
    + i. esplits; eauto. refl.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. revert IN. erewrite Memory.lower_get0; eauto. i. inv IN.
      esplits; eauto. inv LOWER. inv LOWER0. auto.
    + esplits; eauto. refl.
Qed.

Lemma mem_eqrel_memory_op
      m1 m2 m1' m2' released1 released2 kind1 kind2
      cmp
      loc from to val
      (EQMEM: mem_eqrel cmp m1 m2)
      (OP1: Memory.op m1 loc from to val released1 m1' kind1)
      (OP2: Memory.op m2 loc from to val released2 m2' kind2):
  Memory.op_kind_match kind1 kind2.
Proof.
  inv OP1; inv OP2; try by econs.
  - exploit Memory.split_get0; eauto. i. des.
    apply EQMEM in GET3. des.
    inv ADD. inv ADD0. exfalso. eapply DISJOINT; eauto.
    + apply Interval.mem_ub. auto.
    + inv SPLIT. inv SPLIT0. econs; auto. left. auto.
  - exploit Memory.lower_get0; eauto. i.
    apply EQMEM in x0. des.
    erewrite Memory.add_get0 in IN; eauto. congr.
  - exploit Memory.split_get0; eauto. i. des.
    apply EQMEM in GET3. des.
    inv ADD. inv ADD0. exfalso. eapply DISJOINT; eauto.
    + apply Interval.mem_ub. auto.
    + inv SPLIT. inv SPLIT0. econs; auto. left. auto.
  - exploit Memory.split_get0; try exact SPLIT; eauto. i. des.
    apply EQMEM in GET3. des.
    exploit Memory.split_get0; eauto. i. des.
    exploit MemoryFacts.get_same_from; [exact IN|exact GET3|..].
    { ii. subst. inv SPLIT. inv SPLIT1. inv TS23. }
    { ii. subst. inv SPLIT0. inv SPLIT1. inv TS23. }
    i. des. inv x1. econs; ss.
  - exploit Memory.lower_get0; eauto. i.
    apply EQMEM in x0. des.
    exploit Memory.split_get0; eauto. i. des. congr.
  - exploit Memory.lower_get0; eauto. i.
    apply EQMEM in x0. des.
    erewrite Memory.add_get0 in IN; eauto. congr.
  - exploit Memory.lower_get0; eauto. i.
    apply EQMEM in x0. des.
    exploit Memory.split_get0; eauto. i. des. congr.
Qed.

Lemma mem_eqlerel_add
      loc from to val released
      m1 m2 m2'
      (MEMLE: mem_eqlerel m1 m2)
      (ADD2: Memory.add m2 loc from to val released m2'):
  exists m1',
    <<ADD1: Memory.add m1 loc from to val released m1'>> /\
    <<MEMLE': mem_eqlerel m1' m2'>>.
Proof.
  exploit (@Memory.add_exists m1 loc from to);
    try by inv ADD2; inv ADD; eauto.
  { i. destruct msg2. eapply MEMLE in GET2. des.
    inv ADD2. inv ADD. eapply DISJOINT. eauto.
  }
  i. des. esplits; eauto.
  econs; splits; ii; revert IN.
  - erewrite Memory.add_o; eauto. erewrite (@Memory.add_o m2'); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + i. eapply MEMLE. eauto.
  - erewrite Memory.add_o; eauto. erewrite (@Memory.add_o mem2); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + i. eapply MEMLE. eauto.
Qed.

Lemma mem_eqlerel_split
      loc ts1 ts2 ts3 val2 val3 released2 released3
      m1 m2 m2' prm prm'
      (MEMLE: mem_eqlerel m1 m2)
      (PRM1: Memory.le prm m1)
      (SPLIT2: Memory.split m2 loc ts1 ts2 ts3 val2 val3 released2 released3 m2')
      (SPLITP2: Memory.split prm loc ts1 ts2 ts3 val2 val3 released2 released3 prm'):
  exists m1',
    <<SPLIT2: Memory.split m1 loc ts1 ts2 ts3 val2 val3 released2 released3 m1'>> /\
    <<MEMLE': mem_eqlerel m1' m2'>>.
Proof.
  exploit Memory.split_get0; eauto. i. des. apply PRM1 in GET3.
  exploit (@Memory.split_exists m1 loc ts1 ts2 ts3);
    try by inv SPLIT2; inv SPLIT; eauto. i. des.
  esplits; eauto.
  econs; splits; ii; revert IN.
  - erewrite Memory.split_o; eauto. erewrite (@Memory.split_o m2'); eauto.
    repeat condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + guardH o. i. des. inv IN. esplits; eauto. refl.
    + eapply MEMLE.
  - erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); eauto.
    repeat condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + guardH o. i. des. inv IN. esplits; eauto. refl.
    + eapply MEMLE.
Qed.

Lemma mem_eqlerel_lower
      loc from to val released1 released2
      m1 m2 m2' prm prm'
      (MEMLE: mem_eqlerel m1 m2)
      (PRM1: Memory.le prm m1)
      (LOWER2: Memory.lower m2 loc from to val released1 released2 m2')
      (LOWERP2: Memory.lower prm loc from to val released1 released2 prm'):
  exists m1',
    <<LOWER1: Memory.lower m1 loc from to val released1 released2 m1'>> /\
    <<MEMLE': mem_eqlerel m1' m2'>>.
Proof.
  exploit Memory.lower_get0; eauto. i. apply PRM1 in x0.
  exploit (@Memory.lower_exists m1 loc from to val released1 released2);
    try by inv LOWER2; inv LOWER; eauto; try by viewtac. i. des.
  esplits; eauto.
  econs; esplits; ii; revert IN.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o m2'); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + eapply MEMLE.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto. refl.
    + eapply MEMLE.
Qed.

Lemma mem_eqlerel_promise
      loc from to val released kind
      m1 m2 m2' prm prm'
      (MEMLE: mem_eqlerel m1 m2)
      (PRM1: Memory.le prm m1)
      (PROMISE2: Memory.promise prm m2 loc from to val released prm' m2' kind):
  exists m1',
    <<PROMISE1: Memory.promise prm m1 loc from to val released prm' m1' kind>> /\
    <<MEMLE': mem_eqlerel m1' m2'>>.
Proof.
  inv PROMISE2.
  - exploit mem_eqlerel_add; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit mem_eqlerel_split; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit mem_eqlerel_lower; eauto. i. des.
    esplits; eauto. econs; eauto.
Qed.

Lemma mem_eqlerel_add_forward
      loc from to val released1 released2
      m1 m2 m2'
      (MEMLE: mem_eqlerel m2 m1)
      (ADD2: Memory.add m2 loc from to val released2 m2')
      (RELLE: View.opt_le released2 released1)
      (RELWF: View.opt_wf released1):
  exists m1',
    <<ADD1: Memory.add m1 loc from to val released1 m1'>> /\
    <<MEMLE': mem_eqlerel m2' m1'>>.
Proof.
  exploit (@Memory.add_exists m1 loc from to); eauto;
    try by inv ADD2; inv ADD; eauto.
  { i. destruct msg2. eapply MEMLE in GET2. des.
    inv ADD2. inv ADD. eapply DISJOINT. eauto.
  }
  i. des. esplits; eauto.
  econs; splits; ii; revert IN.
  - erewrite Memory.add_o; eauto. erewrite (@Memory.add_o mem2); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto.
    + i. eapply MEMLE. eauto.
  - erewrite Memory.add_o; eauto. erewrite (@Memory.add_o m2'); eauto.
    condtac; ss.
    + i. des. inv IN. esplits; eauto.
    + i. eapply MEMLE. eauto.
Qed.

Lemma mem_eqlerel_split_forward
      loc ts1 ts2 ts3 val2 val3 released2 released2' released3
      m1 m2 m2'
      (MEMLE: mem_eqlerel m2 m1)
      (SPLIT2: Memory.split m2 loc ts1 ts2 ts3 val2 val3 released2 released3 m2')
      (RELLE: View.opt_le released2 released2')
      (RELWF: View.opt_wf released2'):
  exists released3' m1',
    <<SPLIT2: Memory.split m1 loc ts1 ts2 ts3 val2 val3 released2' released3' m1'>> /\
    <<MEMLE': mem_eqlerel m2' m1'>>.
Proof.
  exploit Memory.split_get0; eauto. i. des.
  apply MEMLE in GET3. i. des.
  exploit (@Memory.split_exists m1 loc ts1 ts2 ts3); eauto;
    try by inv SPLIT2; inv SPLIT; eauto. i. des.
  esplits; eauto.
  econs; splits; ii; revert IN0.
  - erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); eauto.
    repeat condtac; ss.
    + i. des. inv IN0. esplits; eauto.
    + guardH o. i. des. inv IN0. esplits; eauto.
    + eapply MEMLE.
  - erewrite Memory.split_o; eauto. erewrite (@Memory.split_o m2'); eauto.
    repeat condtac; ss.
    + i. des. inv IN0. esplits; eauto.
    + guardH o. i. des. inv IN0. esplits; eauto.
    + eapply MEMLE.
Qed.

Lemma mem_eqlerel_lower_forward
      loc from to val released1 released2
      m1 m2 m2'
      (MEMLE: mem_eqlerel m2 m1)
      (LOWER2: Memory.lower m2 loc from to val released1 released2 m2'):
  exists released1' m1',
    <<LOWER1: Memory.lower m1 loc from to val released1' released2 m1'>> /\
    <<MEMLE': mem_eqlerel m2' m1'>>.
Proof.
  exploit Memory.lower_get0; eauto. i.
  apply MEMLE in x0. des.
  exploit (@Memory.lower_exists m1 loc from to val rel2 released2); eauto;
    try by inv LOWER2; inv LOWER; eauto; try by viewtac.
  { etrans; eauto. inv LOWER2. inv LOWER. auto. }
  i. des.
  esplits; eauto.
  econs; esplits; ii; revert IN0.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
    condtac; ss.
    + i. des. inv IN0. esplits; eauto. refl.
    + eapply MEMLE.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o m2'); eauto.
    condtac; ss.
    + i. des. inv IN0. esplits; eauto. refl.
    + eapply MEMLE.
Qed.
