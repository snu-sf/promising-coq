Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import DRFBase.
Require Import SmallStep.
Require Import Race.
Require Import PIStep.

Require Import FulfillStep.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Definition TimeMap_lift (l: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec l y then Time.join (tm y) t else tm y.

Definition Capability_lift (l: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift l t rw) (TimeMap_lift l t sc)
  end.

Lemma TimeMap_lift_incr l t tm:
  TimeMap.le tm (TimeMap_lift l t tm).
Proof.
  ii. unfold TimeMap_lift. condtac; try refl. apply Time.join_l.
Qed.

Lemma TimeMap_lift_mon l t tm1 tm2
      (LE: TimeMap.le tm1 tm2):
  TimeMap.le (TimeMap_lift l t tm1) (TimeMap_lift l t tm2).
Proof.
  ii. unfold TimeMap_lift. condtac; auto.
  apply Time.join_spec.
  - rewrite <- Time.join_l. auto.
  - apply Time.join_r.
Qed.

Lemma Capability_lift_wf l t cap
      (WF: Capability.wf cap):
  Capability.wf (Capability_lift l t cap).
Proof.
  unfold Capability_lift. destruct cap. inv WF. econs; ss.
  - etrans; eauto. apply TimeMap_lift_incr.
  - apply TimeMap_lift_mon. auto.
Qed.

Lemma Capability_lift_incr l t cap:
  Capability.le cap (Capability_lift l t cap).
Proof.
  unfold Capability_lift. destruct cap. econs; try refl.
  - apply TimeMap_lift_incr.
  - apply TimeMap_lift_incr.
Qed.

Lemma Capability_lift_mon l t cap1 cap2
      (LE: Capability.le cap1 cap2):
  Capability.le (Capability_lift l t cap1) (Capability_lift l t cap2).
Proof.
  inv LE. unfold Capability_lift. destruct cap1, cap2. econs; ss.
  - apply TimeMap_lift_mon. auto.
  - apply TimeMap_lift_mon. auto.
Qed.

Inductive Memory_op mem1 loc from to val rel mem2: forall (kind:Memory.promise_kind), Prop :=
| Memory_op_add
    (ADD: Memory.add mem1 loc from to val rel mem2):
    Memory_op mem1 loc from to val rel mem2 Memory.promise_kind_add
| Memory_op_split
    to3 val3 rel3
    (SPLIT: Memory.split mem1 loc from to to3 val val3 rel rel3 mem2):
    Memory_op mem1 loc from to val rel mem2 (Memory.promise_kind_split to3 val3 rel3)
| Memory_op_change
    rel0
    (LOWER: Memory.lower mem1 loc from to val rel0 rel mem2):
    Memory_op mem1 loc from to val rel mem2 (Memory.promise_kind_lower rel0)
.

Lemma memory_op_get
      m1 l f t v r m2 k
      (OP: Memory_op m1 l f t v r m2 k):
  Memory.get l t m2 = Some (f, Message.mk v r).
Proof.
  inv OP.
  - erewrite Memory.add_o; eauto. condtac; ss. des; congr.
  - erewrite Memory.split_o; eauto. condtac; ss. des; congr.
  - erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
Qed.

Definition pi_step_lift_mem l t p k (e:ThreadEvent.t) M1 M2 : Prop :=
  match ThreadEvent.is_writing e with
  | Some (loc,from,to,val,rel,ord) =>
    <<NOPRM: Memory.get loc to p = None>> /\
    <<DISJ: forall t' v' r' (KIND: k = Memory.promise_kind_split t' v' r'), Memory.get loc t' p = None>> /\
    <<PMREL: Memory_op M1 loc from to val (if Loc.eq_dec l loc then rel else Capability_lift l t rel) M2 k>>
  | None =>
    M1 = M2
  end.

Definition msg_add e msgs := 
  match ThreadEvent.is_writing e with
  | Some (loc, from, ts, val, rel, ord) => (loc,ts)::msgs
  | None => msgs
  end.

Inductive thread_event_eqlerel: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| teel_promise loc from to val rel1 rel2
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.promise loc from to val rel1) (ThreadEvent.promise loc from to val rel2) 
| teel_silent:
  thread_event_eqlerel (ThreadEvent.silent) (ThreadEvent.silent)
| teel_read loc ts val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.read loc ts val rel1 ord) (ThreadEvent.read loc ts val rel2 ord)
| teel_write loc from to val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.write loc from to val rel1 ord) (ThreadEvent.write loc from to val rel2 ord)
| teel_update loc tsr tsw valr valw relr1 relr2 relw1 relw2 ordr ordw
    (LEREL: Capability.le relr1 relr2)
    (LEREL: Capability.le relw1 relw2):
  thread_event_eqlerel (ThreadEvent.update loc tsr tsw valr valw relr1 relw1 ordr ordw) (ThreadEvent.update loc tsr tsw valr valw relr2 relw2 ordr ordw)
| teel_fence ordr ordw:
  thread_event_eqlerel (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
| teel_syscall e:
  thread_event_eqlerel (ThreadEvent.syscall e) (ThreadEvent.syscall e)
.

Lemma remove_pi_step_lift_mem
      l t prm prm' k e
      loc from to val released
      (REMOVE: Memory.remove prm loc from to val released prm'):
  pi_step_lift_mem l t prm k e <2= pi_step_lift_mem l t prm' k e.
Proof.
  unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|]; auto.
  i. des. esplits; eauto.
  - erewrite Memory.remove_o; eauto. condtac; ss.
  - i. subst. erewrite Memory.remove_o; eauto. condtac; ss.
    eapply DISJ; eauto.
Qed.

Inductive pi_step_lift_except_aux l t (tid_except:Ident.t) e: (Configuration.t*Configuration.t*Memory.t) -> (Configuration.t*Configuration.t*Memory.t) -> Prop :=
| pi_step_lift_except_intro tid k cS1 cS2 cT1 cT2 M1 M2 lst lc
    (PI_STEP: pi_step false tid e (cS1,cT1) (cS2,cT2))
    (FIND: IdentMap.find tid_except cT2.(Configuration.threads) = Some (lst,lc))
    (MEM: pi_step_lift_mem l t lc.(Local.promises) k e M1 M2)
    (TID: tid <> tid_except):
  pi_step_lift_except_aux l t tid_except e (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift_except_aux.

Definition pi_step_lift_except l t tid_except := step_union (pi_step_lift_except_aux l t tid_except).
Hint Unfold pi_step_lift_except.

Definition mem_eqrel (cmp: Loc.t -> Time.t -> Capability.t -> Capability.t -> Prop) (m1 m2: Memory.t) : Prop :=
  <<LR: mem_sub cmp m1 m2>> /\
  <<RL: mem_sub (fun l t x y => cmp l t y x) m2 m1>>.
Hint Unfold mem_eqrel.

Definition mem_eqlerel (m1 m2: Memory.t) : Prop :=
  mem_eqrel (fun _ _ => Capability.le) m1 m2.
Hint Unfold mem_eqlerel.

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

Definition Capability_lift_le l t (msgs: list (Loc.t*Time.t)) loc ts cap1 cap2 : Prop :=
  cap1 = cap2 \/ (List.In (loc,ts) msgs /\ cap2 = Capability_lift l t cap1).
Hint Unfold Capability_lift_le.

Global Program Instance Capability_lift_le_PreOrder l t msgs loc ts : PreOrder (Capability_lift_le l t msgs loc ts).
Next Obligation. 
  ii. unfold Capability_lift_le in *.
  des; subst; eauto.
  right. destruct x. s.
  splits; eauto.
  unfold TimeMap_lift.
  f_equal.
  - extensionality y. destruct (LocSet.Facts.eq_dec l y); eauto.
    apply TimeFacts.antisym; repeat apply Time.join_spec;
      (try apply Time.join_l);
      (try apply Time.join_r).
    rewrite <- ? Time.join_l. refl.
  - extensionality y. destruct (LocSet.Facts.eq_dec l y); eauto.
    apply TimeFacts.antisym; repeat apply Time.join_spec;
      (try apply Time.join_l);
      (try apply Time.join_r).
    rewrite <- ? Time.join_l. refl.
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

Inductive mem_eqlerel_lift l t p k e (m1 m2: Memory.t) : Prop :=
| mem_le_lift_intro m1'
  (MEMEQ: mem_eqlerel m1 m1')
  (MEMWR: pi_step_lift_mem l t p k e m1' m2)
.

Definition conf_update_memory (c: Configuration.t) (m: Memory.t) : Configuration.t :=
 Configuration.mk c.(Configuration.threads) c.(Configuration.sc) m.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 l t tid
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  rtc (pi_step_except false tid) cSTM1.(fst) cSTM2.(fst).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. inv USTEP. econs; eauto.
Qed.

Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid l t
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(fst).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(fst).(Configuration.threads) /\
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads).
Proof.
  apply pi_steps_lift_except_pi_steps in STEPS.
  apply rtc_pi_step_except_find in STEPS. eauto.
Qed.

Lemma mem_eqlerel_add_forward
      loc from to val released1 released2
      m1 m2 m2'
      (MEMLE: mem_eqlerel m2 m1)
      (ADD2: Memory.add m2 loc from to val released2 m2')
      (RELLE: Capability.le released2 released1)
      (RELWF: Capability.wf released1):
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
      (RELLE: Capability.le released2 released2')
      (RELWF: Capability.wf released2'):
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
      loc from to val released1 released2 released2'
      m1 m2 m2'
      (MEMLE: mem_eqlerel m2 m1)
      (LOWER2: Memory.lower m2 loc from to val released1 released2 m2')
      (RELLE: Capability.le released2 released2')
      (RELWF: Capability.wf released2'):
  exists released1' m1',
    <<LOWER1: Memory.lower m1 loc from to val released1' released2' m1'>> /\
    <<MEMLE': mem_eqlerel m2' m1'>>.
Proof.
  exploit Memory.lower_get0; eauto. i.
  apply MEMLE in x0. des.
  exploit (@Memory.lower_exists m1 loc from to val rel2 released2'); eauto;
    try by inv LOWER2; inv LOWER; eauto; try by committac.
  { admit. (* we have to use something different than lower *) }
  i. des.
  esplits; eauto.
  econs; esplits; ii; revert IN0.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
    condtac; ss.
    + i. des. inv IN0. esplits; eauto.
    + eapply MEMLE.
  - erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o m2'); eauto.
    condtac; ss.
    + i. des. inv IN0. esplits; eauto.
    + eapply MEMLE.
Admitted.

Definition Capability_lift_if loc l t rel :=
  if Loc.eq_dec l loc then rel else Capability_lift l t rel.

Lemma Capability_lift_if_wf loc l t rel
      (WF: Capability.wf rel):
  Capability.wf (Capability_lift_if loc l t rel).
Proof.
  unfold Capability_lift_if. condtac; auto.
  apply Capability_lift_wf. auto.
Qed.

Lemma Capability_lift_if_incr loc l t rel:
  Capability.le rel (Capability_lift_if loc l t rel).
Proof.
  unfold Capability_lift_if. condtac; [refl|].
  apply Capability_lift_incr.
Qed.

Lemma Capability_lift_if_mon loc l t rel1 rel2
      (LE: Capability.le rel1 rel2):
  Capability.le (Capability_lift_if loc l t rel1) (Capability_lift_if loc l t rel2).
Proof.
  unfold Capability_lift_if. condtac; auto.
  apply Capability_lift_mon. auto.
Qed.

Lemma write_step_pi_step_lift_mem
      lc0 sc0 mem0 mem0'
      lc1 sc1 mem1
      loc from to val releasedm released ord kind
      lco l t
      (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem1 kind)
      (EQLEREL: mem_eqlerel mem0 mem0')
      (RELM_WF: Capability.wf releasedm)
      (RELM_CLOSED: Memory.closed_capability releasedm mem0)
      (LOCAL1: Local.wf lc0 mem0)
      (LOCAL2: Local.wf lco mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (DISJ: Local.disjoint lc0 lco):
  exists mem1' kind',
    <<LIFT: forall e (E: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)),
      pi_step_lift_mem l t lco.(Local.promises) kind' e mem0' mem1'>> /\
    <<EQLEREL: mem_eqlerel mem1 mem1'>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.promise_step_disjoint; eauto. i. des.
  exploit Capability_lift_if_wf; eauto. i.
  inv STEP1. inv PROMISE.
  - exploit mem_eqlerel_add_forward; eauto.
    { apply Capability_lift_if_incr. }
    i. des. esplits; eauto. i.
    unfold pi_step_lift_mem. rewrite E. splits; cycle 2.
    + econs 1; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.add_o; eauto. condtac; ss. des; congr.
    + congr.
  - exploit mem_eqlerel_split_forward; eauto.
    { apply Capability_lift_if_incr. }
    i. des. esplits; eauto. i.
    unfold pi_step_lift_mem. rewrite E. splits; cycle 2.
    + econs 2; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.split_o; eauto. condtac; ss. des; congr.
    + i. inv KIND. destruct (Memory.get loc t' (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJ; eauto.
      hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
  - exploit mem_eqlerel_lower_forward; eauto.
    { apply Capability_lift_if_incr. }
    i. des. esplits; eauto. i.
    unfold pi_step_lift_mem. rewrite E. splits; cycle 2.
    + econs 3; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
    + congr.
Qed.

Lemma pi_step_lifting_aux
      tid cS1 cT1 cS2 cT2 M1 l t
      (PISTEP: pi_step_except false tid (cS1,cT1) (cS2,cT2))
      (FIND: IdentMap.find tid cT2.(Configuration.threads) <> None)
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQLEREL: mem_eqlerel cT1.(Configuration.memory) M1):
  exists M2, 
  pi_step_lift_except l t tid (cS1,cT1,M1) (cS2,cT2,M2) /\
  mem_eqlerel cT2.(Configuration.memory) M2.
Proof.
  inv PISTEP. inv PI_STEP. assert (X:= USTEP). inv X.
  destruct (IdentMap.find tid cT2.(Configuration.threads)) as [[]|]eqn: EQ; [|by exfalso; eauto].
  inv STEPT. inv STEP; inv STEP0; try by esplits; s; eauto; econs; econs; eauto; ss.
  { inversion WF. subst.
    ss. generalize EQ. i. rewrite IdentMap.gso in EQ0; eauto. destruct s.
    exploit write_step_pi_step_lift_mem; eauto; try apply WFT; try by committac.
    { inv WFT. committac. }
    { eapply WFT. eauto. }
    { eapply WFT. apply EQ0. }
    { eapply WFT; eauto. }
    i. des. esplits; eauto.
  }
  { inversion WF. subst.
    ss. generalize EQ. i. rewrite IdentMap.gso in EQ0; eauto. destruct s.
    exploit Local.read_step_future; try eapply WFT; eauto. i. des.
    exploit Local.read_step_disjoint; try exact LOCAL1.
    { eapply WFT. eauto. }
    { eapply WFT; eauto. }
    { eapply WFT. eauto. }
    i. des.
    exploit write_step_pi_step_lift_mem; try exact x1; eauto; try apply WFT.
    { eapply WFT. eauto. }
    i. des. esplits; eauto.
  }
Grab Existential Variables.
  { apply Memory.promise_kind_add. }
  { apply Memory.promise_kind_add. }
  { apply Memory.promise_kind_add. }
  { apply Memory.promise_kind_add. }
  { apply Capability.bot. }
  { apply Capability.bot. }
  { apply Memory.promise_kind_add. }
Qed.

Lemma rtc_pi_step_lifting_aux
      tid cST1 cST2 M1 l t
      (PISTEP: rtc (pi_step_except false tid) cST1 cST2)
      (FIND: IdentMap.find tid cST2.(snd).(Configuration.threads) <> None)
      (WF: pi_wf loctmeq cST1)
      (EQLEREL: mem_eqlerel cST1.(snd).(Configuration.memory) M1):
  exists M2, 
  rtc (pi_step_lift_except l t tid) (cST1,M1) (cST2,M2) /\
  mem_eqlerel cST2.(snd).(Configuration.memory) M2.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff, 
        Operators_Properties.clos_rt_rtn1_iff in PISTEP.
  ginduction PISTEP; eauto.
  apply Operators_Properties.clos_rt_rtn1_iff, 
        Operators_Properties.clos_rt_rt1n_iff in PISTEP.

  i. exploit IHPISTEP; eauto.
  { inv H. inv PI_STEP. inv USTEP.
    exploit small_step_find; eauto.
    intro TEQ. ss. rewrite <-TEQ in FIND. eauto. }
  intro RES. des.

  destruct y, z.
  exploit pi_step_lifting_aux; eauto.
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, PISTEP. i. inv PR. eauto. }
  intro STEP'; des.

  esplits.
  - etrans; [eauto|].
    econs; [|reflexivity]; eauto.
  - eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 l t
      (PI_STEPS: rtc (pi_step_except false tid) cST1 cST2)
      (FIND: IdentMap.find tid cST2.(snd).(Configuration.threads) <> None)
      (WF: pi_wf loctmeq cST1):
  exists M2, rtc (pi_step_lift_except l t tid) (cST1,cST1.(snd).(Configuration.memory)) (cST2,M2).
Proof.
  exploit rtc_pi_step_lifting_aux; eauto; cycle 1.
  - i; des. eauto.
  - rr. split; ii; esplits; eauto; reflexivity.
Qed.

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

Lemma mem_eqrel_closed_capability
      cmp cap m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: Memory.closed_capability cap m1):
  Memory.closed_capability cap m2.
Proof.
  inv CLOSED. econs; eapply mem_eqrel_closed_timemap; eauto.
Qed.

Lemma mem_eqrel_closed_commit
      cmp commit m1 m2
      (EQMEM: mem_eqrel cmp m1 m2)
      (CLOSED: Commit.closed commit m1):
  Commit.closed commit m2.
Proof.
  inv CLOSED. econs; i; eapply mem_eqrel_closed_capability; eauto.
Qed.

Lemma TimeMap_lift_closed_timemap
      tm mem l t
      (CLOSED: Memory.closed_timemap tm mem)
      (GET: Memory.get l t mem <> None):
  Memory.closed_timemap (TimeMap_lift l t tm) mem.
Proof.
  ii. unfold TimeMap_lift. condtac.
  - subst. destruct (Time.join_cases (tm loc) t); rewrite H.
    + apply CLOSED.
    + destruct (Memory.get loc t mem) as [[? []]|] eqn:X; eauto. congr.
  - apply CLOSED.
Qed.

Lemma Capability_lift_closed_capability
      cap mem l t
      (CLOSED: Memory.closed_capability cap mem)
      (GET: Memory.get l t mem <> None):
  Memory.closed_capability (Capability_lift l t cap) mem.
Proof.
  destruct cap. ss. inv CLOSED. econs; ss.
  - apply TimeMap_lift_closed_timemap; auto.
  - apply TimeMap_lift_closed_timemap; auto.
Qed.

Lemma conf_update_memory_wf
      l t msgs cS1 cT1 M1
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQMEM: mem_eqrel (Capability_lift_le l t msgs) cT1.(Configuration.memory) M1)
      (IN: Memory.get l t cT1.(Configuration.memory) <> None):
  pi_wf (Capability_lift_le l t msgs) (cS1,conf_update_memory cT1 M1).
Proof.
  econs; inv WF; try done.
  - inv WFT. econs; s.
    + inv WF. econs; ss. i. exploit THREADS; eauto. i.
      inv x. econs; eauto.
      * eapply mem_eqrel_closed_commit; eauto.
      * admit. (* promise <= mem *)
    + eapply mem_eqrel_closed_timemap; eauto.
    + inv MEM. econs.
      * i. inv EQMEM. des. exploit H0; eauto. i. des.
        exploit CLOSED; eauto. i. des. inv CMP.
        { splits; auto. eapply mem_eqrel_closed_capability; eauto. }
        { des. subst. splits.
          - apply Capability_lift_wf. auto.
          - unfold Capability_lift. destruct rel2. ss.
            unfold TimeMap_lift. condtac; ss. subst.
            admit. (* released.rw loc <= to *)
          - eapply mem_eqrel_closed_capability; eauto.
            eapply Capability_lift_closed_capability; eauto.
        }
      * ii. specialize (INHABITED loc). apply EQMEM in INHABITED. des.
        inv CMP; auto.
        admit. (* inhabited *)
  - i. exploit LR; eauto. i. des.
    apply EQMEM in IN1. des.
    esplits; eauto. inv CMP. auto.
  - i. apply EQMEM in IN0. des.
    exploit RL; eauto. i. des.
    esplits; eauto. inv CMP0. auto.
Admitted.

Lemma small_step_write_closed
      tid c c1 e loc from ts val rel ord withprm
      (WF: Configuration.wf c)
      (STEP: small_step withprm tid e c c1)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)):
  <<CLOSED: Memory.closed_capability rel c1.(Configuration.memory)>> /\
  <<TS: Time.le (rel.(Capability.rw) loc) ts>>.

Proof.
  inv STEP. inv STEP0; inv STEP; inv EVENT.
  - inv WF.
    exploit Local.write_step_future; eauto; try by committac.
    { eapply WF0. eauto. }
    i. des. splits; eauto.
  - inv WF.
    exploit Local.read_step_future; eauto.
    { eapply WF0. eauto. }
    i. des.
    exploit Local.write_step_future; eauto.
    i. des. splits; eauto.
Qed.

Lemma pi_step_lift_except_future
      l t msgs tid cS1 cT1 cS2 cT2 M1 M2 e
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQMEM: mem_eqrel (Capability_lift_le l t msgs) cT1.(Configuration.memory) M1)
      (IN: Memory.get l t cT1.(Configuration.memory) <> None)
      (PI_STEP: pi_step_lift_except_aux l t tid e (cS1,cT1,M1) (cS2,cT2,M2))
:
  <<EQMEM: mem_eqrel (Capability_lift_le l t (msg_add e msgs)) cT2.(Configuration.memory) M2>> /\
  <<IN: Memory.get l t cT2.(Configuration.memory) <> None>> /\
  <<MEMFUT: Memory.future M1 M2>> /\
  <<TIMELE: TimeMap.le cT1.(Configuration.sc) cT2.(Configuration.sc)>>.
Proof.
  assert (EQMEM2: mem_eqrel (Capability_lift_le l t (msg_add e msgs)) cT2.(Configuration.memory) M2).
  { unfold mem_eqrel. splits.
    - admit. (* mem_eqrel *)
    - admit. (* mem_eqrel *)
  }
  assert (IN2: Memory.get l t cT2.(Configuration.memory) <> None).
  { destruct (Memory.get l t (Configuration.memory cT1)) as [[? []]|] eqn:X; [|congr].
    inv PI_STEP. inv PI_STEP0. exploit small_step_future; eauto.
    { inv WF. auto. }
    i. des. exploit Memory.future_get; eauto. i. des.
    rewrite GET. congr.
  }
  inv PI_STEP. splits; auto.
  - revert MEM. unfold pi_step_lift_mem.
    destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
    { i. subst. refl. }
    i. des. econs 2; eauto.
    inv PI_STEP0. subst. exploit small_step_write_closed; eauto.
    { inv WF. auto. }
    i. des. inv PMREL.
    + econs 1; eauto.
      * eapply mem_eqrel_closed_capability; eauto. condtac; ss.
        eapply Capability_lift_closed_capability; eauto.
      * condtac; ss.
        destruct t4. ss. unfold TimeMap_lift. condtac; ss.
    + econs 2; eauto.
      * eapply mem_eqrel_closed_capability; eauto. condtac; ss.
        eapply Capability_lift_closed_capability; eauto.
      * condtac; ss.
        destruct t4. ss. unfold TimeMap_lift. condtac; ss.
    + econs 3; eauto.
      * eapply mem_eqrel_closed_capability; eauto. condtac; ss.
        eapply Capability_lift_closed_capability; eauto.
      * condtac; ss.
        destruct t4. ss. unfold TimeMap_lift. condtac; ss.
      * admit. (* capability le (lowering) *)
  - inv PI_STEP0.
    eapply small_step_future; eauto.
    inv WF. auto.
Admitted.

Lemma rtc_pi_step_lift_except_future
      l t tid cS1 cT1 cSTM2 lst1 lc1
      (WF: pi_wf loctmeq (cS1,cT1))
      (IN: Memory.get l t cT1.(Configuration.memory) <> None)
      (PI_STEPS: rtc (pi_step_lift_except l t tid) (cS1,cT1,cT1.(Configuration.memory)) cSTM2)
      (FIND: IdentMap.find tid cT1.(Configuration.threads) = Some (lst1,lc1)):
  <<WF: exists msgs, pi_wf (Capability_lift_le l t msgs) (cSTM2.(fst).(fst),(conf_update_memory cSTM2.(fst).(snd) cSTM2.(snd)))>> /\
  <<MEMFUT: Memory.future cT1.(Configuration.memory) cSTM2.(snd)>> /\
  <<TIMELE: TimeMap.le cT1.(Configuration.sc) cSTM2.(fst).(snd).(Configuration.sc)>> /\
  <<LOCWF: Local.wf lc1 cSTM2.(snd)>> /\
  <<MEMCLOTM: Memory.closed_timemap (cSTM2.(fst).(snd).(Configuration.sc)) cSTM2.(snd)>> /\
  <<MEMCLO: Memory.closed cSTM2.(snd)>>.
Proof.
  apply (@proj2 (<<EQMEM: exists msgs, mem_eqrel (Capability_lift_le l t msgs) cSTM2.(fst).(snd).(Configuration.memory) cSTM2.(snd)>> /\
                 <<IN: Memory.get l t cSTM2.(fst).(snd).(Configuration.memory) <> None>>)).
  revert FIND.
  apply Operators_Properties.clos_rt_rt1n_iff, 
        Operators_Properties.clos_rt_rtn1_iff in PI_STEPS.
  induction PI_STEPS.
  { set (X:=WF). inv X. inv WFT. inv WF0. destruct lst1.
    i; esplits; s; eauto; try reflexivity. 
    split; ii; esplits; eauto. 
    eapply conf_update_memory_wf; eauto.
    split; ii; esplits; eauto.
  }
  apply Operators_Properties.clos_rt_rtn1_iff, 
        Operators_Properties.clos_rt_rt1n_iff in PI_STEPS.

  i. exploit IHPI_STEPS; eauto. i; des. clear IHPI_STEPS.
  inv H. destruct y as [[]], z as [[]].
  exploit pi_step_lift_except_future; try apply USTEP; eauto. 
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
    i. inv PR. eauto. }
  i; des. destruct lst1.

  exploit conf_update_memory_wf; [|eauto|eauto|].
  { eapply rtc_pi_step_future; eauto.
    etrans.
    - eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
      i. inv PR. eauto.
    - s. econs 2; [|reflexivity]. inv USTEP. eauto. }
  intro X. inv X. inv WFT. inv WF1.
  s. esplits; eauto; try etrans; eauto.
  { eapply conf_update_memory_wf; eauto.
    eapply rtc_pi_step_future; eauto.
    etrans. 
    { eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
      i; inv PR; eauto. }
    ss. inv USTEP.
    econs 2; [|reflexivity]. eauto. }

  eapply THREADS. s.

  hexploit rtc_pi_step_lift_except_find.
  { etrans; [eauto|].
    econs 2; [|reflexivity]. eauto. }
  s. intro EQ. des. rewrite <-EQ0.
  eauto.
Grab Existential Variables. exact []. exact [].
Qed.

Lemma mem_eqlerel_get
      m1 m2
      l f t v r2
      (LE: mem_eqlerel m1 m2)
      (GET2: Memory.get l t m2 = Some (f, Message.mk v r2)):
  exists r1,
    <<GET1: Memory.get l t m1 = Some (f, Message.mk v r1)>> /\
    <<REL: Capability.le r1 r2>>.
Proof. inv LE. des. exploit H0; eauto. Qed.

Lemma Memory_op_get
      mem1 loc from to val released mem2 kind
      l f t v r
      (OP: Memory_op mem1 loc from to val released mem2 kind)
      (GET2: Memory.get l t mem2 = Some (f, Message.mk v r)):
  (l = loc /\ f = from /\ t = to /\ v = val /\ r = released) \/
  (__guard__ (l <> loc \/ t <> to) /\
   exists f',
     <<GET1: Memory.get l t mem1 = Some (f', Message.mk v r)>> /\
     <<FROM: Time.le f' f>>).
Proof.
  revert GET2. inv OP.
  - erewrite Memory.add_o; eauto. condtac; ss.
    + i. des. inv GET2. left. auto.
    + i. right. esplits; eauto. refl.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + i. des. inv GET2. left. auto.
    + guardH o. i. des. inv GET2. right. splits; auto.
      exploit Memory.split_get0; try exact MEM; eauto. i. des.
      rewrite GET3. esplits; eauto. inv SPLIT. inv SPLIT0. left. auto.
    + i. right. esplits; eauto. refl.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    + i. des. inv GET2. left. auto.
    + i. right. esplits; eauto. refl.
Qed.

Lemma mem_eqlerel_lift_get
      loc ts prm k e m1 m2 l f t v r2
      (LIFT: mem_eqlerel_lift loc ts prm k e m1 m2)
      (GET: Memory.get l t m2 = Some (f, Message.mk v r2)):
  (exists r o, ThreadEvent.is_writing e = Some (l, f, t, v, r, o)) \/
  (exists f' r1,
      <<EVT: forall o, ThreadEvent.is_writing e <> Some (l, f, t, v, r1, o)>> /\
      <<GET: Memory.get l t m1 = Some (f', Message.mk v r1)>> /\
      <<REL: Capability.le r1 r2>> /\
      <<FROM: Time.le f' f>>).
Proof.
  inv LIFT. revert MEMWR. unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[] ?] ?] ?] ?]|] eqn:E; ss.
  - i. des. exploit Memory_op_get; eauto. i. des.
    + subst. eauto.
    + exploit mem_eqlerel_get; eauto. i. des.
      right. esplits; eauto. ii. inv H. unguardH x0. des; congr.
  - i. subst. exploit mem_eqlerel_get; eauto. i. des.
    right. esplits; eauto.
    + congr.
    + refl.
Qed.

Lemma lift_read
      com1 com2 com2' m1 m2 prm l t k e loc to val rel2 ordr
      (LOCAL: Local.read_step (Local.mk com2 prm) m2 loc to val rel2 ordr (Local.mk com2' prm))
      (COM2: Commit.wf com2)
      (REL2: Capability.wf rel2)
      (CoMLE: Commit.le com1 com2)
      (MEMLE: mem_eqlerel_lift l t prm k e m1 m2):
  (exists from relw ordw,
   <<EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, relw, ordw)>>)
  \/
  (exists com1' rel1,
   <<LOCAL: Local.read_step (Local.mk com1 prm) m1 loc to val rel1 ordr (Local.mk com1' prm)>> /\
   <<CoMLE: Commit.le com1' com2'>> /\
   <<RELLE: Capability.le rel1 rel2>>).
Proof.
  inversion LOCAL. ss. subst.
  exploit mem_eqlerel_lift_get; eauto. i. des.
  - left. esplits; eauto.
  - right. esplits; ss.
    + econs; eauto. ss. eapply CommitFacts.readable_mon; eauto. refl.
    + apply CommitFacts.read_commit_mon; eauto; try refl.
    + auto.
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
    try by inv LOWER2; inv LOWER; eauto; try by committac. i. des.
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

Lemma pi_step_lift_mem_add
      loc from to val released
      m1 m2 m2' prm'
      l t prm k e
      (MEMLE: pi_step_lift_mem l t prm k e m1 m2)
      (ADD2: Memory.add m2 loc from to val released m2')
      (ADDP2: Memory.add prm loc from to val released prm'):
  exists m1',
    <<ADD1: Memory.add m1 loc from to val released m1'>> /\
    <<MEMLE': pi_step_lift_mem l t prm' k e m1' m2'>>.
Proof.
  revert MEMLE. unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. subst. esplits; eauto. }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_add; try exact MEM; eauto. i. des.
    esplits; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + congr.
    + econs; eauto.
  - exploit MemoryReorder.split_add; try exact MEM; eauto. i. des.
    esplits; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + i. inv KIND.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. congr.
    + econs; eauto.
  - exploit MemoryReorder.lower_add; try exact MEM; eauto. i. des.
    esplits; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + congr.
    + econs; eauto.
Qed.

Lemma pi_step_lift_mem_split
      loc ts1 ts2 ts3 val2 val3 released2 released3
      m1 m2 m2' prm'
      l t prm k e
      (MEMLE: pi_step_lift_mem l t prm k e m1 m2)
      (SPLIT2: Memory.split m2 loc ts1 ts2 ts3 val2 val3 released2 released3 m2')
      (SPLITP2: Memory.split prm loc ts1 ts2 ts3 val2 val3 released2 released3 prm'):
  exists m1',
    <<SPLIT2: Memory.split m1 loc ts1 ts2 ts3 val2 val3 released2 released3 m1'>> /\
    <<MEMLE': pi_step_lift_mem l t prm' k e m1' m2'>>.
Proof.
  revert MEMLE. unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. subst. esplits; eauto. }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_split; try exact MEM; eauto. i. des.
    { subst. exploit Memory.split_get0; try exact SPLITP2; eauto.
      i. des. congr.
    }
    esplits; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      { des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      }
      { guardH o. des. subst. congr. }
    + congr.
    + econs; eauto.
  - exploit MemoryReorder.split_split; try exact MEM; eauto.
    { ii. inv H. exploit DISJ; eauto. i.
      exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr.
    }
    i. des.
    { subst. exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr. }
    esplits; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.split_o; eauto. condtac; ss.
      * guardH o. des. subst. exploit Memory.split_get0; try exact SPLITP2; eauto.
        i. des. congr.
    + i. inv KIND. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.split_o; eauto. repeat condtac; ss.
      * guardH o. des. subst. exploit DISJ; eauto.
        exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr.
    + econs; eauto.
  - exploit MemoryReorder.lower_split; try exact MEM; eauto. i. des.
    unguardH FROM1. des.
    { inv FROM1. subst. exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr. }
    inv FROM0. esplits; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
      * guardH o. des. subst. congr.
    + congr.
    + econs; eauto.
Qed.

Lemma pi_step_lift_mem_lower
      loc from to val released released'
      m1 m2 m2' prm'
      l t prm k e
      (MEMLE: pi_step_lift_mem l t prm k e m1 m2)
      (LOWER2: Memory.lower m2 loc from to val released released' m2')
      (LOWERP2: Memory.lower prm loc from to val released released' prm'):
  exists m1',
    <<LOWER1: Memory.lower m1 loc from to val released released' m1'>> /\
    <<MEMLE': pi_step_lift_mem l t prm' k e m1' m2'>>.
Proof.
  revert MEMLE. unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. subst. esplits; eauto. }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_lower; try exact MEM; eauto. i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + congr.
    + econs; eauto.
  - exploit MemoryReorder.split_lower; try exact MEM; eauto.
    { ii. inv H. exploit DISJ; eauto. i.
      exploit Memory.lower_get0; try exact LOWERP2; eauto. i. congr.
    }
    i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + i. inv KIND. erewrite Memory.lower_o; eauto. condtac; ss.
      * des. subst. exploit DISJ; eauto.
        erewrite Memory.lower_get0; [|eauto]. congr.
      * eapply DISJ. eauto.
    + econs; eauto.
  - exploit MemoryReorder.lower_lower; try exact MEM; eauto. i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + congr.
    + econs; eauto.
Qed.

Lemma pi_step_lift_mem_promise
      loc from to val released kind
      m1 m2 m2' prm'
      l t prm k e
      (MEMLE: pi_step_lift_mem l t prm k e m1 m2)
      (PROMISE2: Memory.promise prm m2 loc from to val released prm' m2' kind):
  exists m1',
    <<PROMISE1: Memory.promise prm m1 loc from to val released prm' m1' kind>> /\
    <<MEMLE': pi_step_lift_mem l t prm' k e m1' m2'>>.
Proof.
  inv PROMISE2.
  - exploit pi_step_lift_mem_add; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit pi_step_lift_mem_split; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit pi_step_lift_mem_lower; eauto. i. des.
    esplits; eauto. econs; eauto.
Qed.

Lemma mem_eqlerel_lift_promise
      loc from to val released kind
      m1 m2 m2' prm'
      l t prm k e
      (MEMLE: mem_eqlerel_lift l t prm k e m1 m2)
      (PRM1: Memory.le prm m1)
      (PROMISE2: Memory.promise prm m2 loc from to val released prm' m2' kind):
  exists m1',
    <<PROMISE1: Memory.promise prm m1 loc from to val released prm' m1' kind>> /\
    <<MEMLE': mem_eqlerel_lift l t prm' k e m1' m2'>>.
Proof.
  inv MEMLE.
  exploit pi_step_lift_mem_promise; eauto. i. des.
  exploit mem_eqlerel_promise; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma lift_write
      com1 com2 com2' sc1 sc2 sc2' m1 m2 m2' prm prm' l t k e loc from to val relr1 relr2 relw2 ord kind
      (LOCAL: Local.write_step (Local.mk com2 prm) sc2 m2 loc from to val relr2 relw2 ord (Local.mk com2' prm') sc2' m2' kind)
      (PRM1: Memory.le prm m1)
      (M1: Memory.closed m1)
      (RELR1: Capability.wf relr1)
      (RELR2: Capability.wf relr2)
      (COM1: Commit.wf com1)
      (COM2: Commit.wf com2)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2)
      (REL: Capability.le relr1 relr2)
      (MEMLE: mem_eqlerel_lift l t prm k e m1 m2):
  exists com1' sc1' m1' kind' relw1,
  <<LOCAL: Local.write_step (Local.mk com1 prm) sc1 m1 loc from to val relr1 relw1 ord (Local.mk com1' prm') sc1' m1' kind'>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<RELLE: Capability.le relw1 relw2>> /\
  <<SC: TimeMap.le sc1' sc2'>> /\
  <<MEMLE: mem_eqlerel_lift l t prm' k e m1' m2'>>.
Proof.
  set (relw1 :=
             (if Ordering.le Ordering.relaxed ord
              then
               Capability.join relr1
                 (Commit.rel (Commit.write_commit com1 sc1 loc to ord) loc)
              else Capability.bot)).
  assert (RELWWF: Capability.wf relw1).
  { unfold relw1. repeat (try condtac; aggrtac).
    - apply COM1.
    - apply COM1.
  }
  assert (RELWLE: Capability.le relw1 relw2).
  { unfold relw1. inv LOCAL. repeat (try condtac; aggrtac).
    - rewrite <- Capability.join_r.
      rewrite <- ? Capability.join_l.
      apply CoMLE.
    - rewrite <- Capability.join_r.
      rewrite <- ? Capability.join_l.
      apply CoMLE.
    - apply COM2.
    - rewrite <- ? Capability.join_r. econs; committac.
    - rewrite <- Capability.join_r.
      apply CoMLE.
  }
  inv LOCAL. inv WRITE.
  exploit mem_eqlerel_lift_promise; eauto. i. des.
  hexploit Memory.promise_future0; eauto; try by committac. i. des.
  hexploit MemorySplit.remove_promise_remove; try exact REMOVE; eauto.
  { inv PROMISE; inv MEM. by inv ADD. by inv SPLIT. by inv LOWER. }
  { by inv PROMISE. }
  { inv PROMISE; inv MEM. by inv ADD. by inv SPLIT. by inv LOWER. }
  i. des.
  hexploit MemoryMerge.promise_promise_promise; try exact PROMISE1; eauto. i.
  esplits; eauto.
  - econs; eauto.
    + eapply CommitFacts.writable_mon; eauto. refl.
    + econs; eauto.
  - apply CommitFacts.write_commit_mon; auto. refl.
  - apply CommitFacts.write_sc_mon; auto. refl.
  - inv MEMLE'. econs; eauto.
    + etrans; eauto.
      eapply lower_mem_eqlerel. inv PROMISE0. eauto.
    + eapply remove_pi_step_lift_mem; [|eauto]. eauto.
Qed.

Lemma lift_fence
      sc1 sc2 sc2' com1 com2 com2' prm prm' ordr ordw
      (LOCAL: Local.fence_step (Local.mk com2 prm) sc2 ordr ordw (Local.mk com2' prm') sc2')
      (COM1: Commit.wf com1)
      (COM2: Commit.wf com2)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2):
  exists com1' sc1',
  <<LOCAL: Local.fence_step (Local.mk com1 prm) sc1 ordr ordw (Local.mk com1' prm') sc1'>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>>.
Proof.
  inversion LOCAL. ss. subst.
  esplits; eauto.
  - econs; eauto.
  - apply CommitFacts.write_fence_commit_mon; eauto; try refl.
    + apply CommitFacts.read_fence_commit_mon; eauto; try refl.
    + unfold Commit.read_fence_commit. ss.
      econs; repeat (try condtac; aggrtac; try apply COM1).
  - apply CommitFacts.write_fence_sc_mon; eauto; try refl.
    apply CommitFacts.read_fence_commit_mon; eauto; try refl.
Qed.

Lemma lift_step
      lang (thS1 thT1 thT2: @Thread.t lang) eT l t k e
      (STEP: Thread.step eT thT1 thT2)
      (NOPRM: ThreadEvent_is_promising eT = None)
      (ST: thS1.(Thread.state) = thT1.(Thread.state))
      (WFS1: Local.wf thS1.(Thread.local) thS1.(Thread.memory))
      (WFT1: Local.wf thT1.(Thread.local) thT1.(Thread.memory))
      (SCS1: Memory.closed_timemap thS1.(Thread.sc) thS1.(Thread.memory))
      (SCT1: Memory.closed_timemap thT1.(Thread.sc) thT1.(Thread.memory))
      (MEMS1: Memory.closed thS1.(Thread.memory))
      (MEMT1: Memory.closed thT1.(Thread.memory))
      (COM: Commit.le thS1.(Thread.local).(Local.commit) thT1.(Thread.local).(Local.commit))
      (PRM: thS1.(Thread.local).(Local.promises) = thT1.(Thread.local).(Local.promises))
      (SC: TimeMap.le thS1.(Thread.sc) thT1.(Thread.sc))
      (MEM: mem_eqlerel_lift l t thT1.(Thread.local).(Local.promises) k e thS1.(Thread.memory) thT1.(Thread.memory))
: 
  (exists loc ts from val relr relw ordr ordw,
   <<EVTR: ThreadEvent.is_reading eT = Some (loc, ts, val, relr, ordr)>> /\
   <<EVTW: ThreadEvent.is_writing e = Some (loc, from, ts, val, relw, ordw)>>)
  \/
  (exists eS thS2,
   <<EVT: thread_event_eqlerel eS eT>> /\
   <<STEP: Thread.step eS thS1 thS2>> /\
   <<ST: thS2.(Thread.state) = thT2.(Thread.state)>> /\
   <<COM: Commit.le thS2.(Thread.local).(Local.commit) thT2.(Thread.local).(Local.commit)>> /\
   <<PRM: thS2.(Thread.local).(Local.promises) = thT2.(Thread.local).(Local.promises)>> /\
   <<SC: TimeMap.le thS2.(Thread.sc) thT2.(Thread.sc)>> /\
   <<MEM: mem_eqlerel_lift l t thT2.(Thread.local).(Local.promises) k e thS2.(Thread.memory) thT2.(Thread.memory)>>).
Proof.
  inv STEP; inv STEP0; inv NOPRM; ss.
  - destruct lc1. subst. ss.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 1. eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_read; eauto.
    { apply WFT1. }
    { eapply MEMT1. eauto. }
    i. des.
    { left. esplits; eauto. }
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs. eauto.
    + econs 2. econs 2; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. ss. subst.
    hexploit lift_write; try exact MEM; eauto; try refl;
      try apply WFS1; try apply WFT1; try by committac. i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs. eauto.
    + econs 2. econs 3; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL1. subst. ss.
    exploit Local.read_step_future; eauto. s. i. des.
    exploit lift_read; eauto.
    { apply WFT1. }
    i. des.
    { left. esplits; eauto. }
    inversion LOCAL2. ss. subst.
    exploit Local.read_step_future; try exact LOCAL; try apply WFS1; eauto.
    { destruct thS1, local. ss. }
    s. i. des.
    hexploit lift_write; try exact MEM; eauto; try refl;
      try apply WF0; try apply WF2; try by committac. i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs; eauto.
    + econs 2. econs 4; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 5; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 6; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
Qed.
