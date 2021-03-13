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

Require Import MemoryRel.
Require Import SmallStep.
Require Import Fulfilled.
Require Import Race.
Require Import PIStep.

Require Import FulfillStep.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Definition lift_timemap (l: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec l y then Time.join (tm y) t else tm y.

Definition lift_view (l: Loc.t) (t: Time.t) (rel: View.t) : View.t :=
  match rel with
  | View.mk pln rlx =>
    View.mk pln (lift_timemap l t rlx)
  end.

Definition lift_opt_view (l: Loc.t) (t: Time.t) (rel: option View.t) : option View.t :=
  Some (lift_view l t (View.unwrap rel)).

Lemma lift_timemap_incr l t tm:
  TimeMap.le tm (lift_timemap l t tm).
Proof.
  ii. unfold lift_timemap. condtac; try refl. apply Time.join_l.
Qed.

Lemma lift_timemap_mon l t tm1 tm2
      (LE: TimeMap.le tm1 tm2):
  TimeMap.le (lift_timemap l t tm1) (lift_timemap l t tm2).
Proof.
  ii. unfold lift_timemap. condtac; auto.
  apply Time.join_spec.
  - rewrite <- Time.join_l. auto.
  - apply Time.join_r.
Qed.

Lemma lift_view_wf l t cap
      (WF: View.wf cap):
  View.wf (lift_view l t cap).
Proof.
  unfold lift_view. destruct cap. inv WF. econs; ss.
  - etrans; eauto. apply lift_timemap_incr.
Qed.

Lemma lift_view_incr l t cap:
  View.le cap (lift_view l t cap).
Proof.
  unfold lift_view. destruct cap. econs; try refl.
  - apply lift_timemap_incr.
Qed.

Lemma lift_view_mon l t cap1 cap2
      (LE: View.le cap1 cap2):
  View.le (lift_view l t cap1) (lift_view l t cap2).
Proof.
  inv LE. unfold lift_view. destruct cap1, cap2. econs; ss.
  - apply lift_timemap_mon. auto.
Qed.

Lemma lift_opt_view_wf l t cap
      (WF: View.opt_wf cap):
  View.opt_wf (lift_opt_view l t cap).
Proof.
  econs. apply lift_view_wf. viewtac.
Qed.

Lemma lift_opt_view_incr l t cap:
  View.opt_le cap (lift_opt_view l t cap).
Proof.
  destruct cap; econs. apply lift_view_incr.
Qed.

Lemma lift_opt_view_mon l t cap1 cap2
      (LE: View.opt_le cap1 cap2):
  View.opt_le (lift_opt_view l t cap1) (lift_opt_view l t cap2).
Proof.
  econs. apply lift_view_mon. viewtac.
Qed.

Lemma lift_timemap_closed_timemap
      tm mem l t
      (CLOSED: Memory.closed_timemap tm mem)
      (GET: Memory.get l t mem <> None):
  Memory.closed_timemap (lift_timemap l t tm) mem.
Proof.
  ii. unfold lift_timemap. condtac.
  - subst. destruct (Time.join_cases (tm loc) t); rewrite H.
    + apply CLOSED.
    + destruct (Memory.get loc t mem) as [[? []]|] eqn:X; eauto. congr.
  - apply CLOSED.
Qed.

Lemma lift_view_closed_view
      cap mem l t
      (CLOSED: Memory.closed_view cap mem)
      (GET: Memory.get l t mem <> None):
  Memory.closed_view (lift_view l t cap) mem.
Proof.
  destruct cap. ss. inv CLOSED. econs; ss.
  - apply lift_timemap_closed_timemap; auto.
Qed.

Lemma lift_view_closed_opt_view
      cap mem l t
      (CLOSED: Memory.closed_opt_view cap mem)
      (GET: Memory.get l t mem <> None)
      (INHABITED: Memory.inhabited mem):
  Memory.closed_opt_view (lift_opt_view l t cap) mem.
Proof.
  econs. apply lift_view_closed_view; auto. viewtac.
Qed.

Definition loc_ord_dec (loc:Loc.t) (ord:Ordering.t) (l:Loc.t):
  {l = loc \/ Ordering.le ord Ordering.relaxed} + {~ (l = loc \/ Ordering.le ord Ordering.relaxed)}.
Proof.
  destruct (Loc.eq_dec l loc).
  { left. auto. }
  destruct (Ordering.le ord Ordering.relaxed) eqn:X.
  { left. auto. }
  right. contradict n. des; auto. congr.
Defined.

Definition lift_view_if loc ord l t rel :=
  if loc_ord_dec loc ord l then rel else lift_opt_view l t rel.

Lemma lift_view_if_wf loc ord l t rel
      (WF: View.opt_wf rel):
  View.opt_wf (lift_view_if loc ord l t rel).
Proof.
  unfold lift_view_if. condtac; auto. econs.
  apply lift_view_wf. viewtac.
Qed.

Lemma lift_view_if_incr loc ord l t rel:
  View.opt_le rel (lift_view_if loc ord l t rel).
Proof.
  unfold lift_view_if. condtac; [refl|].
  destruct rel; econs.
  apply lift_view_incr.
Qed.

Lemma lift_view_if_mon loc ord l t rel1 rel2
      (LE: View.opt_le rel1 rel2):
  View.opt_le (lift_view_if loc ord l t rel1) (lift_view_if loc ord l t rel2).
Proof.
  unfold lift_view_if. condtac; auto. econs.
  apply lift_view_mon. viewtac.
Qed.

Definition lift_mem l t p (e:ThreadEvent.t) M1 M2 : Prop :=
  match ThreadEvent.is_writing e with
  | Some (loc,from,to,val,rel,ord) =>
    exists k,
    <<NOPRM: Memory.get loc to p = None>> /\
    <<DISJ: forall t' v' r' (KIND: k = Memory.op_kind_split t' v' r'), Memory.get loc t' p = None>> /\
    <<PMREL: Memory.op M1 loc from to val (lift_view_if loc ord l t rel) M2 k>>
  | None =>
    match e with
    | ThreadEvent.promise loc from to val None (Memory.op_kind_lower released0) =>
      exists released0',
      <<NOPRM: Memory.get loc to p = None>> /\
      <<PMREL: Memory.lower M1 loc from to val released0' None M2>>
    | _ =>
      M1 = M2
    end
  end.

Definition msg_add l e msgs :=
  match ThreadEvent.is_writing e with
  | Some (loc, from, ts, val, rel, ord) =>
    if loc_ord_dec loc ord l then msgs else (loc,ts)::msgs
  | None => msgs
  end.

Lemma remove_lift_mem
      l t prm prm' e
      loc from to val released
      (REMOVE: Memory.remove prm loc from to val released prm'):
  lift_mem l t prm e <2= lift_mem l t prm' e.
Proof.
  unfold lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|]; ss.
  - i. des. esplits; eauto.
    + erewrite Memory.remove_o; eauto. condtac; ss.
    + i. subst. erewrite Memory.remove_o; eauto. condtac; ss.
      eapply DISJ; eauto.
  - destruct e; ss. destruct released0, kind; ss. i. des.
    esplits; eauto. erewrite Memory.remove_o; eauto. condtac; ss.
Qed.

Inductive pi_step_lift_except_aux l t (tid_except:Ident.t) e: (Configuration.t*Configuration.t*Memory.t) -> (Configuration.t*Configuration.t*Memory.t) -> Prop :=
| pi_step_lift_except_intro tid cS1 cS2 cT1 cT2 M1 M2 lst lc
    (PI_STEP: pi_step false tid e (cS1,cT1) (cS2,cT2))
    (FIND: IdentMap.find tid_except (Configuration.threads cT2) = Some (lst,lc))
    (MEM: lift_mem l t (Local.promises lc) e M1 M2)
    (TID: tid <> tid_except):
  pi_step_lift_except_aux l t tid_except e (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift_except_aux.

Definition pi_step_lift_except l t tid_except := union (pi_step_lift_except_aux l t tid_except).
Hint Unfold pi_step_lift_except.

Definition lift_view_le l t (msgs: list (Loc.t*Time.t)) loc ts cap1 cap2 : Prop :=
  cap1 = cap2 \/ (List.In (loc,ts) msgs /\ cap2 = Some (lift_view l t (View.unwrap cap1))).
Hint Unfold lift_view_le.

Global Program Instance lift_view_le_PreOrder l t msgs loc ts : PreOrder (lift_view_le l t msgs loc ts).
Next Obligation.
  ii. unfold lift_view_le in *.
  des; subst; eauto. s.
  right. splits; ss. destruct ((View.unwrap x)). s.
  unfold lift_timemap. f_equal. f_equal.
  - extensionality y. destruct (LocSet.Facts.eq_dec l y); eauto.
    apply TimeFacts.antisym; repeat apply Time.join_spec;
      (try apply Time.join_l);
      (try apply Time.join_r).
    rewrite <- ? Time.join_l. refl.
Qed.

Inductive mem_eqlerel_lift l t p e (m1 m2: Memory.t) : Prop :=
| mem_le_lift_intro m1'
  (MEMEQ: mem_eqlerel m1 m1')
  (MEMWR: lift_mem l t p e m1' m2)
.

Definition conf_update_memory (c: Configuration.t) (m: Memory.t) : Configuration.t :=
 Configuration.mk (Configuration.threads c) (Configuration.sc c) m.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 l t tid
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  rtc (pi_step_except false tid) (fst cSTM1) (fst cSTM2).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. inv USTEP. econs; eauto.
Qed.

Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid l t
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  IdentMap.find tid (fst (fst cSTM1)).(Configuration.threads) = IdentMap.find tid (fst (fst cSTM2)).(Configuration.threads) /\
  IdentMap.find tid (snd (fst cSTM1)).(Configuration.threads) = IdentMap.find tid (snd (fst cSTM2)).(Configuration.threads).
Proof.
  apply pi_steps_lift_except_pi_steps in STEPS.
  apply rtc_pi_step_except_find in STEPS. eauto.
Qed.

Lemma write_step_lift_mem
      lc0 sc0 mem0 mem0'
      lc1 sc1 mem1
      loc from to val releasedm released ord kind
      lco l t
      (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem1 kind)
      (EQLEREL: mem_eqlerel mem0 mem0')
      (RELM_WF: View.opt_wf releasedm)
      (RELM_CLOSED: Memory.closed_opt_view releasedm mem0)
      (LOCAL1: Local.wf lc0 mem0)
      (LOCAL2: Local.wf lco mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (DISJ: Local.disjoint lc0 lco):
  exists mem1',
    <<LIFT: forall e (E: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)),
      lift_mem l t (Local.promises lco) e mem0' mem1'>> /\
    <<EQLEREL: mem_eqlerel mem1 mem1'>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.promise_step_disjoint; eauto. i. des.
  exploit lift_view_if_wf; eauto. i.
  inv STEP1. inv PROMISE.
  - exploit mem_eqlerel_add_forward; eauto.
    { apply lift_view_if_incr. }
    i. des. esplits; eauto. i.
    unfold lift_mem. rewrite E. esplits; cycle 2.
    + econs 1; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.add_o; eauto. condtac; ss. des; congr.
    + congr.
  - exploit mem_eqlerel_split_forward; eauto.
    { apply lift_view_if_incr. }
    i. des. esplits; eauto. i.
    unfold lift_mem. rewrite E. esplits; cycle 2.
    + econs 2; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.split_o; eauto. condtac; ss. des; congr.
    + i. inv KIND. destruct (Memory.get loc t' (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJ; eauto.
      hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
  - exploit mem_eqlerel_lower_forward; eauto. i. des.
    esplits; eauto. i.
    unfold lift_mem. rewrite E. esplits; cycle 2.
    + unfold lift_view_if. condtac; cycle 1.
      { exfalso. apply n. right. clear COND.
        destruct (Ordering.le ord Ordering.relaxed) eqn:Y; ss.
        exploit ORD; eauto.
        { by destruct ord; inv Y. }
        i. des. congr.
      }
      econs 3; eauto.
    + destruct (Memory.get loc to (Local.promises lco)) as [[]|] eqn:X; auto.
      exfalso. eapply Memory.disjoint_get; try apply DISJOINT2; eauto. s.
      erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
    + congr.
Qed.

Lemma pi_step_lifting_aux
      tid cS1 cT1 cS2 cT2 M1 l t
      (PISTEP: pi_step_except false tid (cS1,cT1) (cS2,cT2))
      (FIND: IdentMap.find tid (Configuration.threads cT2) <> None)
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQLEREL: mem_eqlerel (Configuration.memory cT1) M1):
  exists M2,
  pi_step_lift_except l t tid (cS1,cT1,M1) (cS2,cT2,M2) /\
  mem_eqlerel (Configuration.memory cT2) M2.
Proof.
  inv PISTEP. inv PI_STEP. assert (X:= USTEP). inv X.
  destruct (IdentMap.find tid (Configuration.threads cT2)) as [[]|]eqn: EQ; [|by exfalso; eauto].
  inv STEPT.
  inv STEP; [inv STEP0|inv STEP0; inv LOCAL];
    try by esplits; s; eauto; econs; econs; eauto; ss.
  { apply promise_pf_inv in PFREE. des. inversion WF. subst. ss.
    generalize EQ. i. rewrite IdentMap.gso in EQ0; eauto. destruct s.
    exploit Local.promise_step_future; try eapply WFT; eauto. i. des.
    exploit Local.promise_step_disjoint; try exact LOCAL; try eapply WFT; eauto. i. des.
    inv LOCAL. inv PROMISE. exploit Memory.lower_get0; try exact MEM; eauto. i.
    exploit mem_eqlerel_lower_forward; eauto. i. des.
    exists m1'. splits; eauto.
    econs. econs; eauto. red. ss. esplits; eauto.
    destruct (Memory.get loc to (Local.promises t0)) as [[]|] eqn:X; [|done].
    exfalso. eapply Memory.disjoint_get.
    - inv WFT. inv WF1. eapply DISJOINT; eauto.
    - eapply Memory.lower_get0. eauto.
    - eauto.
  }
  { clear PFREE. inversion WF. subst. ss.
    generalize EQ. i. rewrite IdentMap.gso in EQ0; eauto. destruct s.
    exploit write_step_lift_mem; eauto; try apply WFT; try by viewtac.
    { eapply WFT. eauto. }
    { eapply WFT. apply EQ0. }
    { eapply WFT; eauto. }
    i. des. esplits; eauto.
  }
  { clear PFREE. inversion WF. subst. ss.
    generalize EQ. i. rewrite IdentMap.gso in EQ0; eauto. destruct s.
    exploit Local.read_step_future; try eapply WFT; eauto. i. des.
    exploit Local.read_step_disjoint; try exact LOCAL1.
    { eapply WFT. eauto. }
    { eapply WFT; eauto. }
    { eapply WFT. eauto. }
    i. des.
    exploit write_step_lift_mem; try exact x1; eauto; try apply WFT.
    { eapply WFT. eauto. }
    i. des. esplits; eauto.
  }
Qed.

Lemma rtc_pi_step_lifting_aux
      tid cST1 cST2 M1 l t
      (PISTEP: rtc (pi_step_except false tid) cST1 cST2)
      (FIND: IdentMap.find tid (Configuration.threads (snd cST2)) <> None)
      (WF: pi_wf loctmeq cST1)
      (EQLEREL: mem_eqlerel (Configuration.memory (snd cST1)) M1):
  exists M2,
  rtc (pi_step_lift_except l t tid) (cST1,M1) (cST2,M2) /\
  mem_eqlerel (Configuration.memory (snd cST2)) M2.
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
    eapply rtc_implies, PISTEP. i. inv H0. eauto. }
  intro STEP'; des.

  esplits.
  - etrans; [eauto|].
    econs; [|reflexivity]; eauto.
  - eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 l t
      (PI_STEPS: rtc (pi_step_except false tid) cST1 cST2)
      (FIND: IdentMap.find tid (Configuration.threads (snd cST2)) <> None)
      (WF: pi_wf loctmeq cST1):
  exists M2, rtc (pi_step_lift_except l t tid) (cST1,(Configuration.memory (snd cST1))) (cST2,M2).
Proof.
  exploit rtc_pi_step_lifting_aux; eauto; cycle 1.
  - i; des. eauto.
  - rr. split; ii; esplits; eauto; reflexivity.
Qed.

Lemma conf_update_memory_wf
      l t msgs cS1 cT1 M1
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQMEM: mem_eqrel (lift_view_le l t msgs) (Configuration.memory cT1) M1)
      (IN: Memory.get l t (Configuration.memory cT1) <> None)
      (MSGS: forall loc to (IN: List.In (loc, to) msgs),
          (exists from msg, fulfilled cT1 loc from to msg) /\
          loc <> l /\
          to <> Time.bot):
  pi_wf (lift_view_le l t msgs) (cS1,conf_update_memory cT1 M1).
Proof.
  econs; inv WF; try done.
  - inv WFT. econs; s.
    + inv WF. econs; ss. i. exploit THREADS; eauto. i.
      inv x. econs; eauto.
      * eapply mem_eqrel_closed_tview; eauto.
      * ii. destruct msg. exploit PROMISES; eauto. i.
        eapply EQMEM in x. des. rewrite IN0.
        unfold lift_view_le in CMP. des; subst; ss.
        exploit MSGS; eauto. i. des.
        inv x. exfalso. eapply FULFILLED. econs; eauto.
    + eapply mem_eqrel_closed_timemap; eauto.
    + inv MEM. econs.
      * i. inv EQMEM. des. exploit H0; eauto. i. des.
        exploit CLOSED; eauto. i. des. inv CMP.
        { splits; auto. eapply mem_eqrel_closed_opt_view; eauto. }
        { des. subst. splits.
          - apply lift_opt_view_wf. auto.
          - s. unfold lift_view. destruct ((View.unwrap rel2)). ss.
            unfold lift_timemap. condtac; ss. subst.
            exploit MSGS; eauto. i. des. congr.
          - eapply mem_eqrel_closed_opt_view; eauto.
            eapply lift_view_closed_opt_view; eauto.
        }
      * ii. specialize (INHABITED loc). apply EQMEM in INHABITED. des.
        inv CMP; auto. des; subst; ss.
        exfalso. eapply MSGS; eauto.
  - i. exploit LR; eauto. i. des.
    apply EQMEM in IN1. des.
    esplits; eauto. inv CMP. auto.
  - i. apply EQMEM in IN0. des.
    exploit RL; eauto. i. des.
    esplits; eauto. inv CMP0. auto.
Qed.

Lemma small_step_write_closed
      tid c c1 e loc from ts val rel ord withprm
      (WF: Configuration.wf c)
      (STEP: small_step withprm tid e c c1)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)):
  <<CLOSED: Memory.closed_opt_view rel (Configuration.memory c1)>> /\
  <<TS: Time.le ((View.rlx (View.unwrap rel)) loc) ts>>.

Proof.
  inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL]; inv EVENT.
  - clear PFREE. inv WF.
    exploit Local.write_step_future; eauto; try by viewtac.
    { eapply WF0. eauto. }
    i. des. splits; eauto.
  - clear PFREE. inv WF.
    exploit Local.read_step_future; eauto.
    { eapply WF0. eauto. }
    i. des.
    exploit Local.write_step_future; eauto.
    i. des. splits; eauto.
Qed.

Lemma small_step_false_normal
      tid e c1 c2
      (STEP: small_step false tid e c1 c2)
      (NONPROMISING: ThreadEvent.is_promising e = None)
      (NONWRITING: ThreadEvent.is_writing e = None):
  (Configuration.memory c1) = (Configuration.memory c2).
Proof.
  inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL]; inv PFREE; ss.
Qed.

Lemma small_step_false_promising
      tid e c1 c2 loc from to val released kind
      (STEP: small_step false tid e c1 c2)
      (NONWRITING: e = ThreadEvent.promise loc from to val released kind):
  Memory.op (Configuration.memory c1) loc from to val released (Configuration.memory c2) kind.
Proof.
  inv STEP. inv STEP0; inv STEP; inv PFREE; ss.
  apply promise_pf_inv in H0. des. subst. inv LOCAL.
  eapply Memory.promise_op. eauto.
Qed.

Lemma small_step_false_writing
      tid e c1 c2 loc from to val released ord
      (STEP: small_step false tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  exists kind, Memory.op (Configuration.memory c1) loc from to val released (Configuration.memory c2) kind.
Proof.
  inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL]; inv PFREE; ss.
  - inv WRITING. inv LOCAL0. inv WRITE. inv PROMISE.
    + esplits. econs 1; eauto.
    + esplits. econs 2; eauto.
    + esplits. econs 3; eauto.
  - inv WRITING. inv LOCAL1. inv LOCAL2. inv WRITE. inv PROMISE.
    + esplits. econs 1; eauto.
    + esplits. econs 2; eauto.
    + esplits. econs 3; eauto.
Qed.

Lemma lift_view_le_imm
      l t loc to msgs released ord:
  lift_view_le l t
                     (if loc_ord_dec loc ord l then msgs else (loc, to) :: msgs)
                     loc to
                     released
                     (lift_view_if loc ord l t released).
Proof.
  unfold lift_view_if. condtac.
  - left. ss.
  - right. splits; eauto. left. ss.
Qed.

Lemma lift_view_le_incr
      l t msgs loc to rel1 rel2 l' t'
  (LE: lift_view_le l t msgs loc to rel1 rel2):
  lift_view_le l t ((l', t') :: msgs) loc to rel1 rel2.
Proof.
  unfold lift_view_le in *. des; auto.
  right. splits; ss. auto.
Qed.

Lemma lift_view_le_incr'
      l t msgs loc to ord rel1 rel2 l' t'
      (LE: lift_view_le l t msgs l' t' rel1 rel2):
  lift_view_le
    l t
    (if loc_ord_dec loc ord l then msgs else (loc, to) :: msgs)
    l' t' rel1 rel2.
Proof.
  condtac; ss.
  apply lift_view_le_incr. auto.
Qed.

Lemma memory_op_mem_eqrel
      m1 m2 m1' m2' kind1 kind2
      l t msgs
      loc from to val released ord
      (EQMEM: mem_eqrel (lift_view_le l t msgs) m1 m2)
      (OP1: Memory.op m1 loc from to val released m1' kind1)
      (OP2: Memory.op m2 loc from to val (lift_view_if loc ord l t released) m2' kind2)
      (KIND: Memory.op_kind_match kind1 kind2):
  mem_eqrel (lift_view_le
               l t
               (if loc_ord_dec loc ord l then msgs else (loc, to) :: msgs))
            m1' m2'.
Proof.
  inv KIND; inv OP1; inv OP2;
    econs; esplits; ii; revert IN;
      (repeat
         match goal with
         | [X: Memory.add _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.add_o m); [|eexact X]
         | [X: Memory.split _ _ _ _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.split_o m); [|eexact X]
         | [X: Memory.lower _ _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.lower_o m); [|eexact X]
         end);
      repeat
        (match goal with
         | [|- context[if ?c then _ else Memory.get _ _ _]] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [X: _ \/ _ |- _] => guardH X
         end);
      ss; i; des;
        repeat (match goal with
                | [H: Some _ = Some _ |- _] => inv H
                end);
        (try by esplits; eauto; apply lift_view_le_imm).
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
  - subst. exploit Memory.split_get0; try exact SPLIT; eauto. i. des.
    apply EQMEM in GET3. des.
    exploit Memory.split_get0; try exact SPLIT0; eauto. i. des.
    rewrite IN0 in GET3. inv GET3. condtac; ss.
    + des. inv IN. esplits; eauto. apply lift_view_le_imm.
    + guardH o. inv IN. esplits; eauto. apply lift_view_le_incr'; ss.
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
  - subst. exploit Memory.split_get0; try exact SPLIT; eauto. i. des.
    apply EQMEM in GET3. des.
    exploit Memory.split_get0; try exact SPLIT0; eauto. i. des.
    rewrite IN0 in GET3. inv GET3. condtac; ss.
    + des. inv IN. esplits; eauto. apply lift_view_le_imm.
    + guardH o. inv IN. esplits; eauto. apply lift_view_le_incr'; ss.
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
  - apply EQMEM in IN. des. esplits; eauto. apply lift_view_le_incr'; ss.
Qed.

Lemma memory_lower_None_mem_eqrel
      m1 m2 m1' m2' released1 released2
      l t msgs
      loc from to val
      (EQMEM: mem_eqrel (lift_view_le l t msgs) m1 m2)
      (OP1: Memory.lower m1 loc from to val released1 None m1')
      (OP2: Memory.lower m2 loc from to val released2 None m2'):
  mem_eqrel (lift_view_le l t msgs) m1' m2'.
Proof.
  econs; esplits; ii; revert IN;
      (repeat
         match goal with
         | [X: Memory.add _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.add_o m); [|eexact X]
         | [X: Memory.split _ _ _ _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.split_o m); [|eexact X]
         | [X: Memory.lower _ _ _ _ _ _ _ ?m |- context[Memory.get _ _ ?m]] =>
           erewrite (@Memory.lower_o m); [|eexact X]
         end);
      repeat
        (match goal with
         | [|- context[if ?c then _ else Memory.get _ _ _]] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [X: _ \/ _ |- _] => guardH X
         end);
      ss; i; des;
        repeat (match goal with
                | [H: Some _ = Some _ |- _] => inv H
                end);
        (try by esplits; eauto; apply lift_view_le_imm).
  - apply EQMEM in IN. des. esplits; eauto.
  - apply EQMEM in IN. des. esplits; eauto.
Qed.

Lemma msg_add_inv
      loc to l e msgs
      (IN: List.In (loc, to) (msg_add l e msgs)):
  List.In (loc, to) msgs \/
  (match ThreadEvent.is_writing e with
   | Some (loc', _, ts', _, _, ord) =>
     ~ (l = loc) /\
     ~ (Ordering.le ord Ordering.relaxed) /\
     loc = loc' /\ to = ts'
   | None => False
   end).
Proof.
  revert IN. unfold msg_add.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. left. ss. }
  condtac; ss.
  { i. left. ss. }
  i. des.
  - inv IN. right. splits; ss; ii; apply n; auto.
  - left. ss.
Qed.

Lemma writing_small_step_not_bot
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  to <> Time.bot.
Proof.
  inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL]; inv WRITING.
  - inv LOCAL0. eapply MemoryFacts.write_not_bot. eauto.
  - inv LOCAL2. eapply MemoryFacts.write_not_bot. eauto.
Qed.

Lemma pi_step_lift_except_future
      l t msgs tid cS1 cT1 cS2 cT2 M1 M2 e
      (WF: pi_wf loctmeq (cS1,cT1))
      (EQMEM: mem_eqrel (lift_view_le l t msgs) (Configuration.memory cT1) M1)
      (IN: Memory.get l t (Configuration.memory cT1) <> None)
      (PI_STEP: pi_step_lift_except_aux l t tid e (cS1,cT1,M1) (cS2,cT2,M2))
      (MSGS: forall loc to (IN: List.In (loc, to) msgs),
          (exists from msg, fulfilled cT1 loc from to msg) /\
          loc <> l /\
          to <> Time.bot)
:
  <<EQMEM: mem_eqrel (lift_view_le l t (msg_add l e msgs)) (Configuration.memory cT2) M2>> /\
  <<IN: Memory.get l t (Configuration.memory cT2) <> None>> /\
  <<MSGS: forall loc to (IN: List.In (loc, to) (msg_add l e msgs)),
          (exists from msg, fulfilled cT2 loc from to msg) /\
          loc <> l /\
          to <> Time.bot>> /\
  <<MEMFUT: Memory.future M1 M2>> /\
  <<TIMELE: TimeMap.le (Configuration.sc cT1) (Configuration.sc cT2)>>.
Proof.
  assert (EQMEM2: mem_eqrel (lift_view_le l t (msg_add l e msgs)) (Configuration.memory cT2) M2).
  { inv PI_STEP. unfold lift_mem in MEM. unfold msg_add.
    destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
    { destruct (ThreadEvent.is_promising e) as [[]|] eqn:Y; cycle 1.
      - subst. inv PI_STEP0. erewrite <- small_step_false_normal; eauto.
        destruct e; subst; ss.
      - destruct e; inv Y. ss.
        inv PI_STEP0; ss. subst.
        inv STEPT; ss. destruct pf; ss.
        inv STEP. inv STEP0; ss.
        symmetry in PF. apply promise_pf_inv in PF. des. subst. des.
        inv LOCAL. inv PROMISE. ss.
        eapply memory_lower_None_mem_eqrel; eauto.
    }
    des.
    exploit small_step_false_writing;
      (try by inv PI_STEP0; eauto); eauto. i. des.
    exploit mem_eqrel_memory_op; [|exact x0|exact PMREL|..]; eauto. i.
    eapply memory_op_mem_eqrel; eauto.
  }
  assert (IN2: Memory.get l t (Configuration.memory cT2) <> None).
  { destruct (Memory.get l t (Configuration.memory cT1)) as [[? []]|] eqn:X; [|congr].
    inv PI_STEP. inv PI_STEP0. exploit small_step_future; eauto.
    { inv WF. auto. }
    i. des. exploit Memory.future_get1; eauto. i. des.
    rewrite GET. congr.
  }
  inv PI_STEP. splits; auto; cycle 1.
  - revert MEM. unfold lift_mem.
    destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
    { i. destruct e; subst; try refl.
      destruct released; subst; try refl.
      destruct kind; subst; try refl.
      des. econs 2; eauto. econs.
      - econs 3. eauto.
      - econs.
      - apply Time.bot_spec.
    }
    i. des. econs 2; eauto.
    inv PI_STEP0. subst. exploit small_step_write_closed; eauto.
    { inv WF. auto. }
    i. des. econs; eauto.
    + eapply mem_eqrel_closed_opt_view; eauto.
      unfold lift_view_if. condtac; ss.
      eapply lift_view_closed_opt_view; eauto.
      eapply small_step_future; eauto. inv WF. ss.
    + unfold lift_view_if. condtac; ss.
      destruct (View.unwrap o). ss. unfold lift_timemap. condtac; ss.
      exfalso. apply n. auto.
  - inv PI_STEP0.
    eapply small_step_future; eauto.
    inv WF. auto.
  - i. exploit msg_add_inv; eauto. i. des.
    + exploit MSGS; eauto. i. des. esplits; eauto.
      inv WF. inv PI_STEP0.
      destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; ss.
      * eapply writing_small_step_fulfilled_forward; eauto.
      * eapply nonwriting_small_step_fulfilled_forward; eauto.
    + destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; ss.
      des. subst.
      inv WF. inv PI_STEP0. exploit writing_small_step_fulfilled_new; eauto. i.
      esplits; eauto. eapply writing_small_step_not_bot; eauto.
Qed.

Lemma rtc_pi_step_lift_except_future
      l t tid cS1 cT1 cSTM2 lst1 lc1
      (WF: pi_wf loctmeq (cS1,cT1))
      (IN: Memory.get l t (Configuration.memory cT1) <> None)
      (PI_STEPS: rtc (pi_step_lift_except l t tid) (cS1,cT1,(Configuration.memory cT1)) cSTM2)
      (FIND: IdentMap.find tid (Configuration.threads cT1) = Some (lst1,lc1)):
  <<WF: exists msgs, pi_wf (lift_view_le l t msgs) ((fst (fst cSTM2)),(conf_update_memory (snd (fst cSTM2)) (snd cSTM2)))>> /\
  <<MEMFUT: Memory.future (Configuration.memory cT1) (snd cSTM2)>> /\
  <<TIMELE: TimeMap.le (Configuration.sc cT1) (snd (fst cSTM2)).(Configuration.sc)>> /\
  <<LOCWF: Local.wf lc1 (snd cSTM2)>> /\
  <<MEMCLOTM: Memory.closed_timemap ((snd (fst cSTM2)).(Configuration.sc)) (snd cSTM2)>> /\
  <<MEMCLO: Memory.closed (snd cSTM2)>>.
Proof.
  apply (@proj2 (<<EQMEM: exists msgs, mem_eqrel (lift_view_le l t msgs) (snd (fst cSTM2)).(Configuration.memory) (snd cSTM2) /\
                 <<MSGS: forall loc to (IN: List.In (loc, to) msgs),
                         (exists from msg, fulfilled (snd (fst cSTM2)) loc from to msg) /\
                         loc <> l /\
                         to <> Time.bot>> >> /\
                 <<IN: Memory.get l t (snd (fst cSTM2)).(Configuration.memory) <> None>>)).
  revert FIND.
  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in PI_STEPS.
  induction PI_STEPS.
  { set (X:=WF). inv X. inv WFT. inv WF0. destruct lst1.
    i; esplits; s; eauto; try reflexivity.
    - split; ii; esplits; eauto.
    - instantiate (1:=[]). done.
    - eapply conf_update_memory_wf; eauto.
      + split; ii; esplits; eauto.
      + instantiate (1:=[]). done.
  }
  apply Operators_Properties.clos_rt_rtn1_iff,
        Operators_Properties.clos_rt_rt1n_iff in PI_STEPS.

  i. exploit IHPI_STEPS; eauto. i; des. clear IHPI_STEPS.
  inv H. destruct y as [[]], z as [[]].
  exploit pi_step_lift_except_future; try apply USTEP; eauto.
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
    i. inv H. eauto. }
  i; des. destruct lst1.

  exploit conf_update_memory_wf; [|eauto|eauto| |].
  { eapply rtc_pi_step_future; eauto.
    etrans.
    - eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
      i. inv H. eauto.
    - s. econs 2; [|reflexivity]. inv USTEP. eauto. }
  { eauto. }
  intro X. inv X. inv WFT. inv WF1.
  s. esplits; eauto; try etrans; eauto.
  { eapply conf_update_memory_wf; eauto.
    eapply rtc_pi_step_future; eauto.
    etrans.
    { eapply rtc_implies, (@pi_steps_lift_except_pi_steps (_,_) (_,_)), PI_STEPS.
      i; inv H; eauto. }
    ss. inv USTEP.
    econs 2; [|reflexivity]. eauto.
  }

  eapply THREADS. s.

  hexploit rtc_pi_step_lift_except_find.
  { etrans; [eauto|].
    econs 2; [|reflexivity]. eauto. }
  s. intro EQ. des. rewrite <-EQ0.
  eauto.
Qed.

Lemma mem_eqlerel_lift_get
      loc ts prm e m1 m2 l f t v r2
      (LIFT: mem_eqlerel_lift loc ts prm e m1 m2)
      (GET: Memory.get l t m2 = Some (f, Message.mk v r2)):
  (exists r o, ThreadEvent.is_writing e = Some (l, f, t, v, r, o)) \/
  (ThreadEvent.is_promising e = Some (l, t) /\
   ThreadEvent.is_lower_none e) \/
  (exists f' r1,
      <<EVT: forall o, ThreadEvent.is_writing e <> Some (l, f, t, v, r1, o)>> /\
      <<GET: Memory.get l t m1 = Some (f', Message.mk v r1)>> /\
      <<REL: View.opt_le r1 r2>> /\
      <<FROM: Time.le f' f>>).
Proof.
  inv LIFT. revert MEMWR. unfold lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[] ?] ?] ?] ?]|] eqn:E; ss.
  - i. des. exploit Memory.op_get_inv; eauto. i. des.
    + subst. eauto.
    + exploit mem_eqlerel_get; eauto. i. des.
      right. right. esplits; eauto. ii. inv H. unguardH x0. des; congr.
  - i. destruct (classic (m1' = m2)).
    { subst. exploit mem_eqlerel_get; eauto. i. des.
      right. right. esplits; eauto; ss. refl.
    }
    destruct e; try congr. destruct released; try congr. destruct kind; try congr.
    des. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + i. des. inv GET.
      exploit Memory.lower_get0; eauto.
    + guardH o. right. right. apply MEMEQ in GET. des.
      esplits; eauto; ss. refl.
Qed.

Lemma lift_read
      com1 com2 com2' m1 m2 prm l t e loc to val rel2 ordr
      (LOCAL: Local.read_step (Local.mk com2 prm) m2 loc to val rel2 ordr (Local.mk com2' prm))
      (COM2: TView.wf com2)
      (REL2: View.opt_wf rel2)
      (CoMLE: TView.le com1 com2)
      (MEMLE: mem_eqlerel_lift l t prm e m1 m2):
  (exists from relw ordw,
   <<EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, relw, ordw)>>)
  \/
  (<<EVTP: ThreadEvent.is_promising e = Some (loc, to)>> /\
   <<EVTL: ThreadEvent.is_lower_none e>>)
  \/
  (exists com1' rel1,
   <<LOCAL: Local.read_step (Local.mk com1 prm) m1 loc to val rel1 ordr (Local.mk com1' prm)>> /\
   <<CoMLE: TView.le com1' com2'>> /\
   <<RELLE: View.opt_le rel1 rel2>>).
Proof.
  inversion LOCAL. ss. subst.
  exploit mem_eqlerel_lift_get; eauto. i. des; eauto.
  right. right. esplits; ss.
  - econs; eauto. ss. eapply TViewFacts.readable_mon; eauto.
    + apply CoMLE.
    + refl.
  - apply TViewFacts.read_tview_mon; eauto; try refl.
  - auto.
Qed.

Lemma lift_mem_add
      loc from to val released
      m1 m2 m2' prm'
      l t prm e
      (MEMLE: lift_mem l t prm e m1 m2)
      (ADD2: Memory.add m2 loc from to val released m2')
      (ADDP2: Memory.add prm loc from to val released prm'):
  exists m1',
    <<ADD1: Memory.add m1 loc from to val released m1'>> /\
    <<MEMLE': lift_mem l t prm' e m1' m2'>>.
Proof.
  revert MEMLE. unfold lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. destruct e; try by subst; esplits; eauto.
    destruct released0; try by subst; esplits; eauto.
    destruct kind; try by subst; esplits; eauto. des. ss.
    exploit MemoryReorder.lower_add; eauto. i. des.
    esplits; eauto.
    erewrite Memory.add_o; eauto. condtac; ss. des. subst. ss.
  }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_add; try exact MEM; eauto. i. des.
    esplits; eauto; cycle 2.
    + econs 1; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + congr.
  - exploit MemoryReorder.split_add; try exact MEM; eauto. i. des.
    esplits; eauto; cycle 2.
    + econs 2; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + i. inv KIND.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. congr.
  - exploit MemoryReorder.lower_add; try exact MEM; eauto. i. des.
    esplits; eauto; cycle 2.
    + econs 3; eauto.
    + erewrite Memory.add_o; eauto. condtac; ss. des. subst. congr.
    + congr.
Qed.

Lemma lift_mem_split
      loc ts1 ts2 ts3 val2 val3 released2 released3
      m1 m2 m2' prm'
      l t prm e
      (MEMLE: lift_mem l t prm e m1 m2)
      (SPLIT2: Memory.split m2 loc ts1 ts2 ts3 val2 val3 released2 released3 m2')
      (SPLITP2: Memory.split prm loc ts1 ts2 ts3 val2 val3 released2 released3 prm'):
  exists m1',
    <<SPLIT2: Memory.split m1 loc ts1 ts2 ts3 val2 val3 released2 released3 m1'>> /\
    <<MEMLE': lift_mem l t prm' e m1' m2'>>.
Proof.
  revert MEMLE. unfold lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. destruct e; try by subst; esplits; eauto.
    destruct released; try by subst; esplits; eauto.
    destruct kind; try by subst; esplits; eauto. des. ss.
    exploit MemoryReorder.lower_split; eauto. i. des.
    unguardH FROM1. des.
    - inv FROM1. exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr.
    - inv FROM0. esplits; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
      + des. subst. exploit Memory.lower_get0; try exact PMREL; eauto.
        exploit Memory.split_get0; try exact PMREL; eauto. i. des. congr.
      + guardH o. des. subst. congr.
  }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_split; try exact MEM; eauto. i. des.
    { subst. exploit Memory.split_get0; try exact SPLITP2; eauto.
      i. des. congr.
    }
    esplits; eauto; cycle 2.
    + econs 1; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      { des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      }
      { guardH o0. des. subst. congr. }
    + congr.
  - exploit MemoryReorder.split_split; try exact MEM; eauto.
    { ii. inv H. exploit DISJ; eauto. i.
      exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr.
    }
    i. des.
    { subst. exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr. }
    esplits; eauto; cycle 2.
    + econs 2; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.split_o; eauto. condtac; ss.
      * guardH o0. des. subst. exploit Memory.split_get0; try exact SPLITP2; eauto.
        i. des. congr.
    + i. inv KIND. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.split_o; eauto. repeat condtac; ss.
      * guardH o0. des. subst. exploit DISJ; eauto.
        exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr.
  - exploit MemoryReorder.lower_split; try exact MEM; eauto. i. des.
    unguardH FROM1. des.
    { inv FROM1. subst. exploit Memory.split_get0; try exact SPLITP2; eauto. i. des. congr. }
    inv FROM0. esplits; eauto; cycle 2.
    + econs 3; eauto.
    + erewrite Memory.split_o; eauto. repeat condtac; ss.
      * des. subst. exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
      * guardH o0. des. subst. congr.
    + congr.
Qed.

Lemma lift_mem_lower
      loc from to val released released'
      m1 m2 m2' prm'
      l t prm e
      (MEMLE: lift_mem l t prm e m1 m2)
      (LOWER2: Memory.lower m2 loc from to val released released' m2')
      (LOWERP2: Memory.lower prm loc from to val released released' prm'):
  exists m1',
    <<LOWER1: Memory.lower m1 loc from to val released released' m1'>> /\
    <<MEMLE': lift_mem l t prm' e m1' m2'>>.
Proof.
  revert MEMLE. unfold lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn:X; cycle 1.
  { i. destruct e; try by subst; esplits; eauto.
    destruct released0; try by subst; esplits; eauto.
    destruct kind; try by subst; esplits; eauto. des. ss.
    exploit MemoryReorder.lower_lower; eauto. i. des.
    - subst. exploit Memory.lower_get0; try exact LOWERP2; eauto. congr.
    - esplits; eauto.
      erewrite Memory.lower_o; eauto. condtac; ss. des. subst. ss.
  }
  i. des. inv PMREL.
  - exploit MemoryReorder.add_lower; try exact MEM; eauto. i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto; cycle 2.
    + econs 1; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + congr.
  - exploit MemoryReorder.split_lower_diff; try exact MEM; eauto.
    { ii. inv H. exploit DISJ; eauto. i.
      exploit Memory.lower_get0; try exact LOWERP2; eauto. i. congr.
    }
    i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto; cycle 2.
    + econs 2; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + i. inv KIND. erewrite Memory.lower_o; eauto. condtac; ss.
      * des. subst. exploit DISJ; eauto.
        erewrite Memory.lower_get0; [|eauto]. congr.
      * eapply DISJ. eauto.
  - exploit MemoryReorder.lower_lower; try exact MEM; eauto. i. des.
    { subst. erewrite Memory.lower_get0 in NOPRM; eauto. congr. }
    esplits; eauto; cycle 2.
    + econs 3; eauto.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst. congr.
    + congr.
Qed.

Lemma lift_mem_promise
      loc from to val released kind
      m1 m2 m2' prm'
      l t prm e
      (MEMLE: lift_mem l t prm e m1 m2)
      (PROMISE2: Memory.promise prm m2 loc from to val released prm' m2' kind):
  exists m1',
    <<PROMISE1: Memory.promise prm m1 loc from to val released prm' m1' kind>> /\
    <<MEMLE': lift_mem l t prm' e m1' m2'>>.
Proof.
  inv PROMISE2.
  - exploit lift_mem_add; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit lift_mem_split; eauto. i. des.
    esplits; eauto. econs; eauto.
  - exploit lift_mem_lower; eauto. i. des.
    esplits; eauto. econs; eauto.
Qed.

Lemma mem_eqlerel_lift_promise
      loc from to val released kind
      m1 m2 m2' prm'
      l t prm e
      (MEMLE: mem_eqlerel_lift l t prm e m1 m2)
      (PRM1: Memory.le prm m1)
      (PROMISE2: Memory.promise prm m2 loc from to val released prm' m2' kind):
  exists m1',
    <<PROMISE1: Memory.promise prm m1 loc from to val released prm' m1' kind>> /\
    <<MEMLE': mem_eqlerel_lift l t prm' e m1' m2'>>.
Proof.
  inv MEMLE.
  exploit lift_mem_promise; eauto. i. des.
  exploit mem_eqlerel_promise; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma lift_write
      com1 com2 com2' sc1 sc2 sc2' m1 m2 m2' prm prm' l t e loc from to val relr1 relr2 relw2 ord kind
      (LOCAL: Local.write_step (Local.mk com2 prm) sc2 m2 loc from to val relr2 relw2 ord (Local.mk com2' prm') sc2' m2' kind)
      (PRM1: Memory.le prm m1)
      (FINITE1: Memory.finite prm)
      (M1: Memory.closed m1)
      (RELR1: View.opt_wf relr1)
      (RELR2: View.opt_wf relr2)
      (COM1: TView.wf com1)
      (COM2: TView.wf com2)
      (CoMLE: TView.le com1 com2)
      (SC: TimeMap.le sc1 sc2)
      (REL: View.opt_le relr1 relr2)
      (MEMLE: mem_eqlerel_lift l t prm e m1 m2):
  exists com1' sc1' m1' kind' relw1,
  <<LOCAL: Local.write_step (Local.mk com1 prm) sc1 m1 loc from to val relr1 relw1 ord (Local.mk com1' prm') sc1' m1' kind'>> /\
  <<CoMLE: TView.le com1' com2'>> /\
  <<RELLE: View.opt_le relw1 relw2>> /\
  <<SC: TimeMap.le sc1' sc2'>> /\
  <<MEMLE: mem_eqlerel_lift l t prm' e m1' m2'>>.
Proof.
  set (relw1 := TView.write_released com1 sc1 loc to relr1 ord).
  assert (RELWWF: View.opt_wf relw1).
  { unfold relw1, TView.write_released. condtac; econs. repeat (try condtac; aggrtac).
    - apply COM1.
    - apply COM1.
  }
  assert (RELWLE: View.opt_le relw1 relw2).
  { unfold relw1. inv LOCAL. s. eapply TViewFacts.write_released_mon; eauto. refl. }
  inv LOCAL. inv WRITE.
  exploit mem_eqlerel_lift_promise; eauto. i. des.
  hexploit Memory.promise_future0; eauto; try by viewtac. i. des.
  hexploit MemorySplit.remove_promise_remove; try exact REMOVE; eauto.
  { inv PROMISE; inv MEM. by inv ADD. by inv SPLIT. by inv LOWER. }
  { by inv PROMISE. }
  { inv PROMISE; inv MEM. by inv ADD. by inv SPLIT. by inv LOWER. }
  i. des.
  hexploit MemoryMerge.promise_promise_promise; try exact PROMISE1; eauto. i.
  esplits; eauto.
  - econs; eauto.
    + eapply TViewFacts.writable_mon; eauto.
      * apply CoMLE.
      * refl.
    + econs; eauto.
  - apply TViewFacts.write_tview_mon; auto. refl.
  - inv MEMLE'. econs; eauto.
    + etrans; eauto.
      eapply lower_mem_eqlerel. inv PROMISE0. eauto.
    + eapply remove_lift_mem; [|eauto]. eauto.
Qed.

Lemma lift_fence
      sc1 sc2 sc2' com1 com2 com2' prm prm' ordr ordw
      (LOCAL: Local.fence_step (Local.mk com2 prm) sc2 ordr ordw (Local.mk com2' prm') sc2')
      (COM1: TView.wf com1)
      (COM2: TView.wf com2)
      (CoMLE: TView.le com1 com2)
      (SC: TimeMap.le sc1 sc2):
  exists com1' sc1',
  <<LOCAL: Local.fence_step (Local.mk com1 prm) sc1 ordr ordw (Local.mk com1' prm') sc1'>> /\
  <<CoMLE: TView.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>>.
Proof.
  inversion LOCAL. ss. subst.
  esplits; eauto.
  - econs; eauto.
  - apply TViewFacts.write_fence_tview_mon; eauto; try refl.
    + apply TViewFacts.read_fence_tview_mon; eauto; try refl.
    + unfold TView.read_fence_tview. ss.
      econs; repeat (try condtac; aggrtac; try apply COM1).
  - apply TViewFacts.write_fence_sc_mon; eauto; try refl.
    apply TViewFacts.read_fence_tview_mon; eauto; try refl.
Qed.

Lemma lift_step
      lang (thS1 thT1 thT2: @Thread.t lang) eT l t e
      (STEP: Thread.step true eT thT1 thT2)
      (ST: (Thread.state thS1) = (Thread.state thT1))
      (WFS1: Local.wf (Thread.local thS1) (Thread.memory thS1))
      (WFT1: Local.wf (Thread.local thT1) (Thread.memory thT1))
      (SCS1: Memory.closed_timemap (Thread.sc thS1) (Thread.memory thS1))
      (SCT1: Memory.closed_timemap (Thread.sc thT1) (Thread.memory thT1))
      (MEMS1: Memory.closed (Thread.memory thS1))
      (MEMT1: Memory.closed (Thread.memory thT1))
      (COM: TView.le (Local.tview (Thread.local thS1)) (Local.tview (Thread.local thT1)))
      (PRM: (Local.promises (Thread.local thS1)) = (Local.promises (Thread.local thT1)))
      (SC: TimeMap.le (Thread.sc thS1) (Thread.sc thT1))
      (MEM: mem_eqlerel_lift l t (Local.promises (Thread.local thT1)) e (Thread.memory thS1) (Thread.memory thT1))
:
  (exists loc ts from val relr relw ordr ordw,
   <<EVTR: ThreadEvent.is_reading eT = Some (loc, ts, val, relr, ordr)>> /\
   <<EVTW: ThreadEvent.is_writing e = Some (loc, from, ts, val, relw, ordw)>>)
  \/
  (exists loc ts val relr ordr,
   <<EVTR: ThreadEvent.is_reading eT = Some (loc, ts, val, relr, ordr)>> /\
   <<EVTP: ThreadEvent.is_promising e = Some (loc, ts)>> /\
   <<EVTL: ThreadEvent.is_lower_none e>>)
  \/
  (exists eS thS2,
   <<STEP: Thread.step true eS thS1 thS2>> /\
   <<ST: (Thread.state thS2) = (Thread.state thT2)>> /\
   <<PRM: (Local.promises (Thread.local thS2)) = (Local.promises (Thread.local thT2))>> /\
   <<EVT: ThreadEvent.le eS eT>> /\
   <<COM: TView.le (Local.tview (Thread.local thS2)) (Local.tview (Thread.local thT2))>> /\
   <<SC: TimeMap.le (Thread.sc thS2) (Thread.sc thT2)>> /\
   <<MEM: mem_eqlerel_lift l t (Local.promises (Thread.local thT2)) e (Thread.memory thS2) (Thread.memory thT2)>>).
Proof.
  inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
  - symmetry in PF. apply promise_pf_inv in PF. des. subst.
    inv LOCAL. exploit mem_eqlerel_lift_promise; eauto.
    { rewrite <- PRM. apply WFS1. }
    s. i. des. destruct thS1. ss.
    right. right. esplits.
    + econs 1. econs. econs.
      * rewrite PRM. eauto.
      * econs.
      * ss.
    + ss.
    + ss.
    + econs. econs.
    + ss.
    + ss.
    + ss.
  - subst. destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 1]; eauto.
    + ss.
    + ss.
    + econs.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL0. subst. ss.
    exploit lift_read; eauto.
    { apply WFT1. }
    { eapply MEMT1. eauto. }
    i. des.
    { left. esplits; eauto. }
    { right. left. esplits; eauto. }
    destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 2]; eauto.
    + ss.
    + ss.
    + econs. eauto.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL0. ss. subst.
    hexploit lift_write; try exact MEM; eauto; try refl;
      try apply WFS1; try apply WFT1; try by viewtac. i. des.
    destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 3]; eauto.
    + ss.
    + ss.
    + econs. eauto.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL1. subst. ss.
    exploit Local.read_step_future; eauto. s. i. des.
    exploit lift_read; eauto.
    { apply WFT1. }
    i. des.
    { left. esplits; eauto. }
    { right. left. esplits; eauto. }
    inversion LOCAL2. ss. subst.
    exploit Local.read_step_future; try exact LOCAL; try apply WFS1; eauto.
    { destruct thS1, local. ss. }
    s. i. des.
    hexploit lift_write; try exact MEM; eauto; try refl;
      try apply WF0; try apply WF2; try by viewtac. i. des.
    destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 4]; eauto.
    + ss.
    + ss.
    + econs; eauto.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL0. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 5]; eauto.
    + ss.
    + ss.
    + econs.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL0. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. right. esplits.
    + econs 2. econs; [|econs 6]; eauto.
    + ss.
    + ss.
    + econs.
    + ss.
    + ss.
    + ss.
Qed.
