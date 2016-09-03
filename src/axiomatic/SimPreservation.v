(******************************************************************************)
(** * Simulation between axiomatic and operational machines *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.
Require Import Time.
Require Import Configuration.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Thread.
Require Import TView.

Require Import Gevents.
Require Import model.
Require Import Gstep GstepRead GstepWrite GstepFence GstepOther.
Require Import Machine.
Require Import SimRel.

Set Implicit Arguments.
Remove Hints plus_n_O.

Require Import Setoid Permutation.

Hint Resolve gstep_wf gstep_inc coh_wf.

Lemma sim_tview_other_threads_silent acts sb rmw rf mo sc
  (COH: Coherent acts sb rmw rf mo sc) f f' i tview
  (LOCAL: sim_tview f acts sb rmw rf sc tview i)
  (F: forall a, (In a acts) -> f' a = f a) :
    sim_tview f' acts sb rmw rf sc tview i.
Proof.
unfold sim_tview, sim_cur, sim_acq, sim_rel in *; desf; splits; ins.
all: eapply max_value_new_f; eauto.
all: ins; apply F; eauto with acts.
Qed.

Lemma sim_tview_other_threads acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f f' i (NEQ: i <> thread a) tview 
  (LOCAL: sim_tview f acts sb rmw rf sc tview i)
  (F: forall a, (In a acts) -> f' a = f a) :
    sim_tview f' acts' sb' rmw' rf' sc' tview i.
Proof.
unfold sim_tview, sim_cur, sim_acq, sim_rel in *; desf; splits; ins.
all: eapply max_value_same_set.
all: try match goal with
       | [|- max_value _ _ _] => eapply max_value_new_f with (f:=f); eauto with acts
     end.
all: ins; try eapply gstep_t_cur_other;  
     try eapply gstep_t_acq_other;  
     try eapply gstep_t_rel_other;  
     eauto 2 using gstep_urr_a, gstep_rwr_a, gstep_scr_a, urr_mon, rwr_mon, scr_mon.
Qed.

(******************************************************************************)
(** * Lemmas for the read step   *)
(******************************************************************************)

Lemma tview_step_read acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a l v o (LABa : lab a = Aload l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  b o_b (INb : In b acts) (RFb : rf0 b a) (LABb : lab b = Astore l v o_b)
  rel (SIM_MSG: sim_msg f acts sb rmw rf sc b rel.(View.unwrap))
  tview (TVIEW: sim_tview f acts sb rmw rf sc tview (thread a)):
  sim_tview f acts0 sb0 rmw0 rf0 sc0 (TView.read_tview tview l (f b) rel o) (thread a).
Proof.
assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.
assert (LOC_B: Gevents.loc b = Some l). 
  unfold Gevents.loc; destruct (lab b); ins; desf.

assert (RLXa: is_rlx_rw a <-> Ordering.le Ordering.relaxed o).
  by destruct a; ins; desf.
assert (ACQa: is_acq a <-> Ordering.le Ordering.acqrel o).
  by destruct a; ins; desf.
assert (SCa: is_sc a <-> Ordering.le Ordering.seqcst o).
  by destruct a; ins; desf.

assert (~ is_fence a /\ ~ is_write a /\ is_read a).
  by destruct a; ins; desf.

destruct tview; simpl.
red in TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
red in SIM_MSG; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

all: try rewrite LocFun.add_spec; desf.
all: ins.
all: try rewrite !tm_join_bot.
all: try rewrite !tm_find_join.
all: try rewrite !tm_find_singleton; desf.
all: try rewrite !time_join_bot.
all: do 2 (try match goal with
| [|- max_value _ _ (Time.join _ _)] => eapply max_value_join  end).
all: try match goal with
       | [|- max_value _ _ (LocFun.find _ _)] => eapply max_value_same_set; eauto with acts
       | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto end.
all: simpl.
all: try by intro x; split; [intro K; pattern x; exact K|].
all: intro x.

all: try (rewrite (gstep_t_cur_urr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_cur_rwr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_cur_scr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_acq_urr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_acq_rwr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_acq_scr_read COH GSTEP b RFb); split; ins; desf; try by eauto; try by (exfalso; eauto)).


rewrite (gstep_t_rel_other GSTEP _ _ (gstep_urr_a COH GSTEP (l:=_)) 
                           (urr_mon GSTEP (l:=_))); auto.
rewrite (gstep_t_rel_other GSTEP _ _ (gstep_rwr_a COH GSTEP (l:=_)) 
                           (rwr_mon GSTEP (l:=_))); auto.
rewrite (gstep_t_rel_other GSTEP _ _ (gstep_scr_a COH GSTEP (l:=_)) 
                           (scr_mon GSTEP (l:=_))); auto.
Qed.

Lemma memory_step_nonwrite acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  (COH0: Coherent acts0 sb0 rmw0 rf0 mo0 sc0) 
  ffrom fto (MONOTONE : monotone mo fto)
  prev a (NW: ~ is_write a) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem (SIM_MEM : sim_mem ffrom fto acts sb rmw rf sc mem):
  sim_mem ffrom fto acts0 sb0 rmw0 rf0 sc0 mem.
Proof.
red; ins.
specialize (SIM_MEM l); desc. 
splits.
- intro b. specialize (DOM b); desf.
  red in GSTEP; desc.
  rewrite ACT_STEP.
  ins; desf; subst.
  by apply DOM; eauto.
- ins.
  specialize (SIMCELL to from v rel CELL); desc.
  exists b.
  unfold sim_mem_helper in *; desc; splits; eauto.
  by red in GSTEP; desc; rewrite ACT_STEP; right.
  unfold sim_msg in *; desc; splits; eauto.
  all: ins.
  all: eapply max_value_same_set; try edone.
  all: simpl; eauto using gstep_msg_rel_urr_nonwrite, gstep_msg_rel_rwr_nonwrite, 
  gstep_msg_rel_scr_nonwrite.
- ins; apply UPDATES; try done.
  eapply gstep_rf_rmw_nonwrite with (rf:=rf) in RF_RMW; eauto.
Qed.

(******************************************************************************)
(** * Lemmas for the write step   *)
(******************************************************************************)

Lemma tview_step_write acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  prev a l v o (LABa : lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  tview (TVIEW: sim_tview f acts sb rmw rf sc tview (thread a))
  f' (F : forall b, In b acts -> f' b = f b)
  (MON : monotone mo0 f'):
  sim_tview f' acts0 sb0 rmw0 rf0 sc0 (TView.write_tview tview sc_map l (f' a) o) (thread a).
Proof.

assert (WRITE: is_write a).
  eauto with acts.
assert (NR: ~ is_read a).
  eauto with acts.

assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
assert (SCa': Ordering.le Ordering.seqcst o <-> is_sc_wf a).
  by rewrite SCa; eauto 7 with acts.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.

assert (LOC_A: Gevents.loc a = Some l). 
  by unfold Gevents.loc; destruct (lab a); ins; desf.

destruct tview; simpl.
red in TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

all: try rewrite LocFun.add_spec; desf.
all: ins.
all: try rewrite !tm_join_bot.
all: try rewrite !tm_find_join.
all: try rewrite !tm_find_singleton; desf.
all: try rewrite !time_join_bot.
all: do 2 (try match goal with
| [|- max_value _ _ (Time.join _ _)] => eapply max_value_join  end).
all: try match goal with
         | [|- max_value _ _ (LocFun.find _ _)] => eapply max_value_same_set;
           try eapply max_value_new_f with (f':=f'); eauto with acts
         | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto
       end.
all: simpl.
all: try by intro x; split; [intro K; pattern x; exact K|].
all: intro x.

all: clear 
  CUR_UR CUR_RW CUR_SC
  ACQ_UR ACQ_RW ACQ_SC
  REL_UR REL_UR0 REL_UR1.

  all: try rewrite (gstep_t_acq_urr_nonread COH GSTEP NR).  
  all: try rewrite (gstep_t_acq_rwr_nonread COH GSTEP NR).  
  all: try rewrite (gstep_t_acq_scr_nonread COH GSTEP NR).  
  all: try rewrite (gstep_t_cur_urr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_cur_rwr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_cur_scr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_rel_urr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_rel_rwr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_rel_scr_write COH GSTEP WRITE).
  all: split; ins; desf; eauto 3 with acts.
  all: try by exfalso; eauto with acts.
  all: eauto 10 with rel.
  all: eauto using inclusion_refl2 with rel_mon.
Qed.

Lemma sc_map_step_write acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  prev a l v o (LABa : lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  f' (F : forall b, In b acts -> f' b = f b)
  (MON : monotone mo0 f'):
  forall l0, max_value f' (S_tm acts0 sb0 rmw0 rf0 l0)
     (LocFun.find l0 (TView.write_sc sc_map l (f' a) o)).
Proof.
assert (WRITE: is_write a).
  eauto with acts.
assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
    ins.
    unfold TView.write_sc; desf; ins.
    all: try rewrite !tm_find_join.
    all: try rewrite !tm_find_singleton; desf; ins.
    all: try rewrite time_join_bot.
    all: try eapply max_value_join.
    all: try match goal with
             | [|- max_value _ _ (LocFun.find _ _)] => eapply max_value_same_set;
               try eapply max_value_new_f with (f':=f'); eauto with acts
             | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto
           end.
    all: ins.
    all: rewrite gstep_S_tm_write; eauto.
    all: split; ins; desf; eauto.
    all: try by (exfalso; eauto).
    right; splits; eauto.
    by destruct x; ins; desf.
    by destruct a; ins; desf; exfalso; unfold loc in *; ins; desf; auto.
Qed.


Lemma memory_add_bot l from to val released (LT : Time.lt from to) 
      (WF : View.opt_wf released) :
  Memory.add Memory.bot l from to val released 
    (Memory.singleton l val released LT). 
Proof.
  econs; econs; eauto.
  red; ins; unfold DenseOrder.DOMap.find in *; ins.
  rewrite DenseOrder.DOMap.Raw.gempty in *; ins.
Qed.

Lemma memory_exists 
  mem (CLOSED: Memory.closed mem)
  from to (FROM: Time.lt from to)
  tview (CWF: TView.wf tview)
  released (RWF: View.opt_wf released)
  l (LE: Time.le (released.(View.unwrap).(View.rlx) l) to) 
  (DISJ: forall (to2 from2 : Time.t) (msg2 : Message.t),
           Memory.get l to2 mem = Some (from2, msg2) ->
           Interval.disjoint (from, to) (from2, to2)) v :
  exists mem', 
    Memory.write Memory.bot mem l from to v 
                 released Memory.bot mem' Memory.op_kind_add .
Proof.
  exploit (@Memory.add_exists mem l from to v); try edone.
  intro M; desc; exists mem2.
  econs; eauto using Memory.remove_singleton.
  econs; try apply (memory_add_bot _ _ FROM); eauto.
Qed.

Lemma memory_exists_write 
  mem (CLOSED: Memory.closed mem)
  from to (FROM: Time.lt from to)
  tview (CWF: TView.wf tview)
  l (CUR_LE: Time.le (View.rlx (TView.cur tview) l) to)
  (DISJ: forall (to2 from2 : Time.t) (msg2 : Message.t),
           Memory.get l to2 mem = Some (from2, msg2) ->
           Interval.disjoint (from, to) (from2, to2)) 
  v o sc_map :
  exists mem', 
    Memory.write Memory.bot mem l from to v 
                 (TView.write_released tview sc_map l to None o)
                 Memory.bot mem' Memory.op_kind_add .
Proof.
  eapply memory_exists; eauto.
  { apply TViewFacts.write_future0; ss. econs. }
  assert (YY: Time.le (View.rlx (TView.rel tview l) l) to).
    by etransitivity; [|exact CUR_LE]; apply CWF.
  unfold TView.write_released.
  ins; desf; ins; unfold TimeMap.join, TimeMap.bot; ins; desf;
  unfold LocFun.add; desf; try congruence; ins;
  repeat apply Time.join_spec; eauto using Time.bot_spec;
  try rewrite tm_singleton; try reflexivity.
Qed.


Lemma memory_write0 mem mem' l from t v rel l0 t0
  (ADD: Memory.write Memory.bot mem l from t v rel Memory.bot mem' Memory.op_kind_add)
  from0 m (NEW: Memory.get l0 t0 mem = Some (from0, m)):
  Memory.get l0 t0 mem' = Some (from0, m).
Proof.
  destruct ADD; inv PROMISE. 
  rewrite (Memory.add_o _ _ MEM); desf; ins; desf. 
  by rewrite (Memory.add_get0 MEM) in NEW.
Qed.

Lemma memory_write1 mem mem' l from t v rel 
  (ADD: Memory.write Memory.bot mem l from t v rel Memory.bot mem' Memory.op_kind_add)
  l0 t0 from0 m
  (NEW: Memory.get l0 t0 mem' = Some (from0, m)) (NEQ: l <> l0 \/ t <> t0 \/ from <> from0):
  Memory.get l0 t0 mem = Some (from0, m).
Proof.
  destruct ADD; inv PROMISE. 
  rewrite (Memory.add_o _ _ MEM) in NEW; desf; ins; desf; try congruence.
Qed.


Lemma memory_step_write_dom acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem mem' (CLOSED: Memory.closed mem)
  l0 b (DOM : In b acts /\ is_write b /\ loc b = Some l0 -> Memory.get l0 (f b) mem <> None)
  from rel 
  (ADD: Memory.write Memory.bot mem l from (f' a) v rel Memory.bot mem' Memory.op_kind_add):
  In b acts0 /\ is_write b /\ loc b = Some l0 -> Memory.get l0 (f' b) mem' <> None.
Proof.
ins; red in GSTEP; desc.
rewrite ACT_STEP in H; ins; desf; subst.
- assert (l = l0).
    unfold loc, lab in *; destruct b; destruct lb; desf.
  subst.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  intro; desf.
  by apply Memory.bot_finite.
  by destruct CLOSED.
- rewrite F; eauto.
  assert (N: Memory.get l0 (f b) mem <> None).
  eauto.
  destruct (Memory.get l0 (f b) mem) as [[from0 [v0 rel0]]|] eqn:Y; cycle 1.
  by exfalso; auto.
  eapply memory_write0 in Y; try edone.
  intro; desf.
Qed.

Lemma memory_step_write_rmw acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  a l v o (LABa: lab a = Astore l v o) prev (LOCprev: loc prev = Some l)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem mem' (CLOSED: Memory.closed mem)
  from rel 
  (ADD: Memory.write Memory.bot mem l from (f' a) v rel Memory.bot mem' 
                     Memory.op_kind_add)
  l0 b c (RF_RMW: (rf0;; rmw0) b c) (LOC: loc b = Some l0)
  (UPDATES: forall a b (RF_RMW: (rf ;; rmw) a b) (LOC: loc a = Some l0),
                exists m, Memory.get l0 (f b) mem = Some ((f a), m))
  (RMW: forall c, prev <> a -> rf c prev -> f c = from) :
  exists m : Message.t, Memory.get l0 (f' c) mem' = Some (f' b, m).
Proof.
  eapply gstep_rf_rmw with (rf:=rf) in RF_RMW; eauto.
  unfold Relation_Operators.union in RF_RMW; unfold seq at 2 in RF_RMW; desf.
  - specialize (UPDATES b c RF_RMW LOC).
  desc.
  exists m.
  rewrite !F; eauto.
  eapply memory_write0 in UPDATES; eauto.
  unfold seq in RF_RMW; desc; eapply rf_acta; eauto.
  unfold seq in RF_RMW; desc; eapply rmw_actb; eauto.
- eapply RMW in RF_RMW2; try edone.
  rewrite <- F in RF_RMW2; try by eapply rf_acta; eauto.
  rewrite RF_RMW2.
  assert (l = l0).
    eapply loceq_rf in RF_RMW; eauto; congr.
  subst l0.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  by apply Memory.bot_finite.
  by destruct CLOSED.
Qed.

Lemma memory_step_write_cell_eq acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 
  (COH : Coherent acts sb rmw rf mo sc) 
   a l v o (LABa: lab a = Astore l v o) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  ffrom ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  v0 rel mem (CLOSED: Memory.closed mem)
  (SIMCELL : forall to from v rel, Memory.get l to mem = Some (from, Message.mk v rel) ->
          exists b, In b acts /\ is_write b /\ loc b = Some l /\ ffrom b = from 
                    /\ f b = to /\ sim_mem_helper f acts sb rmw rf sc b from v rel.(View.unwrap))
  sc_map (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  tview (SIM_TVIEW : sim_tview f acts sb rmw rf sc tview (thread a))
  (FROM: Time.lt (ffrom' a) (f' a))
  mem' (ADD: Memory.write Memory.bot mem l (ffrom' a) (f' a) v 
          (TView.write_released tview sc_map l (f' a) None o)
     Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l (f' a) mem' = Some (ffrom' a, Message.mk v0 rel)):
  exists b, In b acts0 /\ is_write b /\ loc b = Some l /\
    ffrom' b = ffrom' a /\ f' b = f' a /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b (ffrom' a) v0 rel.(View.unwrap).
Proof.
desc; subst.
  exists a; splits; eauto with acts.
  by red in GSTEP; desc; rewrite ACT_STEP; vauto.
  by unfold loc; destruct (lab a); ins; desf.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  2: by apply Memory.bot_finite.
  2: by destruct CLOSED. 

ins.

assert(LocFun.add l (if Ordering.le Ordering.acqrel o
then View.join (View.join (TView.cur tview) (View.singleton_ur l (f' a)))
(if Ordering.le Ordering.seqcst o then
{| View.pln := TimeMap.bot; View.rlx := TimeMap.bot; View.sc := sc_map |}
else View.bot) else TView.rel tview l) 
(TView.rel tview) l= LocFun.find l (LocFun.add l
(if Ordering.le Ordering.acqrel o then
View.join (View.join (TView.cur tview) (View.singleton_ur l (f' a)))
(if Ordering.le Ordering.seqcst o then
{| View.pln := TimeMap.bot; View.rlx := TimeMap.bot; View.sc := sc_map |}
else View.bot) else TView.rel tview l) (TView.rel tview))).  done.
unfold TView.write_released, TView.write_tview in ADD. simpl in ADD.
rewrite H in ADD. clear H.

rewrite View.join_bot_l in ADD.
destruct tview; simpl.
red in SIM_TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
assert (SCa': Ordering.le Ordering.seqcst o <-> is_sc_wf a).
  by rewrite SCa; eauto 7 with acts.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.
assert (RLXa: Ordering.le Ordering.relaxed o <-> is_rlx_rw a).
  by destruct a; ins; desf.
assert (LOC_A: loc a = Some l). 
  by unfold loc; destruct (lab a); ins; desf.
assert (W: is_write a). 
  by destruct a as [??[]]; ins.

red; splits; try done.
by unfold val, lab in *; destruct a; destruct lb; desf.

desf; red; splits; eauto; ins.

all: try rewrite LocFun.add_spec; desf.
all: ins.
all: try rewrite !tm_join_bot.
all: try rewrite !tm_find_join.
all: try rewrite !tm_find_singleton; desf.
all: try rewrite !time_join_bot.
all: try rewrite tm_find_bot.
all: do 2 (try match goal with 
  | [|- max_value _ _ (Time.join _ _)] => eapply max_value_join end).
all: try match goal with
         | [|- max_value _ _ (LocFun.find _ _)] => eapply max_value_same_set;
           try eapply max_value_new_f with (f':=f'); eauto with acts
         | [|- max_value _ _ Time.bot] => eapply max_value_empty; eauto 
         | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto  end.
all: simpl.
all: try by intro x; split; [intro K; pattern x; exact K|].
all: intro x.
all: try rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A).
all: try rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A).
all: try rewrite (gstep_msg_rel_scr_write COH GSTEP W LOC_A).
all: try split; intro; des; subst; eauto 4.
all: try by (exfalso; eauto).
all: eauto 9.
all: eauto using inclusion_refl2 with rel_mon.
all: try match goal with 
           | H: msg_rel urr _ _ _ _ _ _ _ _ |- _ =>
             cdes GSTEP; eapply actb_msg_urr in H; try done; eauto
           | H: msg_rel rwr _ _ _ _ _ _ _ _ |- _ =>
             cdes GSTEP; eapply actb_msg_rwr in H; try done; eauto
           | H: msg_rel scr _ _ _ _ _ _ _ _ |- _ =>
             cdes GSTEP; eapply actb_msg_scr in H; try done; eauto
         end.
all: try by exfalso; congruence.
all: try by exfalso; destruct o; ins; desf; eauto 3.
Qed.

Lemma memory_step_write_cell_neq acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 
  (COH : Coherent acts sb rmw rf mo sc) 
   a l v o (LABa: lab a = Astore l v o) prev
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  ffrom ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  l0 to from0 v0 rel0 mem
  (SIMCELL : forall to from v rel, Memory.get l0 to mem = Some (from, Message.mk v rel) ->
          exists b, In b acts /\ is_write b /\ loc b = Some l0 /\ ffrom b = from 
                    /\ f b = to /\ sim_mem_helper f acts sb rmw rf sc b from v rel.(View.unwrap))
  sc_map tview mem' 
  (ADD: Memory.write Memory.bot mem l (ffrom' a) (f' a) v 
          (TView.write_released tview sc_map l (f' a) None o) Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l0 to mem' = Some (from0, Message.mk v0 rel0))
  (NEQ: ~ ((l=l0 /\ f' a = to /\ ffrom' a = from0))):
  exists b, In b acts0 /\ is_write b /\ loc b = Some l0 /\
    ffrom' b = from0 /\ f' b = to /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b from0 v0 rel0.(View.unwrap).
Proof.
assert (OLD: Memory.get l0 to mem = Some (from0, Message.mk v0 rel0)).
    eapply memory_write1; try edone; tauto.
  assert (LOC_A: Gevents.loc a = Some l). 
    by unfold Gevents.loc; destruct (lab a); ins; desf.
  assert (W: is_write a). 
    by destruct a as [??[]]; ins.
  clear GET ADD.
  specialize (SIMCELL to from0 v0 rel0 OLD); desc.
  exists b.
  unfold sim_mem_helper in *; desc; splits; try rewrite F; try rewrite F_FROM; eauto.
  by red in GSTEP; desc; rewrite ACT_STEP; right.
  unfold sim_msg in *; desc; splits; eauto. 
  all: ins.
  all: eapply max_value_same_set; try edone.
  all: try eapply max_value_new_f with (f':=f'); try edone. 
  all: simpl; eauto 4 with acts.
  by ins; cdes GSTEP; rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A); 
     split; ins; desf; eauto.
  by ins; cdes GSTEP; rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A); 
     split; ins; desf; eauto.
  by ins; cdes GSTEP; rewrite (gstep_msg_rel_scr_write COH GSTEP W LOC_A); 
     split; ins; desf; eauto.
Qed.

Lemma memory_step_update_cell_eq acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 
  (COH : Coherent acts sb rmw rf mo sc) 
   a l v o (LABa: lab a = Astore l v o) prev c (RF: rf c prev)
v_r o_r (LABprev: lab prev = Aload l v_r o_r)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  ffrom ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  rel mem (CLOSED: Memory.closed mem)
  (SIMCELL : forall to from v rel, Memory.get l to mem = Some (from, Message.mk v rel) ->
          exists b, In b acts /\ is_write b /\ loc b = Some l /\ ffrom b = from 
                    /\ f b = to /\ sim_mem_helper f acts sb rmw rf sc b from v rel.(View.unwrap))
  sc_map (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  tview released_r
tview_r
(TVIEW_R: tview_r = TView.read_tview tview l (f c) released_r o_r)
  (SIM_TVIEW : sim_tview f acts sb rmw rf sc  tview_r  (thread a))
  (FROM: Time.lt (ffrom' a) (f' a))
  v0 mem'
  (ADD : Memory.write Memory.bot mem l (f c) (f' a) v
          (TView.write_released tview_r
             sc_map
             l (f' a) released_r o) Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l (f' a) mem' = Some (ffrom' a, Message.mk v0 rel))
  (SIMMSG : sim_msg f acts sb rmw rf sc c (View.unwrap released_r)):
  exists b, In b acts0 /\ is_write b /\ loc b = Some l /\
    ffrom' b = ffrom' a /\ f' b = (f' a) /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b (ffrom' a) v0 rel.(View.unwrap).
Proof.
subst; ins.
  exists a; splits; eauto with acts.
  by red in GSTEP; desc; rewrite ACT_STEP; vauto.
  by unfold loc; destruct (lab a); ins; desf.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  2: by apply Memory.bot_finite.
  2: by destruct CLOSED. 

assert(
 LocFun.add l (if Ordering.le Ordering.acqrel o then View.join (View.join (View.join (View.join (TView.cur tview) (View.singleton_rw l (f c))) (if Ordering.le Ordering.acqrel o_r then View.unwrap released_r else View.bot)) (View.singleton_ur l (f' a))) (if Ordering.le Ordering.seqcst o then {| View.pln := TimeMap.bot; View.rlx := TimeMap.bot; View.sc := sc_map |} else View.bot) else TView.rel tview l) (TView.rel tview) l = LocFun.find l (LocFun.add l (if Ordering.le Ordering.acqrel o then View.join (View.join (View.join (View.join (TView.cur tview) (View.singleton_rw l (f c))) (if Ordering.le Ordering.acqrel o_r then View.unwrap released_r else View.bot)) (View.singleton_ur l (f' a))) (if Ordering.le Ordering.seqcst o then {| View.pln := TimeMap.bot; View.rlx := TimeMap.bot; View.sc := sc_map |} else View.bot) else TView.rel tview l) (TView.rel tview) )
). done.
unfold TView.write_released, TView.write_tview in ADD. simpl in ADD.
rewrite H in ADD. clear H.

(* rewrite View.join_bot_l in ADD. *)
destruct tview; simpl.
red in SIM_TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
assert (SCa': Ordering.le Ordering.seqcst o <-> is_sc_wf a).
  by rewrite SCa; eauto 7 with acts.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.
assert (RLXa: Ordering.le Ordering.relaxed o <-> is_rlx_rw a).
  by destruct a; ins; desf.
assert (LOC_A: loc a = Some l). 
  by unfold Gevents.loc; destruct (lab a); ins; desf.
assert (W: is_write a). 
  by destruct a as [??[]]; ins.

red in SIMMSG; desc.

rewrite GET in ADD.
inversion ADD.
subst v0 rel.





red; splits; try done.
by unfold val, lab in *; destruct a; destruct lb; desf.

Admitted.

Lemma memory_step_write acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a
  (COH : Coherent acts sb rmw rf mo sc) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  ffrom fto mem (SIM_MEM : sim_mem ffrom fto acts sb rmw rf sc mem) 
  ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  fto' (F_TO : forall b, In b acts -> fto' b = fto b) (MON: monotone mo0 fto')
  l v o (LABa: lab a = Astore l v o)
  (CLOSED: Memory.closed mem)
  (FROM: Time.lt (ffrom' a) (fto' a))  
  sc_map (SIM_SC_MAP : forall l, max_value fto (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  tview (SIM_TVIEW : sim_tview fto acts sb rmw rf sc tview (thread a))
  mem' (ADD: Memory.write Memory.bot mem l (ffrom' a) (fto' a) v 
  (TView.write_released tview sc_map l (fto' a) None o)
 Memory.bot mem' Memory.op_kind_add):
  sim_mem ffrom' fto' acts0 sb0 rmw0 rf0 sc0 mem'.
Proof.
red; ins.
specialize (SIM_MEM l0); desc; splits; ins.
- eapply memory_step_write_dom; eauto.
- destruct (classic (l=l0 /\ fto' a = to /\ ffrom' a = from)); desc; subst.
  by eapply memory_step_write_cell_eq; eauto.
  by eapply memory_step_write_cell_neq; eauto.
- eapply memory_step_write_rmw with (prev:=a); eauto.
  by unfold loc; ins; desf.
  eby ins.
Qed.

Lemma memory_step_update acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a
  (COH : Coherent acts sb rmw rf mo sc) 
  b (RF: rf b prev) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  ffrom fto mem (SIM_MEM : sim_mem ffrom fto acts sb rmw rf sc mem) 
  ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  fto' (F_TO : forall b, In b acts -> fto' b = fto b) (MON: monotone mo0 fto')
  l v o (LABa: lab a = Astore l v o)
  v_r o_r (LABp: lab prev = Aload l v_r o_r)
  (CLOSED: Memory.closed mem)
  (FROM: Time.lt (ffrom' a) (fto' a))  
  sc_map (SIM_SC_MAP : forall l, max_value fto (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  tview released_r
  (SIM_TVIEW : sim_tview fto acts sb rmw rf sc  (TView.read_tview tview l (fto b) released_r o_r)  (thread a))
  mem' 
  (ADD: Memory.write Memory.bot mem l (fto b) (fto' a) v
          (TView.write_released (TView.read_tview tview l (fto b) released_r o_r) sc_map
             l (fto' a) released_r o) Memory.bot mem' Memory.op_kind_add)
  (SIMMSG : sim_msg fto acts sb rmw rf sc b (View.unwrap released_r)):
  sim_mem ffrom' fto' acts0 sb0 rmw0 rf0 sc0 mem'.
Proof.
red; ins.
specialize (SIM_MEM l0); desc; splits; ins.
eapply memory_step_write_dom; eauto.
- destruct (classic (l=l0 /\ fto' a = to /\ ffrom' a = from)); desc; subst.
  by eapply memory_step_update_cell_eq; eauto.
  eapply memory_step_write_cell_neq; eauto.
admit.
- eapply memory_step_write_rmw with (prev:=prev); try edone.
  by unfold loc; ins; desf.
  ins; replace b with c; try done.
  eby cdes COH; cdes WF; eapply WF_RF.
Admitted.

(******************************************************************************)
(** * Lemmas for the fence step   *)
(******************************************************************************)

Lemma tview_step_scfence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w)
  (SC: is_sc a)
  (*IS_ACQ: is_acq a*)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  tview (TVIEW: sim_tview f acts sb rmw rf sc tview (thread a))
  (WF: TView.wf tview) :
  sim_tview f acts0 sb0 rmw0 rf0 sc0 (TView.write_fence_tview
     (TView.read_fence_tview tview o_r) sc_map o_w) (thread a).
Proof.
  assert (FENCE: is_fence a).
    by destruct a; ins; desf.
  assert (NR: ~ is_read a).
    eauto with acts.

  assert (SCa: Ordering.le Ordering.seqcst o_w).
     by destruct a; ins; desf.
  assert (SCa': Ordering.le Ordering.seqcst o_w <-> is_sc_wf a).
    by rewrite SCa; eauto 7 with acts.
  assert (RAa: Ordering.le Ordering.acqrel o_r <-> is_acq a).
     by destruct a; ins; desf.
  assert (RAr: Ordering.le Ordering.acqrel o_w).
     by destruct a; ins; desf; destruct o_w.

  destruct WF.
  destruct tview; simpls.
  unfold TView.write_fence_tview, TView.read_fence_tview,
         TView.write_fence_sc; simpl.
  simpl; rewrite SCa, RAr; simpl.
desf.
{
  assert (K: forall l, 
          max_value f (S_tm acts0 sb0 rmw0 rf0 l)
           (LocFun.find l (TimeMap.join sc_map (View.sc acq)))).
    cdes TVIEW; cdes ACQ0; ins. 
    ins; rewrite !tm_find_join.
    ins; eapply max_value_join; [eapply SIM_SC_MAP| |]; eauto.
    intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf; 
    eauto using inclusion_refl2 with rel_mon.

  unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins; desf.


all: try rewrite TimeMap.le_join_r with (r := TimeMap.join _ _).
all: try eapply max_value_same_set; try apply K; 
     eauto using gstep_t_cur_urr_scfence,
     gstep_t_cur_rwr_scfence,
     gstep_t_cur_scr_scfence,
     gstep_t_acq_urr_scfence,
     gstep_t_acq_rwr_scfence,
     gstep_t_acq_scr_scfence,
     gstep_t_rel_urr_scfence,
     gstep_t_rel_rwr_scfence,
     gstep_t_rel_scr_scfence.
all: try etransitivity; [|by apply TimeMap.join_r]; vauto.
by destruct ACQ; etransitivity; eauto.
by destruct ACQ; eauto.
}
{
  assert (K: forall l, 
          max_value f (S_tm acts0 sb0 rmw0 rf0 l)
           (LocFun.find l (TimeMap.join sc_map (View.sc cur)))).
    cdes TVIEW; cdes CUR0; ins. 
    ins; rewrite !tm_find_join.
    ins; eapply max_value_join; [eapply SIM_SC_MAP| |]; eauto.
    intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf; 
    eauto using inclusion_refl2 with rel_mon; exfalso; eauto.

  red in TVIEW; ins; desf; red in ACQ0; desf.
  unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins; desf.
all: try match goal with 
       |- max_value _ (t_acq _ _ _ _ _ _ _ _) _ => 
         rewrite tm_find_join; eapply max_value_join; eauto
     end.
all: try eapply max_value_same_set; try apply K;
     eauto using gstep_t_cur_urr_scfence,
     gstep_t_cur_rwr_scfence,
     gstep_t_cur_scr_scfence,
     gstep_t_acq_urr_scfence,
     gstep_t_acq_rwr_scfence,
     gstep_t_acq_scr_scfence,
     gstep_t_rel_urr_scfence,
     gstep_t_rel_rwr_scfence,
     gstep_t_rel_scr_scfence.
  all: intro.
  all: try rewrite (gstep_t_acq_urr_nonread COH GSTEP NR), or_comm.
  all: try rewrite (gstep_t_acq_rwr_nonread COH GSTEP NR), or_comm.
  all: try rewrite (gstep_t_acq_scr_nonread COH GSTEP NR), or_comm.
  all: apply or_more; ins;
     eauto using gstep_t_cur_urr_scfence,
     gstep_t_cur_rwr_scfence,
     gstep_t_cur_scr_scfence.
}
Qed.


Lemma tview_step_rafence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w) (NSC: ~ is_sc a)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  tview (TVIEW: sim_tview f acts sb rmw rf sc tview (thread a)):
  sim_tview f acts0 sb0 rmw0 rf0 sc0 (TView.write_fence_tview
     (TView.read_fence_tview tview o_r) sc_map o_w) (thread a).
Proof.

  assert (FENCE: is_fence a).
    by destruct a; ins; desf.
  assert (NR: ~ is_read a).
  eauto with acts.

  assert (SCa: Ordering.le Ordering.seqcst o_w = false).
    by destruct a; ins; desf; destruct o_w; ins; desf; destruct NSC; ins. 
  assert (RAa: Ordering.le Ordering.acqrel o_r <-> is_acq a).
    by destruct a; ins; desf.
  assert (RAr: Ordering.le Ordering.acqrel o_w <-> is_rel a).
    by destruct a; ins; desf.

  destruct tview; simpl.
  unfold TView.write_fence_tview, TView.read_fence_tview,
         TView.write_fence_sc.

  red in TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
  unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins; desf.

  all: try rewrite !cap_join_bot.
  all: ins.
  all: try rewrite !tm_join_bot.
  all: try rewrite !tm_find_join.
  all: try rewrite !tm_find_singleton; desf.
  all: try rewrite !time_join_bot.
  all: do 2 (try match goal with
                   | [|- max_value _ _ (Time.join _ _)] => eapply max_value_join  end).
  all: try match goal with
             | [|- max_value _ _ (LocFun.find _ _)] => 
               eapply max_value_same_set; eauto with acts
             | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto end.
  all: try by intro x; split; [intro K; pattern x; exact K|].
  all: intro x.
  all: try rewrite (gstep_t_acq_urr_nonread COH GSTEP NR).
  all: try rewrite (gstep_t_acq_rwr_nonread COH GSTEP NR).
  all: try rewrite (gstep_t_acq_scr_nonread COH GSTEP NR).
  all: try rewrite (gstep_t_cur_urr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_cur_rwr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_cur_scr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_rel_urr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_rel_rwr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_rel_scr_rafence COH GSTEP FENCE).
  all: ins.
  all: try (split; ins; desf; eauto 3).
  all: try by exfalso; eauto.
  all: eauto using inclusion_refl2 with rel_mon.
  all: eauto 8 using inclusion_refl2 with rel_mon.
Qed.

Lemma sc_map_step_fence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  prev a o_r o_w (LABa : lab a = Afence o_r o_w)
  tview (TVIEW : sim_tview f acts sb rmw rf sc tview (thread a))
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a):
  forall l, max_value f (S_tm acts0 sb0 rmw0 rf0 l)
     (LocFun.find l (TView.write_fence_sc
        (TView.read_fence_tview tview o_r) sc_map o_w)).
Proof.
  assert (SCa: Ordering.le Ordering.seqcst o_w <-> is_sc a).
    by destruct a; ins; desf; destruct o_w; ins; desf.
  assert (SCa': Ordering.le Ordering.seqcst o_w <-> is_sc_wf a).
    by rewrite SCa; eauto 7 with acts.
  assert (RAa: Ordering.le Ordering.acqrel o_r <-> is_acq a).
    by destruct a; ins; desf.
  assert (RAr: Ordering.le Ordering.acqrel o_w <-> is_rel a).
    by destruct a; ins; desf.
  assert(F : is_fence a).
    by eauto with acts.
  red in TVIEW; desc; clear REL; red in CUR; red in ACQ; desc.
  intro; unfold TView.write_fence_sc, TView.read_fence_tview; simpl; desf; ins.
  all: try rewrite !cap_join_bot.
  all: ins.
  all: try rewrite !tm_join_bot.
  all: try rewrite !tm_find_join.
  all: try rewrite !tm_find_singleton; desf.
  all: try rewrite !time_join_bot.
  all: do 2 (try match goal with
                   | [|- max_value _ _ (Time.join _ _)] => eapply max_value_join  end).
  all: try match goal with
             | [|- max_value _ _ (LocFun.find _ _)] => 
               eapply max_value_same_set; eauto with acts
             | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto end.
  by intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf;
    eauto using inclusion_refl2 with rel_mon.
  by intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf;
    eauto using inclusion_refl2 with rel_mon; exfalso; eauto.
  by intro; eapply gstep_S_tm_other; eauto. 
Qed.
