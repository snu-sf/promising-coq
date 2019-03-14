(******************************************************************************)
(** * Simulation between axiomatic and operational machines *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import sflib.
From Paco Require Import paco.

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
all: desf; eauto with acts.
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
all: ins. 
all: try eapply gstep_t_cur_other;  
     try eapply gstep_t_acq_other;  
     eauto using gstep_urr_a, gstep_rwr_a, urr_mon, rwr_mon.
all: desf; eauto with acts.
all: split; intro H; destruct H; desc; auto.
all: try by left; 
      eapply gstep_t_rel_other with (acts':=acts'); 
      eauto using gstep_urr_a, gstep_rwr_a, urr_mon, rwr_mon.
all: right; splits; cdes GSTEP; auto; rewrite ACT_STEP in *; vauto.
all: by destruct H0; congruence.
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

assert (~ is_fence a /\ ~ is_write a /\ is_read a).
  by destruct a; ins; desf.

destruct tview; simpl.
red in TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
red in SIM_MSG; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.
all: unfold View.singleton_ur_if.
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
all: try intro x.

all: try (rewrite (gstep_t_cur_urr_read COH GSTEP b RFb); split; ins; desf; try by eauto 10; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_cur_rwr_read COH GSTEP b RFb); split; ins; desf; try by eauto 10; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_acq_urr_read COH GSTEP b RFb); split; ins; desf; try by eauto 10; try by (exfalso; eauto)).
all: try (rewrite (gstep_t_acq_rwr_read COH GSTEP b RFb); split; ins; desf; try by eauto 10; try by (exfalso; eauto)).

by exfalso; destruct o; vauto.
all: try rewrite (gstep_t_rel_other GSTEP _ _ (gstep_urr_a COH GSTEP (l:=_)) 
                           (urr_mon GSTEP (l:=_))); auto.
all: try rewrite (gstep_t_rel_other GSTEP _ _ (gstep_rwr_a COH GSTEP (l:=_)) 
                           (rwr_mon GSTEP (l:=_))); auto.
all: by cdes GSTEP; rewrite ACT_STEP; split; ins; desf; eauto 8.
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
  all: ins; eapply max_value_same_set; try edone; ins; split; ins; desf; vauto; left.
  all: try eby eapply gstep_msg_rel_urr_nonwrite with (acts:=acts) (acts':=acts0).
  all: try eby eapply gstep_msg_rel_rwr_nonwrite with (acts:=acts) (acts':=acts0).
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
assert (X: forall x, In x acts -> In x acts0).
  by cdes GSTEP; rewrite ACT_STEP in *; ins; desf; auto.

assert (XX: forall x, In x acts0 -> In x acts \/ a = x).
  by cdes GSTEP; rewrite ACT_STEP in *; ins; desf; auto.

assert (WRITE: is_write a).
  eauto with acts.
assert (NR: ~ is_read a).
  eauto with acts.

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
all: try by ins; desf; eauto 4 with acts.
all: simpl.
all: try by intro x; split; [intro K; pattern x; exact K|].
all: intro x.

all: clear 
  CUR_UR CUR_RW 
  ACQ_UR ACQ_RW 
  REL_UR REL_RW.

  all: try rewrite (gstep_t_acq_urr_nonread COH GSTEP NR).  
  all: try rewrite (gstep_t_acq_rwr_nonread COH GSTEP NR).  
  all: try rewrite (gstep_t_cur_urr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_cur_rwr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_rel_urr_write COH GSTEP WRITE).
  all: try rewrite (gstep_t_rel_rwr_write COH GSTEP WRITE).
  all: split; ins; desf; eauto 3 with acts.
  all: try by exfalso; eauto with acts.
  all: eauto 10 with rel.
  all: eauto using inclusion_refl2 with rel_mon.

  all: try by apply XX in H0; desf; eauto 8.
  all: try by right; splits; eauto; cdes GSTEP; rewrite ACT_STEP; vauto.
  all: destruct (classic (a=x)); eauto; left; exists x, x; splits; eauto; vauto.
  2: eapply ur_in_rw.
  all: exists x; splits; eauto; left; exists x; splits; eauto.
  all :exists x; splits; try red; eauto.
  all: exists x; splits; eauto; red; splits; eauto; apply XX in H0; tauto.
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
  sc_map 
  tview (SIM_TVIEW : sim_tview f acts sb rmw rf sc tview (thread a))
  (FROM: Time.lt (ffrom' a) (f' a))
  mem' (ADD: Memory.write Memory.bot mem l (ffrom' a) (f' a) v 
          (TView.write_released tview sc_map l (f' a) None o)
     Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l (f' a) mem' = Some (ffrom' a, Message.mk v0 rel))
  (EXpln: Time.le (LocFun.find l (View.pln ((TView.rel tview) l))) (f' a)) 
  (EXrlx: Time.le (LocFun.find l (View.rlx ((TView.rel tview) l))) (f' a)) 
  (COH' : Coherent acts0 sb0 rmw0 rf0 mo0 sc0) :
  exists b, In b acts0 /\ is_write b /\ loc b = Some l /\
    ffrom' b = ffrom' a /\ f' b = f' a /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b (ffrom' a) v0 rel.(View.unwrap).
Proof.

assert (XX'pln: Time.join (LocFun.find l (View.pln ((TView.rel tview) l))) (f' a) = f' a).
{ clear -EXpln.
apply TimeFacts.antisym; try by eapply Time.join_r.
apply Time.join_spec; vauto. }

assert (XX'rlx: Time.join (LocFun.find l (View.rlx ((TView.rel tview) l))) (f' a) = f' a).
{ clear -EXrlx.
apply TimeFacts.antisym; try by eapply Time.join_r.
apply Time.join_spec; vauto. }

exists a; splits; eauto with acts.
by red in GSTEP; desc; rewrite ACT_STEP; vauto.
by unfold loc; destruct (lab a); ins; desf.
apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
2: by apply Memory.bot_finite.
2: by destruct CLOSED. 

unfold TView.write_released, TView.write_tview in ADD. simpl in ADD.
rewrite View.join_bot_l in ADD.
unfold LocFun.add in ADD; ins.
destruct (LocSet.Facts.eq_dec l l); try done.
destruct tview; simpl in *.
red in SIM_TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.
assert (RLXa: Ordering.le Ordering.relaxed o <-> is_rlx_rw a).
  by destruct a; ins; desf.
assert (LOC_A: loc a = Some l). 
  by unfold loc; destruct (lab a); ins; desf.
assert (W: is_write a). 
  by destruct a as [??[]]; ins.

rewrite GET in ADD.
clear GET ACQ_UR ACQ_RW CLOSED.

red; splits; auto.
by unfold val, lab in *; destruct a; destruct lb; desf.

assert (YYpln: is_rlx_rw a -> max_value f'
  (fun a0 : event =>
   msg_rel urr acts0 sb0 rmw0 rf0 sc0 l a0 a \/ is_rlx_rw a /\ loc a = Some l /\ a0 = a)
  (f' a)).
  { red; unnw.
  split. ins; desf; vauto.
  destruct (classic (a=a0)); vauto.
  left.
  eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply acta_msg_urr; eauto.
  by eapply msg_rel_urr_doma1; eauto.
  by eapply msg_rel_urr_doma2; eauto.
  intro; destruct INa; desc.
  eapply Coherent_urr_rel with (acts:=(a :: acts)); try edone.
  right; exists a; split; eauto; vauto.
  }

assert (YYrlx: is_rlx_rw a -> max_value f'
  (fun a0 : event =>
   msg_rel rwr acts0 sb0 rmw0 rf0 sc0 l a0 a \/ is_rlx_rw a /\ loc a = Some l /\ a0 = a)
  (f' a)).
  { red; unnw.
  split. ins; desf; vauto.
  destruct (classic (a=a0)); vauto.
  left.
  eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply acta_msg_rwr; eauto.
  by eapply msg_rel_rwr_doma1; eauto.
  by eapply msg_rel_rwr_doma2; eauto.
  intro; destruct INa; desc.
  eapply Coherent_rwr_rel with (acts:=(a :: acts)); try edone.
  right; exists a; split; eauto; vauto.
  }

red; splits; intro l0.

all: specialize (CUR_UR l0).
all: specialize (CUR_RW l0).
all: specialize (REL_UR l l0).
all: specialize (REL_RW l l0).
all: eapply max_value_new_f with (f:=f) (f':=f') in CUR_UR;
     try by intro; ins; eauto 4 with acts.
all: eapply max_value_new_f with (f:=f) (f':=f') in CUR_RW;
     try by intro; ins; eauto 4 with acts.
all: eapply max_value_new_f with (f:=f) (f':=f') in REL_UR;
     try by intro; ins; eauto 4 with acts.
all: eapply max_value_new_f with (f:=f) (f':=f') in REL_RW;
     try by intro; ins; eauto 4 with acts.
all: try by ins; desf; eauto 4 with acts.
all: desf; simpl.
all: try rewrite !LocFun.add_spec; desf.
all: ins.
all: try rewrite !LocFun.add_spec; desf.
all: try rewrite !tm_join_bot.
all: try rewrite !tm_find_join.
all: try rewrite !tm_find_singleton; desf.
all: try rewrite !time_join_bot.
all: try rewrite tm_find_bot.
all: try by rewrite XX'pln; eauto.
all: try by rewrite XX'rlx; eauto.
all: do 2 (try match goal with 
  | [|- max_value _ _ (Time.join _ _)] => eapply max_value_join end).

all: try match goal with
         | [|- max_value _ _ (LocFun.find _ _)] => eapply max_value_same_set; eauto
         | [|- max_value _ _ Time.bot] => eapply max_value_empty; eauto 
         | [|- max_value _ _ _ ] => eapply max_value_singleton; eauto  end.
all: simpl.
all: try by intro x; split; [intro K; pattern x; exact K|].

all: intro x; simpl.
all: try rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A).
all: try rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A).
all: try split; intro; des; subst; eauto 4.
all: try by (exfalso; eauto).
all: eauto 9.
all: eauto using inclusion_refl2 with rel_mon.
all: try match goal with 
           | H: msg_rel urr _ _ _ _ _ _ _ _ |- _ =>
             cdes GSTEP; eapply actb_msg_urr in H; try done; eauto
           | H: msg_rel rwr _ _ _ _ _ _ _ _ |- _ =>
             cdes GSTEP; eapply actb_msg_rwr in H; try done; eauto
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
  sc_map tview mem' released_r
  (ADD: Memory.write Memory.bot mem l (ffrom' a) (f' a) v 
          (TView.write_released tview sc_map l (f' a) released_r o) Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l0 to mem' = Some (from0, Message.mk v0 rel0))
  (NEQ: ~ ((l=l0 /\ f' a = to /\ ffrom' a = from0))) :
  exists b, In b acts0 /\ is_write b /\ loc b = Some l0 /\
    ffrom' b = from0 /\ f' b = to /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b from0 v0 rel0.(View.unwrap).
Proof.
  assert (OLD: Memory.get l0 to mem = Some (from0, Message.mk v0 rel0)).
    destruct ADD; inv PROMISE.
    rewrite (Memory.add_o _ _ MEM) in GET; desf; ins; desf; try congruence; try edone; tauto.
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
  all: ins; desf; eauto 8 with acts.
  all: try by ins; cdes GSTEP; rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A); 
       split; ins; desf; eauto.
  all: try by ins; cdes GSTEP; rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A); 
       split; ins; desf; eauto.
Qed.

Lemma join_rr x l r : Time.le x r -> Time.le x (Time.join l r).
  ins; etransitivity; eauto using Time.join_r.
Qed.

Lemma memory_step_update_cell_eq acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 
  (COH : Coherent acts sb rmw rf mo sc) 
   a l v o (LABa: lab a = Astore l v o) prev c (RF: rf c prev)
  v_r o_r (LABprev: lab prev = Aload l v_r o_r)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  ffrom ffrom' (F_FROM : forall b, In b acts -> ffrom' b = ffrom b)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  rel mem (CLOSED: Memory.closed mem)
  sc_map
  tview released_r tview_r
  (TVIEW_R: tview_r = TView.read_tview tview l (f c) released_r o_r)
  (SIM_TVIEW : sim_tview f acts sb rmw rf sc  tview_r  (thread a))
  (FROM: Time.lt (ffrom' a) (f' a))
  v0 mem' (ADD : Memory.write Memory.bot mem l (f c) (f' a) v
          (TView.write_released tview_r sc_map
             l (f' a) released_r o) Memory.bot mem' Memory.op_kind_add)
  (GET: Memory.get l (f' a) mem' = Some (ffrom' a, Message.mk v0 rel))
  (SIMMSG : sim_msg f acts sb rmw rf sc c (View.unwrap released_r))
  (EXpln: Time.le (LocFun.find l (View.pln ((TView.rel tview) l))) (f' a)) 
  (EXrlx: Time.le (LocFun.find l (View.rlx ((TView.rel tview) l))) (f' a)) 
  (EXcur_pln: Time.le (LocFun.find l (View.pln (TView.cur tview))) (f' a))
  (EXcur_rlx: Time.le (LocFun.find l (View.rlx (TView.cur tview))) (f' a))
  (COH' : Coherent acts0 sb0 rmw0 rf0 mo0 sc0) :
  exists b, In b acts0 /\ is_write b /\ loc b = Some l /\
    ffrom' b = ffrom' a /\ f' b = (f' a) /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b (ffrom' a) v0 rel.(View.unwrap).
Proof.
  assert (XX'pln: Time.join (LocFun.find l (View.pln ((TView.rel tview) l))) (f' a) = f' a).
  { clear -EXpln.
  apply TimeFacts.antisym; try by eapply Time.join_r.
  apply Time.join_spec; vauto. }

  assert (XX'rlx: Time.join (LocFun.find l (View.rlx ((TView.rel tview) l))) (f' a) = f' a).
  { clear -EXrlx.
  apply TimeFacts.antisym; try by eapply Time.join_r.
  apply Time.join_spec; vauto. }

  subst; ins.
  exists a; splits; eauto with acts.
  by red in GSTEP; desc; rewrite ACT_STEP; vauto.
  by unfold loc; destruct (lab a); ins; desf.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  2: by apply Memory.bot_finite.
  2: by destruct CLOSED. 

unfold TView.write_released, TView.write_tview in ADD. simpl in ADD.
rewrite GET in ADD.
inversion ADD.
subst v0 rel.
rewrite H0 in *.
destruct tview; simpl.
red in SIM_TVIEW; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins.

clear H0 GET ACQ_UR ACQ_RW CLOSED.

assert (forall z, rf z prev -> z = c).
  by intros; cdes COH; cdes WF; eapply WF_RF; eauto.
assert (prev <> a).
  eby intro; subst; destruct a as [??[]].
assert (INc: In c acts).
  by eapply rf_acta in RF; eauto.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.
assert (RLXa: Ordering.le Ordering.relaxed o <-> is_rlx_rw a).
  by destruct a; ins; desf.
assert (LOC_A: loc a = Some l). 
  by unfold Gevents.loc; destruct (lab a); ins; desf.
assert (W: is_write a). 
  by destruct a as [??[]]; ins.
assert (RAprev: Ordering.le Ordering.acqrel o_r <-> is_acq prev).
  by destruct prev; ins; desf.
assert (RLXprev: Ordering.le Ordering.relaxed o_r <-> is_rlx_rw prev).
  by destruct prev; ins; desf.
assert (WRITEc: is_write c).
  by eapply rf_doma in RF; eauto.
assert (loc c = Some l).
  by eapply loceq_rf in RF; eauto; destruct prev; ins; desf.

red in SIMMSG; desc.

red; splits; auto.
by unfold val, lab in *; destruct a; destruct lb; desf.

assert (YYpln: is_rlx_rw a -> max_value f'
  (fun a0 : event =>
   msg_rel urr acts0 sb0 rmw0 rf0 sc0 l a0 a \/ is_rlx_rw a /\ loc a = Some l /\ a0 = a)
  (f' a)).
  { red; unnw.
  clear REL_RW REL_UR CUR_RW CUR_UR.
  split; ins; desf; vauto.
  destruct (classic (a=a0)); vauto.
  left.
  eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply acta_msg_urr; eauto.
  by eapply msg_rel_urr_doma1; eauto.
  by eapply msg_rel_urr_doma2; eauto.
  intro; destruct INa; desc.
  eapply Coherent_urr_rel with (acts:=(a :: acts)); try edone.
  right; exists a; split; eauto; vauto.
  } 

assert (YYrlx: is_rlx_rw a -> max_value f'
  (fun a0 : event =>
   msg_rel rwr acts0 sb0 rmw0 rf0 sc0 l a0 a \/ is_rlx_rw a /\ loc a = Some l /\ a0 = a)
  (f' a)).
  { red; unnw.
  clear REL_RW REL_UR CUR_RW CUR_UR.
  split. ins; desf; vauto.
  destruct (classic (a=a0)); vauto.
  left.
  eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply acta_msg_rwr; eauto.
  by eapply msg_rel_rwr_doma1; eauto.
  by eapply msg_rel_rwr_doma2; eauto.
  intro; destruct INa; desc.
  eapply Coherent_rwr_rel with (acts:=(a :: acts)); try edone.
  right; exists a; split; eauto; vauto.
  }

assert (ZZpln: Time.le (LocFun.find l (View.pln (View.unwrap released_r))) (f' a)).
  { etransitivity; try eby left.
  specialize (UR l).
  red in UR; desc; destruct MAX as [MAX0|MAX1]; desc.
  by rewrite MAX1; eapply Time.bot_spec.
  etransitivity; try edone.
  destruct (classic (c=a_max)); vauto.
  destruct INam; desc; vauto.
  assert (INa_max: In a_max acts).
    by eapply acta_msg_urr; eauto.
  rewrite <- !F; try done.
  left; eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply msg_rel_urr_doma1; eauto.
  by eapply msg_rel_urr_doma2; eauto.
  intro MO.
  unfold msg_rel, m_rel, seq in *; desc.
  eapply gstep_mo with (acts:=acts) in MO; try edone; try by (intro; subst; eauto).
  eapply Coherent_urr_rel with (acts:=acts); try edone.
  } 

assert (ZZrlx: Time.le (LocFun.find l (View.rlx (View.unwrap released_r))) (f' a)).
  { etransitivity; try eby left.
  specialize (RW l).
  red in RW; desc; destruct MAX as [MAX0|MAX1]; desc.
  by rewrite MAX1; eapply Time.bot_spec.
  etransitivity; try edone.
  destruct (classic (c=a_max)); vauto.
  destruct INam; desc; vauto.
  assert (INa_max: In a_max acts).
    by eapply acta_msg_rwr; eauto.
  rewrite <- !F; try done.
  left; eapply MON.
  eapply wf_mo_tot; cdes GSTEP; cdes WF'; eauto; vauto.
  by eapply msg_rel_rwr_doma1; eauto.
  by eapply msg_rel_rwr_doma2; eauto.
  intro MO.
  unfold msg_rel, m_rel, seq in *; desc.
  eapply gstep_mo with (acts:=acts) in MO; try edone; try by (intro; subst; eauto).
  eapply Coherent_rwr_rel with (acts:=acts); try edone.
  } 


assert (ZZ: forall A (P Q: A -> Prop), (forall x, P x /\ Q x) -> (forall x, P x) /\ (forall x, Q x)).
  by clear; split; ins; specialize (H x); desf.

apply ZZ; intro l0.

unfold LocFun.add; rewrite Loc.eq_dec_eq.
destruct (classic (l0 = l)).

- subst.
  destruct (classic (is_rlx_rw a)); cycle 1.
  {
  destruct o; ins; try (by exfalso; ins; desf; eauto 3).
  desf; rewrite tm_find_bot in *; split; eapply max_value_empty; eauto.
  all: intro x; try rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A).
  all: try rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A).
  all: intro X; desf.
  all: try by cdes GSTEP; eapply actb_msg_urr in X; try done; eauto 2.
  all: try by cdes GSTEP; eapply actb_msg_rwr in X; try done; eauto 2.
  all: try by exfalso; destruct o_r; ins; desf; eauto 3.
  } 
  split; match goal with 
    [|- max_value _ _ ?x] => replace x with (f' a); auto
  end.
  all: unfold View.singleton_ur_if, View.singleton_ur.
  all: desf; simpls.
  all: try rewrite !tm_find_join in *.
  all: try rewrite !tm_find_join in *.
  all: try rewrite !tm_find_singleton in *; desf.
  all: try rewrite !time_join_bot in *.
  all: try rewrite tm_find_bot in *.
  all: apply TimeFacts.antisym.
  all: eauto 8 using join_rr, Time.join_r.
  all: try (by exfalso; auto).
  all: repeat apply Time.join_spec; vauto.
- specialize (UR l0).
  specialize (RW l0).
  specialize (CUR_UR l0).
  specialize (CUR_RW l0).
  specialize (REL_UR l l0).
  specialize (REL_RW l l0).
  eapply max_value_new_f with (f:=f) (f':=f') in UR;
      try by intro; ins; desf; eauto 4 with acts.
  eapply max_value_new_f with (f:=f) (f':=f') in RW;
      try by intro; ins; desf; eauto 4 with acts.
  eapply max_value_new_f with (f:=f) (f':=f') in CUR_UR;
      try by intro; ins; desf; eauto 4 with acts.
  eapply max_value_new_f with (f:=f) (f':=f') in CUR_RW;
      try by intro; ins; desf; eauto 4 with acts.
  eapply max_value_new_f with (f:=f) (f':=f') in REL_UR;
      try by intro; ins; desf; eauto 4 with acts.
  eapply max_value_new_f with (f:=f) (f':=f') in REL_RW;
      try by intro; ins; desf; eauto 4 with acts.

  unfold View.singleton_ur_if, View.singleton_ur.
  unfold LocFun.add; desf; simpls.
  all: rewrite !tm_find_join in *.
  all: try rewrite !tm_find_singleton in *; desf.
  all: try rewrite !time_join_bot in *.
  all: try rewrite tm_find_bot in *.
  all: splits.


  all: do 1 (try match goal with 
    | [|- max_value _ _ (Time.join _ _)] => eapply max_value_join; try edone end).
  all: try match goal with
           | [|- max_value _ _ Time.bot] => eapply max_value_empty; eauto end.

  all: simpl.
  all: try by intro x; split; [intro K; pattern x; exact K|].
  all: intro x.
  all: try rewrite (gstep_msg_rel_urr_write COH GSTEP W LOC_A).
  all: try rewrite (gstep_msg_rel_rwr_write COH GSTEP W LOC_A).
  all: try by exfalso; destruct o_r; ins; desf; eauto 3.
  all: try split; intro; des; subst; eauto 4.
  all: try by exfalso; congruence.
  all: try by match goal with 
             | H: msg_rel urr _ _ _ _ _ _ _ _ |- _ =>
               cdes GSTEP; eapply actb_msg_urr in H; try done; eauto 2
             | H: msg_rel rwr _ _ _ _ _ _ _ _ |- _ =>
               cdes GSTEP; eapply actb_msg_rwr in H; try done; eauto 2
           end.
  all: try by (exfalso; eauto 3).
  all: try by replace c with z; eauto 3.
  all: try by exfalso; destruct o; ins; desf; eauto 3.
  all: eauto using inclusion_refl2 with rel_mon.
  all: eauto 10.
Qed.

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
  (TView.write_released tview sc_map l (fto' a) None o) Memory.bot mem' Memory.op_kind_add)
  (EXpln: Time.le (LocFun.find l (View.pln ((TView.rel tview) l))) (fto' a)) 
  (EXrlx: Time.le (LocFun.find l (View.rlx ((TView.rel tview) l))) (fto' a)) 
  (COH' : Coherent acts0 sb0 rmw0 rf0 mo0 sc0) :
  sim_mem ffrom' fto' acts0 sb0 rmw0 rf0 sc0 mem'.
Proof.
red; ins.
specialize (SIM_MEM l0); desc; splits; ins.
- eapply memory_step_write_dom with (acts:=acts); eauto.
- destruct (classic (l=l0 /\ fto' a = to /\ ffrom' a = from)); desc; subst.
   by eapply memory_step_write_cell_eq with (acts:=acts); eauto.
   eapply memory_step_write_cell_neq with (acts:=acts); eauto.
- eapply memory_step_write_rmw with (acts:=acts) (prev:=a); eauto.
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
  (SIMMSG : sim_msg fto acts sb rmw rf sc b (View.unwrap released_r))
  (FROM': ffrom' a = fto b) 
  (EXpln: Time.le (LocFun.find l (View.pln ((TView.rel tview) l))) (fto' a)) 
  (EXrlx: Time.le (LocFun.find l (View.rlx ((TView.rel tview) l))) (fto' a)) 
  (EXcur_pln: Time.le (LocFun.find l (View.pln (TView.cur tview))) (fto' a))
  (EXcur_rlx: Time.le (LocFun.find l (View.rlx (TView.cur tview))) (fto' a))
  (COH' : Coherent acts0 sb0 rmw0 rf0 mo0 sc0) :
  sim_mem ffrom' fto' acts0 sb0 rmw0 rf0 sc0 mem'.
Proof.
red; ins.
specialize (SIM_MEM l0); desc; splits; ins.
- eapply memory_step_write_dom with (acts:=acts); eauto.
- destruct (classic (l=l0 /\ fto' a = to /\ ffrom' a = from)); desc; subst.
  by eapply memory_step_update_cell_eq with (acts:=acts); eauto.
  eapply memory_step_write_cell_neq with (acts:=acts); eauto.
  eby rewrite FROM'; edone.
- eapply memory_step_write_rmw with (prev:=prev) (acts:=acts); try edone.
  by unfold loc; ins; desf.
  ins; replace b with c; try done.
  eby cdes COH; cdes WF; eapply WF_RF.
Qed.

(******************************************************************************)
(** * Lemmas for the fence step   *)
(******************************************************************************)

Lemma tview_step_scfence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w)
  (SC: is_sc a)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  tview (TVIEW: sim_tview f acts sb rmw rf sc tview (thread a))
  (WF: TView.wf tview) :
  sim_tview f acts0 sb0 rmw0 rf0 sc0 (TView.write_fence_tview
     (TView.read_fence_tview tview o_r) sc_map o_w) (thread a).
Proof.

  assert (X: forall x l', In x acts0 /\ is_write x /\ loc x = Some l' /\
      thread x = thread a -> rfhbsc_opt acts0 sb0 rmw0 rf0 l' x a).
  {
  ins; desc.
  exists x; splits; vauto.
  exists x; splits; vauto.
  destruct (classic (x=a)); vauto.
  right; exists x; splits; vauto; exists a; splits; vauto.
  eapply sb_in_hb; eauto.
  cdes GSTEP; eapply SB_AT_END; eauto.
  rewrite ACT_STEP in H; destruct H; vauto.  }

  assert (FENCE: is_fence a).
    by destruct a; ins; desf.
  assert (NR: ~ is_read a).
    eauto with acts.
  assert (SCFENCE: is_sc_fence a).
    by destruct a; ins; desf.

  assert (SCa: Ordering.le Ordering.seqcst o_w).
     by destruct a; ins; desf.
  assert (SCa': Ordering.le Ordering.seqcst o_w <-> is_sc_fence a).
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
           (LocFun.find l (TimeMap.join sc_map (View.rlx acq)))).
    cdes TVIEW; cdes ACQ0; ins. 
    ins; rewrite !tm_find_join.
    ins; eapply max_value_join; [eapply SIM_SC_MAP| |]; eauto.
    intro; rewrite gstep_S_tm_scfence; eauto. split; ins; desf; 
    eauto using inclusion_refl2 with rel_mon.

  unfold sim_tview, sim_acq, sim_cur, sim_rel; splits; ins; desf.

  all: try rewrite TimeMap.le_join_r with (r := TimeMap.join _ _).
  all: try eapply max_value_same_set; try apply K; 
       eauto using gstep_t_cur_urr_scfence,
       gstep_t_cur_rwr_scfence,
       gstep_t_acq_urr_scfence,
       gstep_t_acq_rwr_scfence.
  by etransitivity; [|by apply TimeMap.join_r]; vauto; destruct ACQ; eauto.
  by etransitivity; [|by apply TimeMap.join_r]; vauto; destruct ACQ; eauto.
  1: ins; rewrite gstep_t_rel_urr_scfence; eauto.
  2: ins; rewrite gstep_t_rel_rwr_scfence; eauto.
  all: split; ins; desf; auto; exists a, a; split; vauto; eauto.
} 
{
  assert (K: forall l, 
          max_value f (S_tm acts0 sb0 rmw0 rf0 l)
           (LocFun.find l (TimeMap.join sc_map (View.rlx cur)))).
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
     gstep_t_acq_urr_scfence,
     gstep_t_acq_rwr_scfence,
     gstep_t_rel_urr_scfence,
     gstep_t_rel_rwr_scfence.
  all: intro.
  all: try rewrite (gstep_t_acq_urr_nonread COH GSTEP NR), or_comm.
  all: try rewrite (gstep_t_acq_rwr_nonread COH GSTEP NR), or_comm.
  all: try by apply or_more; ins;
     eauto using gstep_t_cur_urr_scfence,
     gstep_t_cur_rwr_scfence.
  1: ins; rewrite gstep_t_rel_urr_scfence; eauto.
  2: ins; rewrite gstep_t_rel_rwr_scfence; eauto.
  all: split; ins; desf; auto; exists a, a; split; vauto; eauto.
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

assert (X1: forall x, In x acts0 /\ is_write x -> In x acts).
{ ins; cdes GSTEP; rewrite ACT_STEP in H; destruct H; vauto.
destruct x as [??[]]; ins. }

assert (X2: forall x, In x acts -> In x acts0).
{ ins; eapply act_mon; vauto. }

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
  all: try rewrite (gstep_t_cur_urr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_cur_rwr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_rel_urr_rafence COH GSTEP FENCE).
  all: try rewrite (gstep_t_rel_rwr_rafence COH GSTEP FENCE).
  all: ins.

  all: try (split; ins; desf; eauto 4).
  all: try by exfalso; eauto.
  all: eauto using inclusion_refl2 with rel_mon.
  all: eauto 10 using inclusion_refl2 with rel_mon.
  all: exists x, x; split; try apply ur_in_rw; try apply urr_refl; 
        eauto; try exists x; splits; vauto.
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
  assert (SCa': Ordering.le Ordering.seqcst o_w <-> is_sc_fence a).
    by rewrite SCa; eauto 7 with acts.
  assert (RAa: Ordering.le Ordering.acqrel o_r <-> is_acq a).
    by destruct a; ins; desf.
  assert (RAr: Ordering.le Ordering.acqrel o_w <-> is_rel a).
    by destruct a; ins; desf.
  assert(F : is_fence a).
    by eauto with acts.
  assert(Fsc : is_fence a /\ is_sc a <-> is_sc_fence a).
    by split; destruct a; ins; desf.

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
   intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf;
    eauto using inclusion_refl2 with rel_mon.
  by intro; rewrite gstep_S_tm_scfence; eauto; split; ins; desf;
    eauto using inclusion_refl2 with rel_mon; exfalso; eauto.
   intro; eapply gstep_S_tm_other; eauto.
Qed.
