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
Require Import Commit.

Require Import Gevents.
Require Import model.
Require Import Gstep GstepRead GstepWrite GstepFence GstepOther.
Require Import Machine.
Require Import SimRel.

Set Implicit Arguments.
Remove Hints plus_n_O.

Require Import Setoid Permutation.

Hint Resolve gstep_wf gstep_inc coh_wf.

Lemma foo (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof. tauto. Qed.


Lemma get_cell :
  forall f acts sb rmw rf mo sc mem 
    (MONOTONE: monotone mo f) (WF: WfMO acts mo)
    (MEM : sim_mem f acts sb rmw rf sc mem) a rf0 l v o
    (LAB' : lab a = Aload l v o) 
    (WF_RF : WfRF (a :: acts) rf0)
     b (RFba : rf0 b a) (INb : In b acts)
     o_b (Lb : lab b = Astore l v o_b),
  exists from rel, Memory.get l (f b) mem = Some (from, Message.mk v rel) /\
                  (sim_mem_helper f acts sb rmw rf sc b from v rel).
Proof.
  ins; desc.
  assert (X:= proj1 (MEM l) b).
  destruct (Memory.get l (f b) mem) as [[from [v' rel]]|] eqn:Y; cycle 1.
  - exfalso; apply X; try done.
    unfold is_write, loc; rewrite Lb in *; done.
  - apply (proj2 (MEM l)) in Y; desc.
destruct (classic (b0=b)); subst.
* assert (v'=v).
      red in Y3; desc; desc; ins.
      unfold val in *; rewrite Lb in *; ins; congruence.
  subst.
  eauto; reflexivity.
* exfalso. 
eapply monotone_injective in H; eauto with acts.
unfold loc; destruct (lab b); ins; desf.
Qed.

Lemma sim_commit_other_threads_silent acts sb rmw rf mo sc
  (COH: Coherent acts sb rmw rf mo sc) f f' i commit
  (LOCAL: sim_commit f acts sb rmw rf sc commit i)
  (F: forall a, (In a acts) -> f' a = f a) :
    sim_commit f' acts sb rmw rf sc commit i.
Proof.
unfold sim_commit, sim_cur, sim_acq, sim_rel in *; desf; splits; ins.
all: eapply max_value_new_f; eauto.
all: ins; apply F; eauto with acts.
Qed.

Lemma sim_commit_other_threads acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f f' i (NEQ: i <> thread a) commit 
  (LOCAL: sim_commit f acts sb rmw rf sc commit i)
  (F: forall a, (In a acts) -> f' a = f a) :
    sim_commit f' acts' sb' rmw' rf' sc' commit i.
Proof.
unfold sim_commit, sim_cur, sim_acq, sim_rel in *; desf; splits; ins.
all: eapply max_value_same_set.
all: try match goal with
       | [|- max_value _ _ _] => eapply max_value_new_f with (f:=f); eauto with acts
     end.
all: ins; try eapply gstep_t_cur_other;  
     try eapply gstep_t_acq_other;  
     try eapply gstep_t_rel_other;  
     eauto 2 using gstep_urr_a, gstep_rwr_a, gstep_scr_a, urr_mon, rwr_mon, scr_mon.
Qed.

Lemma gstep_tm_to_a acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  tm l 
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' l ;; hb acts' sb' rmw' rf') (tm acts' sb' rmw' rf' sc' l))
  (TM_MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc l x y -> In y acts)
   x (CUR: t_cur tm acts sb rmw rf sc (thread a) l x) :
   tm acts' sb' rmw' rf' sc' l x a.
Proof.
red in CUR; red in CUR; desc.
red in CUR; desc.
unfold seq, eqv_rel in *.
desc; subst.
apply TM_HB; exists y; split.
apply TM_MON; done.
apply sb_in_hb; eapply gstep_sb; eauto.
right; red; repeat (eexists; splits; eauto).
Qed.

(******************************************************************************)
(** * Lemmas for the read step   *)
(******************************************************************************)

Lemma Readable_cur_tm acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  tm (CUR: max_value f (t_cur tm acts sb rmw rf sc (thread a) l) t) 
  (WRITE : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> is_write x)
  (ACTS : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> In x acts)
  (COHERENT: forall c, mo' b c -> tm acts' sb' rmw' rf' sc' l c a -> False)
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' l ;; hb acts' sb' rmw' rf') 
                    (tm acts' sb' rmw' rf' sc' l))
  (TM_MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l))
  (TM_DOMa: doma (tm acts sb rmw rf sc l) (fun e => loc e = Some l))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc l x y -> In y acts)
  (RFb: rf' b a) : Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in CUR; desf.
apply Time.bot_spec.
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP; desf. 
eapply monotone_converse with (acts:=(a :: acts)); ins; eauto using rf_acta, rf_doma.
- by eapply rf_acta in RFb; try eassumption.
- eapply rf_doma in RFb; eauto.
- by destruct INam; desc; pattern a_max; eapply c_cur_doma; eauto.
- by eapply loceq_rf in RFb; eauto; unfold loc in *; rewrite LABa in RFb.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  cdes WF'; eauto.
- intro.
  eapply COHERENT; eauto.
  eapply gstep_non_write_mo with (acts:=acts) (mo:=mo); eauto.
  eapply gstep_tm_to_a; eauto.
Qed.

Lemma Readable_msg_sc acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) t)
  (RFb: rf' b a) (SC: is_sc a): Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in MSG; desf.
apply Time.bot_spec.
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP. 
eapply monotone_converse with (acts:=(a :: acts)); eauto.
- right; eapply acta_msg_scr; eauto.
- eapply rf_acta in RFb; eauto. rewrite <- ACT_STEP; eauto.
- eauto with rel.
- eapply rf_doma in RFb; eauto.
- eauto with rel.
- eapply loceq_rf in RFb; eauto. unfold loc in *. rewrite LABa in RFb. auto.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  rewrite <- ACT_STEP.
  cdes WF'; eauto.
- intro.
admit.
(*  eapply Coherent_scr_rel; eauto.
  eapply gstep_non_write_mo with (mo:=mo); eauto.
  eapply gstep_scr_rel_nonwrite with (acts:=acts); eauto.
  unfold scr_rel, msg_rel, m_rel, seq, eqv_rel in *; desc; subst.
  eauto.
*)
Admitted.

Lemma Readable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  commit rel
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) (Capability.sc rel l))
  (CUR: sim_cur f acts sb rmw rf sc (Commit.cur commit) (thread a))
  (RFb: rf' b a): 
    Commit.readable commit l (f b) rel o.
Proof.
red in CUR; desc.
constructor; try intro.
-  eapply Readable_cur_tm; eauto using Coherent_urr, urr_hb, urr_mon with rel acts.
   by eapply urr_actb; eauto.
- eapply Readable_cur_tm; eauto using rwr_hb, rwr_mon with rel acts.
  ins; eapply Coherent_rwr with (mo:=mo'); eauto.
  right; splits; eauto with acts.
  eapply rwr_actb; eauto.
- eapply Readable_cur_tm; eauto using scr_hb, scr_mon with rel acts.
  ins; eapply Coherent_scr with (mo:=mo');  eauto with acts.
  eapply scr_actb; eauto.
- eapply Readable_msg_sc; eauto with acts.
Qed.

Lemma commit_step_read acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a l v o (LABa : lab a = Aload l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  b o_b (INb : In b acts) (RFb : rf0 b a) (LABb : lab b = Astore l v o_b)
  rel (SIM_MSG: sim_msg f acts sb rmw rf sc b rel)
  commit (COMMIT: sim_commit f acts sb rmw rf sc commit (thread a)):
  sim_commit f acts0 sb0 rmw0 rf0 sc0 (Commit.read_commit commit l (f b) rel o) (thread a).
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

destruct commit; simpl.
red in COMMIT; desc; red in CUR; red in ACQ; red in REL; desc.
red in SIM_MSG; desc.
unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins.

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
  f (MONOTONE : monotone mo f)
  prev a (NW: ~ is_write a) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem (SIM_MEM : sim_mem f acts sb rmw rf sc mem):
  sim_mem f acts0 sb0 rmw0 rf0 sc0 mem.
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
  eapply gstep_rf_rmw with (rf:=rf) in RF_RMW; eauto.
Qed.

(******************************************************************************)
(** * Lemmas for the write step   *)
(******************************************************************************)

Lemma Writable_cur_rwr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l) t) 
   : Time.lt t (f' a).
Proof.
red in CUR; desf.
admit.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts. 
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP.
  cdes WF'; eauto.
- intro.
  eapply Coherent_rwr; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply rwr_hb.
  eapply rwr_mon; eauto.
  eapply rwr_actb; eauto.
- intro; subst; eauto with acts. 
Admitted.

Lemma Writable_cur_scr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l) t) 
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in CUR; desf.
admit.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts. 
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP; cdes WF'; eauto.
- intro.
  eapply Coherent_scr; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply scr_hb.
  eapply scr_mon; eauto.
  eapply scr_actb; eauto.
- intro; subst; eauto with acts. 
Admitted.

Lemma Writable_sc_map acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (SCMAP: max_value f (S_tm acts sb rmw rf l) t)
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in SCMAP; desf.
admit.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts. 
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP; cdes WF'; eauto.
- intro.
  eapply Coherent_scr; eauto.
  red in INam; red in INam; desc.
  eapply S_tm_sc with (b:=y); eauto with acts.
  eapply S_tmr_mon; eauto.
  apply SC_AT_END; eauto.
  apply S_tmr_domb in INam; done.
  - intro; subst; eauto with acts. 
Admitted.

Lemma Writable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f')
  l v o (LABa: lab a = Astore l v o)
  commit sc_map
  (SC : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (sc_map l))
  (CUR: sim_cur f acts sb rmw rf sc (Commit.cur commit) (thread a)):
  Commit.writable commit sc_map l (f' a) o.
Proof.
red in CUR; desc.
constructor; try intro.
eapply Writable_cur_rwr; eauto.
eapply Writable_cur_scr; eauto with acts.
eapply Writable_sc_map; eauto with acts.
Qed.

Lemma commit_step_write acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  prev a l v o (LABa : lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  commit (COMMIT: sim_commit f acts sb rmw rf sc commit (thread a))
  f' (F : forall b, In b acts -> f' b = f b)
  (MON : monotone mo0 f'):
  sim_commit f' acts0 sb0 rmw0 rf0 sc0 (Commit.write_commit commit sc_map l (f' a) o) (thread a).
Proof.

assert (WRITE: is_write a).
  eauto with acts.
assert (NR: ~ is_read a).
  eauto with acts.

assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.

assert (LOC_A: Gevents.loc a = Some l). 
  by unfold Gevents.loc; destruct (lab a); ins; desf.

destruct commit; simpl.
red in COMMIT; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins.

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
  all: split; ins; desf; eauto 3.
  all: try by exfalso; eauto.
  all: eauto 10 with rel.
  all: eauto using inclusion_refl2 with rel_mon.
  by exploit RAa0; try done; destruct a as [??[]]; ins; destruct o0; ins.
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
     (LocFun.find l0 (Commit.write_sc sc_map l (f' a) o)).
Proof.
assert (WRITE: is_write a).
  eauto with acts.
assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
    ins.
    unfold Commit.write_sc; desf; ins.
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


Lemma memory_exists  acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem (CLOSED: Memory.closed mem)
  from commit:
exists mem', Memory.write Memory.bot mem l from (f' a) v 
  (if Ordering.le Ordering.relaxed o
   then
    Capability.join Capability.bot
      (Commit.rel (Commit.write_commit commit sc_map l (f' a) o) l)
   else Capability.bot)  Memory.bot mem' Memory.promise_kind_add .
Proof.
Admitted.
(* more assumptions are needed *)

Lemma memory_write0 mem mem' l from t v rel l0 t0
  (ADD: Memory.write Memory.bot mem l from t v rel Memory.bot mem' Memory.promise_kind_add)
  from0 m (NEW: Memory.get l0 t0 mem = Some (from0, m)):
  Memory.get l0 t0 mem' = Some (from0, m).
Proof.
Admitted.

Lemma memory_write1 mem mem' l from t v rel 
  (ADD: Memory.write Memory.bot mem l from t v rel Memory.bot mem' Memory.promise_kind_add)
  l0 t0 from0 m
  (NEW: Memory.get l0 t0 mem' = Some (from0, m)) (NEQ: l <> l0 \/ t <> t0):
  Memory.get l0 t0 mem = Some (from0, m).
Proof.
Admitted.


Lemma memory_step_write_dom acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem mem' (CLOSED: Memory.closed mem)
  l0 b (DOM : In b acts /\ is_write b /\ loc b = Some l0 -> Memory.get l0 (f b) mem <> None)
  from rel 
  (ADD: Memory.write Memory.bot mem l from (f' a) v rel Memory.bot mem' Memory.promise_kind_add):
  In b acts0 /\ is_write b /\ loc b = Some l0 -> Memory.get l0 (f' b) mem' <> None.
Proof.
ins; red in GSTEP; desc.
rewrite ACT_STEP in H; ins; desf; subst.
- assert (l = l0).
    unfold loc, lab in *; destruct b; destruct lb; desf.
  subst.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  intro; desf.
  destruct CLOSED; done.
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
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem mem' 
  from rel 
  (ADD: Memory.write Memory.bot mem l from (f' a) v rel Memory.bot mem' Memory.promise_kind_add)
  l0 b c (RF_RMW: (rf0;; rmw0) b c) (LOC: loc b = Some l0)
  (UPDATES: forall a b (RF_RMW: (rf ;; rmw) a b) (LOC: loc a = Some l0),
                exists m, Memory.get l0 (f b) mem = Some ((f a), m)):
  exists m : Message.t, Memory.get l0 (f' c) mem' = Some (f' b, m).
Proof.
eapply gstep_rf_rmw with (rf:=rf) in RF_RMW; eauto.
specialize (UPDATES b c RF_RMW LOC).
desc.
exists m.
rewrite !F; eauto.
eapply memory_write0 in UPDATES; eauto.
unfold seq in RF_RMW; desc; eapply rf_acta; eauto.
unfold seq in RF_RMW; desc; eapply rmw_actb; eauto.
Qed.



Lemma memory_step_write_cell acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 
  (COH : Coherent acts sb rmw rf mo sc) 
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  l0 to from0 v0 rel0 mem (CLOSED: Memory.closed mem)
  (SIMCELL : forall to from v rel, Memory.get l0 to mem = Some (from, Message.mk v rel) ->
          exists b, In b acts /\ is_write b /\ loc b = Some l0 /\ f b = to /\ 
                    sim_mem_helper f acts sb rmw rf sc b from v rel)
  sc_map (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  commit (SIM_COMMIT : sim_commit f acts sb rmw rf sc commit (thread a))
  from (FROM: Time.lt from (f' a))
  mem' (ADD: Memory.write Memory.bot mem l from (f' a) v 
          (if Ordering.le Ordering.relaxed o then 
          (Commit.rel (Commit.write_commit commit sc_map l (f' a) o) l) else Capability.bot)
     Memory.bot mem' Memory.promise_kind_add)
  (GET: Memory.get l0 to mem' = Some (from0, Message.mk v0 rel0)):
  exists b, In b acts0 /\ is_write b /\ loc b = Some l0 /\
    f' b = to /\ sim_mem_helper f' acts0 sb0 rmw0 rf0 sc0 b from0 v0 rel0.
Proof.
destruct (classic (l=l0 /\ f' a = to)).
- desc; subst.
  exists a; splits; eauto with acts.
  by red in GSTEP; desc; rewrite ACT_STEP; vauto.
  by unfold loc; destruct (lab a); ins; desf.
  apply Memory.write_get2 in ADD; eauto using Memory.bot_le.
  2: destruct CLOSED; done. 


ins.

assert(LocFun.add l0 (if Ordering.le Ordering.acqrel o
then Capability.join (Capability.join (Commit.cur commit)
 (Capability.singleton_ur l0 (f' a)))
(if Ordering.le Ordering.seqcst o
then
{|
Capability.ur := TimeMap.bot;
Capability.rw := TimeMap.bot;
Capability.sc := sc_map |}
else Capability.bot)
else Commit.rel commit l0) 
(Commit.rel commit) l0=
LocFun.find l0 (LocFun.add l0
(if Ordering.le Ordering.acqrel o
then
Capability.join
(Capability.join (Commit.cur commit)
 (Capability.singleton_ur l0 (f' a)))
(if Ordering.le Ordering.seqcst o
then
{|
Capability.ur := TimeMap.bot;
Capability.rw := TimeMap.bot;
Capability.sc := sc_map |}
else Capability.bot)
else Commit.rel commit l0) 
(Commit.rel commit))).  done.
rewrite H in ADD. clear H.

unfold Commit.write_commit in ADD; ins.

destruct commit; simpl.
red in SIM_COMMIT; desc; red in CUR; red in ACQ; red in REL; desc.
unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins.

assert (SCa: Ordering.le Ordering.seqcst o <-> is_sc a).
  by destruct a; ins; desf.
assert (RAa: Ordering.le Ordering.acqrel o <-> is_rel a).
  by destruct a; ins; desf.
assert (LOC_A: Gevents.loc a = Some l0). 
  by unfold Gevents.loc; destruct (lab a); ins; desf.
assert (W: is_write a). 
  by destruct a as [??[]]; ins.

desf; clear ADD; red; splits; eauto.
all: try by unfold val, lab in *; destruct a; destruct lb; desf.
all: unfold sim_msg; splits; ins.


all: try rewrite LocFun.add_spec; desf.
all: ins.
all: try rewrite !tm_join_bot.
all: try rewrite !tm_find_join.
all: try rewrite !tm_find_singleton; desf.
all: try rewrite !time_join_bot.
all: try rewrite tm_find_bot.
all: do 2 (try match goal with
| [|- max_value _ _ (Time.join _ _)] => eapply max_value_join  end).
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
all: eauto 8.
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

admit.
all: try by destruct o; ins; desf; eauto.
admit.
admit.
admit.
- assert (OLD: Memory.get l0 to mem = Some (from0, Message.mk v0 rel0)).
    eapply memory_write1; try edone; tauto.
  assert (LOC_A: Gevents.loc a = Some l). 
    by unfold Gevents.loc; destruct (lab a); ins; desf.
  assert (W: is_write a). 
    by destruct a as [??[]]; ins.
  clear GET ADD.
  specialize (SIMCELL to from0 v0 rel0 OLD); desc.
  exists b.
  unfold sim_mem_helper in *; desc; splits; try rewrite F; eauto.
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
Admitted.

Lemma memory_step_write acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f f' (F : forall b, In b acts -> f' b = f b) (MON: monotone mo0 f')
  prev a l v o (LABa: lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  mem (SIM_MEM : sim_mem f acts sb rmw rf sc mem) (CLOSED: Memory.closed mem)
  from (FROM: Time.lt from (f' a))  
  sc_map (SIM_SC_MAP : forall l, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  commit (SIM_COMMIT : sim_commit f acts sb rmw rf sc commit (thread a))
  mem' (ADD: Memory.write Memory.bot mem l from (f' a) v 
  (if Ordering.le Ordering.relaxed o then 
      (Commit.rel (Commit.write_commit commit sc_map l (f' a) o) l) else Capability.bot)
 Memory.bot mem' Memory.promise_kind_add):
  sim_mem f' acts0 sb0 rmw0 rf0 sc0 mem'.
Proof.
red; ins.
specialize (SIM_MEM l0); desc.
splits; ins.
eapply memory_step_write_dom; eauto.
eapply memory_step_write_cell; eauto.
eapply memory_step_write_rmw; eauto.
Qed.

(******************************************************************************)
(** * Lemmas for the fence step   *)
(******************************************************************************)

Lemma commit_step_scfence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w)
  (SC: is_sc a)
  (ACQ: is_acq a)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  commit (COMMIT: sim_commit f acts sb rmw rf sc commit (thread a)):
  sim_commit f acts0 sb0 rmw0 rf0 sc0 (Commit.write_fence_commit
     (Commit.read_fence_commit commit o_r) sc_map o_w) (thread a).
Proof.
  assert (FENCE: is_fence a).
    by destruct a; ins; desf.
  assert (NR: ~ is_read a).
    eauto with acts.

  assert (SCa: Ordering.le Ordering.seqcst o_w).
     by destruct a; ins; desf.
  assert (RAa: Ordering.le Ordering.acqrel o_r).
     by destruct a; ins; desf.
  assert (RAr: Ordering.le Ordering.acqrel o_w).
     by destruct a; ins; desf; destruct o_w.

  destruct commit; simpl.
  unfold Commit.write_fence_commit, Commit.read_fence_commit,
         Commit.write_fence_sc.
  simpl; rewrite SCa, RAa, RAr.

  assert (K: forall l, 
          max_value f (S_tm acts0 sb0 rmw0 rf0 l)
           (LocFun.find l (TimeMap.join sc_map (Capability.sc acq)))).
    cdes COMMIT; cdes ACQ0; ins. 
    ins; rewrite !tm_find_join.
    ins; eapply max_value_join; [eapply SIM_SC_MAP| |]; eauto.
    by eapply gstep_S_tm_scfence; eauto.

  unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins; desf.

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
admit.
admit.
Admitted.


Lemma commit_step_rafence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w) (NSC: ~ is_sc a)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a a)
  commit (COMMIT: sim_commit f acts sb rmw rf sc commit (thread a)):
  sim_commit f acts0 sb0 rmw0 rf0 sc0 (Commit.write_fence_commit
     (Commit.read_fence_commit commit o_r) sc_map o_w) (thread a).
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

  destruct commit; simpl.
  unfold Commit.write_fence_commit, Commit.read_fence_commit,
         Commit.write_fence_sc.

  red in COMMIT; desc; red in CUR; red in ACQ; red in REL; desc.
  unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins; desf.

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

(******************************************************************************)
(** * Main Theorem: the operational machine simulates the axiomatic machine   *)
(******************************************************************************)

Definition proof_obligation ax_st ax_st' op_st i lang st st' :=
  forall
   (COH : Coherent (acts ax_st) (sb ax_st) (rmw ax_st) 
          (rf ax_st) (mo ax_st) (sc ax_st))
   (WF_OP_ST : Configuration.wf op_st)
   (CONS_OP_ST : Configuration.consistent op_st)
   (STATES : ts ax_st = IdentMap.map fst (Configuration.threads op_st))
   f (TIME : sim_time op_st ax_st f) commit
   (COMMIT : sim_commit f (acts ax_st) (sb ax_st) (rmw ax_st) 
          (rf ax_st) (sc ax_st) commit i),
  exists te commit' sc' mem' op_st' threads' local', 
    << OP_ST': op_st' = Configuration.mk threads' sc' mem' >> /\ 
    << THREAD': threads' = IdentMap.add i (existT Language.state lang st', local') 
                                          (Configuration.threads op_st) >> /\ 
    << LOCAL': local' = Local.mk commit' Memory.bot >> /\ 
    << STEP: Thread.program_step te 
                    (Thread.mk lang st (Local.mk commit Memory.bot) 
                               (Configuration.sc op_st) (Configuration.memory op_st))
                    (Thread.mk lang st' local' sc' mem') >> /\
    exists f', 
      << F: forall b, In b (acts ax_st) -> f' b = f b >> /\
      << MONOTONE: monotone (mo ax_st') f' >> /\  
      << SIM_COMMIT: sim_commit f' (acts ax_st') (sb ax_st') (rmw ax_st') 
                                (rf ax_st') (sc ax_st') commit' i >> /\
      << SIM_SC_MAP: forall l, max_value f' (S_tm (acts ax_st') (sb ax_st') (rmw ax_st') 
                                                  (rf ax_st') l) 
                                         (LocFun.find l sc')  >> /\
      << SIM_MEM: sim_mem f' (acts ax_st') (sb ax_st') (rmw ax_st') 
                          (rf ax_st') (sc ax_st') mem'  >>.


Lemma ax_op_sim_step_read :
  forall op_st ax_st ax_st'
         a l v o (LABa : lab a = Aload l v o)
   (GSTEP : gstep (acts ax_st) (sb ax_st) (rmw ax_st) 
            (rf ax_st) (mo ax_st) (sc ax_st) (acts ax_st') 
            (sb ax_st') (rmw ax_st') (rf ax_st') (mo ax_st') 
            (sc ax_st') a a)
   (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
           (rf ax_st') (mo ax_st') (sc ax_st')) 
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.read l v o)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; desc. 
  destruct ax_st, ax_st'; simpl; ins.

generalize (gstep_read_rf COH GSTEP LABa); intro; desc.

assert (E: exists from rel, Memory.get l (f b) (Configuration.memory op_st) = 
          Some (from, Message.mk v rel) /\ sim_mem_helper f acts sb rmw rf sc b from v rel).
  cdes COH; cdes WF.
  cdes COH'; cdes WF0.
  eapply get_cell with (acts:=acts) (mo:=mo); try edone. 
  cdes GSTEP; rewrite <- ACT_STEP; try edone.

desc; red in E0; desc.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.
assert (LOC_B: Gevents.loc b = Some l). 
  unfold Gevents.loc; destruct (lab b); ins; desf.

eexists _,_,_,_,_,_,_.
splits; eauto.
- eapply Thread.step_read; eauto.
  econstructor; eauto.
  red in COMMIT; red in SIMMSG; desc.
  eapply Readable_full; eauto. 
- exists f; splits; eauto.
  * rewrite <- gstep_non_write_mo; eauto with acts.
  * eapply commit_step_read with (acts := acts) (acts0 := acts0); eauto.
  * ins. eapply max_value_same_set; try edone.
    ins; rewrite gstep_S_tm_other; eauto with acts.
  * eapply memory_step_nonwrite with (acts := acts) (acts0 := acts0); eauto with acts.
Qed.

Lemma ax_op_sim_step_write :
  forall op_st ax_st ax_st'
         a l v o (LABa : lab a = Astore l v o)
   (GSTEP : gstep (acts ax_st) (sb ax_st) (rmw ax_st) 
            (rf ax_st) (mo ax_st) (sc ax_st) (acts ax_st') 
            (sb ax_st') (rmw ax_st') (rf ax_st') (mo ax_st') 
            (sc ax_st') a a)
   (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
           (rf ax_st') (mo ax_st') (sc ax_st')) 
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.write l v o)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; ins; desc.
  destruct ax_st, ax_st'; simpl; ins.

  generalize (new_f GSTEP MONOTONE); intro; desc.

  generalize (new_from f' a); intro; desc.


assert (exists mem', Memory.write Memory.bot
  (Configuration.memory op_st) l from (f' a) v
  (if Ordering.le Ordering.relaxed o
   then
    Capability.join Capability.bot
      (Commit.rel
         (Commit.write_commit
            (Local.commit {| Local.commit := commit; Local.promises := Memory.bot |})
            (Configuration.sc op_st) l (f' a) o) l)
   else Capability.bot)
 Memory.bot mem' Memory.promise_kind_add).
eapply memory_exists; try edone.
destruct WF_OP_ST; done.

desc.
  eexists _,_,_,mem',_,_,_; splits; eauto.
  - eapply Thread.step_write; eauto.
    econstructor; eauto.
    red in COMMIT; desc; eapply Writable_full; eauto.
  - exists f'; splits; try done.
    * eapply commit_step_write; eauto.
    * eapply sc_map_step_write; eauto.
    * eapply memory_step_write; eauto.
      destruct WF_OP_ST; done.
      rewrite Capability.join_comm, cap_join_bot in H1; done.
Qed.

Lemma ax_op_sim_step_update :
  forall op_st ax_st ax_st'
         a_r l v_r o_r (LABar : lab a_r = Aload l v_r o_r)
         a_w v_w o_w (LABaw : lab a_w = Astore l v_w o_w)
         mc_mid
  (GSTEPr : gstep (acts ax_st) (sb ax_st) (rmw ax_st) 
             (rf ax_st) (mo ax_st) (sc ax_st) (acts mc_mid) 
             (sb mc_mid) (rmw mc_mid) (rf mc_mid) 
             (mo mc_mid) (sc mc_mid) a_r a_r)
  (GSTEPw : gstep (acts mc_mid) (sb mc_mid) (rmw mc_mid) 
             (rf mc_mid) (mo mc_mid) (sc mc_mid) (acts ax_st') 
             (sb ax_st') (rmw ax_st') (rf ax_st') 
             (mo ax_st') (sc ax_st') a_r a_w)
  (COHmid : Coherent (acts mc_mid) (sb mc_mid) (rmw mc_mid) 
             (rf mc_mid) (mo mc_mid) (sc mc_mid))
  (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
             (rf ax_st') (mo ax_st') (sc ax_st'))
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.update l v_r v_w o_r o_w)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a_r) lang st st'.
Proof.
Admitted.

Lemma ax_op_sim_step_fence :
  forall op_st ax_st ax_st'
         a o_r o_w (LABa : lab a = Afence o_r o_w)
   (GSTEP : gstep (acts ax_st) (sb ax_st) (rmw ax_st) 
            (rf ax_st) (mo ax_st) (sc ax_st) (acts ax_st') 
            (sb ax_st') (rmw ax_st') (rf ax_st') (mo ax_st') 
            (sc ax_st') a a)
   (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
           (rf ax_st') (mo ax_st') (sc ax_st')) 
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.fence o_r o_w)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; ins; desc.
  destruct ax_st, ax_st'; simpl; ins.

  eexists _,_,_,_,_,_,_; splits; eauto.
  eapply Thread.step_fence; eauto.
  econstructor; eauto.
  exists f; splits; eauto.
  * rewrite <- gstep_non_write_mo; eauto with acts.

  * destruct (classic (is_sc a)); 
      [ eapply commit_step_scfence|eapply commit_step_rafence]; eauto.
admit. (* Assume all SC fences are ACQ *)
  * 
admit.
  * eapply memory_step_nonwrite; eauto with acts.
Admitted.


Lemma ax_op_sim :
  forall op_st ax_st (SIM: sim op_st ax_st) ax_st' (AXSTEP: step ax_st ax_st'),
  exists e tid op_st', Configuration.step e tid op_st op_st' /\ sim op_st' ax_st'.
Proof.
  ins; red in SIM; desc.
  destruct AXSTEP.

  rewrite STATES in TID.
  apply find_mapD in TID; desc; destruct z as [? local]; ins; desf.
  destruct local as [commit promises].
  assert (TID' := TID).
  apply NO_PROMISES in TID'; ins; subst.

  cut (proof_obligation ax_st ax_st' op_st i lang st st').
  {
    intro X; exploit X; eauto; clear X; ins; desc. 
       by eapply TIME; eauto.
    eexists _,i,_.
    apply foo; [|intro CSTEP].
  -  econstructor; try edone; try apply Thread.step_program; eauto.
     red; ins; eexists; splits; eauto; simpl; desf.
  - red; simpl; splits; eauto.
    * destruct MSTEP; eauto.
      by rewrite <- SAME_ACTS, <- SAME_SB, <- SAME_RMW, <- SAME_RF, <- SAME_MO, <- SAME_SC.
    * eapply Configuration.step_future; eauto.
    * eapply Configuration.step_future; eauto.
    * intro; rewrite IdentMap.gsspec. ins; desf; simpl; eapply NO_PROMISES; eauto.
    * by rewrite IdentMap.map_add; simpl; rewrite MTS, STATES.
    * red in TIME; desc; eexists; red; simpl; splits; eauto; ins.
      rewrite IdentMap.gsspec in TID0; desf; ins; simpl.
      destruct MSTEP; subst.
        rewrite <- SAME_ACTS, <- SAME_SB, <- SAME_RMW, <- SAME_RF, <- SAME_SC.
        eapply sim_commit_other_threads_silent; eauto.
      all: eapply sim_commit_other_threads; eauto 2.
      all: try eapply sim_commit_other_threads; eauto 2.
      all: try intro; subst; eauto.
   }
  clear f TIME.

  destruct MSTEP; ins; subst.
  { (** SILENT **)
    destruct ax_st, ax_st'; ins; desf.
    red; ins; eexists _,_,_,_,_,_,_.
    splits; eauto.
    eapply Thread.step_silent; eauto.
    red in TIME; ins; desc; subst.
    exists f; splits; eauto.
  }
  by eapply ax_op_sim_step_read; eauto.
  by eapply ax_op_sim_step_write; eauto.
  by eapply ax_op_sim_step_update; eauto.
  by eapply ax_op_sim_step_fence; eauto.
Qed.


