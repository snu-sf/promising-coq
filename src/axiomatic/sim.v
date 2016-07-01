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
Require Import Gsteps.
Require Import Machine.

Set Implicit Arguments.
Remove Hints plus_n_O.

Hint Resolve gstep_wf gstep_inc coh_wf.

Lemma foo (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

Section Monotone.

Definition monotone (mo : event -> event -> Prop) f :=
  forall a b, mo a b -> Time.lt (f a) (f b).

Lemma new_f acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  f (MON: monotone mo f): 
  exists f', << F: forall b, In b acts -> f' b = f b >> /\
             << MON: monotone mo' f' >>.
Admitted.

Lemma monotone_converse a b l f acts mo
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (MON: monotone mo f)
  (WF_MO: WfMO acts mo) (NOMO: ~ mo b a): Time.le (f a) (f b).
Proof.
apply Time.le_lteq.
destruct (classic (a=b)) as [|N]; desf; eauto.
eapply WF_MO in N; desf; eauto.
Qed.

Lemma monotone_converse_strict a b l f acts mo
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (MON: monotone mo f)
  (WF_MO: WfMO acts mo) (NOMO: ~ mo b a) (NEQ: a <> b) : Time.lt (f a) (f b).
Proof.
assert (mo a b).
  eapply wf_mo_tot; eauto.
apply MON; done.
Qed.

Definition max_value f (INR : event -> Prop) val :=
 << UB: forall a (INa: INR a), Time.le (f a) val >> /\
 << MAX: exists a_max, << INa: INR a_max >> /\ <<LB': Time.le val (f a_max)>> >>.

End Monotone.

Require Import Setoid Permutation.

Add Parametric Morphism : (monotone) with signature 
  same_relation ==> eq ==> iff as monotone_more.
Proof.
  unfold monotone, same_relation, NW; intuition; eauto. 
Qed.

Section Simulation.

Variable f : event -> Time.t.

Variable acts : list event.  
Variable sb : event -> event -> Prop. 
Variable rmw : event -> event -> Prop. 
Variable rf : event -> event -> Prop. 
Variable mo : event -> event -> Prop. 
Variable sc : event -> event -> Prop. 

Definition sim_msg (m: Message.t) b:=
  << VAL: Some m.(Message.val) = (val b) >> /\
  << UR: forall l, max_value f (fun a => msg_rel urr acts sb rmw rf sc l a b) (LocFun.find l (m.(Message.released)).(Capability.ur)) >> /\
  << RW: forall l, max_value f (fun a => msg_rel rwr acts sb rmw rf sc l a b) (LocFun.find l (m.(Message.released)).(Capability.rw)) >> /\
  << SC: forall l, max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) (LocFun.find l (m.(Message.released)).(Capability.sc)) >>.

Definition sim_cell_helper b from msg :=
  << SIMMSG: sim_msg msg b >> /\ 
  << FROM: Time.lt from (f b) >> /\ 
  << FROMRMW: (forall a (RFRMW: (rf ;; rmw) a b), from = f a) >>.

Definition sim_cell cell l  :=
  << DOM: forall b, (is_write b) /\ (loc b = Some l) <-> Cell.get (f b) cell <> None >> /\
  << SIMCELL: forall b (WRITE: is_write b) (LOC: loc b = Some l) 
                       from msg (CELL: Cell.get (f b) cell = Some (from, msg)),
                sim_cell_helper b from msg >>.

Definition sim_mem (mem: Memory.t) :=
  forall l, sim_cell (mem l) l.

Definition sim_rel rel i :=
  << REL_UR: forall l' l, max_value f (t_rel urr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.ur)) >> /\
  << REL_UR: forall l' l, max_value f (t_rel rwr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.rw)) >> /\
  << REL_UR: forall l' l, max_value f (t_rel scr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.sc)) >>.

Definition sim_cur cur i :=
  << CUR_UR: forall l, max_value f (t_cur urr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.ur)) >> /\
  << CUR_RW: forall l, max_value f (t_cur rwr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.rw)) >> /\
  << CUR_SC: forall l, max_value f (t_cur scr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.sc)) >>.

Definition sim_acq acq i :=
  << ACQ_UR: forall l, max_value f (t_acq urr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.ur)) >> /\
  << ACQ_RW: forall l, max_value f (t_acq rwr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.rw)) >> /\
  << ACQ_SC: forall l, max_value f (t_acq scr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.sc)) >>.

Definition sim_commit commit i :=
  << CUR: sim_cur commit.(Commit.cur) i >> /\
  << ACQ: sim_acq commit.(Commit.acq) i >> /\
  << REL: sim_rel commit.(Commit.rel) i >>.

End Simulation.

Definition sim_time  (op_st: Configuration.t) (ax_st: Machine.configuration) f :=
  << MONOTONE: monotone (mo ax_st) f >> /\  
  << SIM_COMMIT: forall i foo local
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
        sim_commit f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) 
                   local.(Local.commit) i >> /\
  << SIM_SC_MAP: forall l, max_value f (S_tm (acts ax_st) (sb ax_st) (rmw ax_st) 
                                             (rf ax_st) l) 
                                     (LocFun.find l (Configuration.sc op_st))  >> /\
  << SIM_MEM: sim_mem f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) 
                      (Configuration.memory op_st) >>.

Definition sim (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << COH: Coherent (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (mo ax_st) (sc ax_st) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << CONS_OP_ST: Configuration.consistent op_st >> /\
  << NO_PROMISES: forall i foo local 
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: ts ax_st = IdentMap.map fst (Configuration.threads op_st) >> /\
  exists f, << TIME : sim_time op_st ax_st f >>. 

Lemma find_mapD A B tid (f: A -> B) x y :
  IdentMap.find tid (IdentMap.map f x) = Some y ->
  exists z, IdentMap.find tid x = Some z /\ y = f z.
Proof.
  rewrite IdentMap.Facts.map_o; unfold option_map; ins; desf; eauto.
Qed.

Lemma get_cell :
  forall f acts sb rmw rf sc mem 
    (MEM : sim_mem f acts sb rmw rf sc mem) a rf0 l v o
    (LAB' : lab a = Aload l v o) 
    (WF_RF : WfRF (a :: acts) rf0)
     b (RFba : rf0 b a) (INb : In b acts)
     o_b (Lb : lab b = Astore l v o_b),
  exists from rel,
    Cell.get (f b) (mem l) = Some (from, {| Message.val:=v; Message.released:=rel |}).
Proof.
  ins; desc.
  assert (X:= proj1 (MEM l) b).
  destruct (Cell.get (f b) (mem l)) as [[from [v' rel]]|] eqn:Y; cycle 1.
  - exfalso; apply X; try done.
    unfold is_write, loc; rewrite Lb in *; done.
  - assert (v'=v).
      apply (proj2 (MEM l)) in Y; try (unfold is_write, loc; rewrite Lb in *; done).
      red in Y; desc; red in SIMMSG; desc; ins.
      unfold val in *; rewrite Lb in *; ins; congruence.
  subst.
  eauto; reflexivity.
Qed.

Lemma tm_join a b l :
  TimeMap.join a b l =  Time.join (a l) (b l).
Proof.  ins. Qed.

Lemma tm_find_join l a b :
  LocFun.find l (TimeMap.join a b) = 
  Time.join (LocFun.find l a) (LocFun.find l b).
Proof.
  done. 
Qed.

Lemma tm_find_singleton l l' t  :
  LocFun.find l (TimeMap.singleton l' t) = 
    if (Loc.eq_dec l l') then t else Time.bot.
Proof.
  desf.
Qed.

Lemma tm_singleton l t : TimeMap.singleton l t l = t.
Proof.
  apply Loc.eq_dec_eq; done.
Qed.

Lemma time_join_bot a : Time.join a Time.bot =  a.
Proof.
Admitted.

Lemma tm_join_bot a  :
  TimeMap.join a TimeMap.bot =  a.
Proof.
eapply TimeMap.antisym.
apply TimeMap.join_spec.
apply TimeMap.le_PreOrder.
apply TimeMap.bot_spec.
apply TimeMap.join_l.
Qed.

Lemma cap_join_bot a  :
  Capability.join a Capability.bot =  a.
Proof.
eapply Capability.antisym.
apply Capability.join_spec.
apply Capability.le_PreOrder.
apply Capability.bot_spec.
apply Capability.join_l.
Qed.

Lemma max_value_singleton f b t (T: t = f b):
  max_value f (eq b) t.
Proof.
red; splits; ins; desc; subst.
by apply Time.le_lteq; eauto.
exists b; splits; try apply Time.le_lteq; eauto.
Qed.

Lemma max_value_new_f f f' P t 
  (MAX: max_value f P t) (F: forall x, P x -> f' x = f x):
  max_value f' P t.
Proof.
unfold max_value in *; ins; desf; splits; ins.
rewrite F; auto.
exists a_max; rewrite F; auto.
Qed.

Lemma max_value_same_set f P P' t 
  (MAX: max_value f P t) (SAME: forall x, P' x <-> P x):   
  max_value f P' t.
Proof.
  unfold max_value in *; ins; desf; splits; ins.
  specialize (SAME a); desf; eauto.
  exists a_max; specialize (SAME a_max); desf; split; auto.
Qed.

Lemma max_value_join f P P' P'' t t'
  (MAX: max_value f P t) (MAX':  max_value f P' t')
  (SAME: forall x, P'' x <-> P x \/ P' x):
  max_value f P'' (Time.join t t').
Proof.
unfold max_value in *; ins; desf; splits; ins.
apply SAME in INa1; desf.
all: try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
destruct (Time.le_lt_dec (f a_max) (f a_max0)); [exists a_max0|exists a_max]; splits.
all: try rewrite SAME; eauto.
all: try (apply Time.join_spec; eauto;
       etransitivity; eauto; rewrite Time.le_lteq; eauto). 
Qed.

Lemma max_value_loc f f' P P' t b
  (MAX: max_value f P t)
  (SAME: forall x, P' x <-> P x \/ x = b)
  (F: forall x, P x -> f' x = f x):
  max_value f' P'  (Time.join t (f' b)).
Proof.
eapply max_value_join with (P':= eq b); eauto.
eapply max_value_new_f with (f:=f); eauto.
eapply max_value_singleton; done.
ins; specialize (SAME x); desf; split; ins.
apply SAME in H; desf; eauto.
apply SAME0; desf; eauto.
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
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
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
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
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
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
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
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP; desf. 
eapply monotone_converse with (acts:=(a :: acts)); ins; eauto using rf_acta, rf_doma.
- by eapply rf_acta in RFb; try eassumption.
- eapply rf_doma in RFb; eauto.
- by destruct INa; desc; pattern a_max; eapply c_cur_doma; eauto.
- by eapply loceq_rf in RFb; eauto; unfold loc in *; rewrite LABa in RFb.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  cdes WF'; eauto.
- intro.
  eapply COHERENT; eauto.
  eapply gstep_non_write_mo with (acts:=acts) (mo:=mo); eauto.
  eapply gstep_tm_to_a; eauto.
Qed.

Lemma Readable_msg_sc acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) t)
  (RFb: rf' b a) (SC: is_sc a): Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in MSG; desf.
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
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
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
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
  b o_b (INb : In b acts) (RFb : rf0 b a) (LABb : lab b = Astore l v o_b)
  m (SIM_MSG: sim_msg f acts sb rmw rf sc m b)
  rel (RELEASED: rel = Message.released m)
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
  f (MONOTONE : monotone mo f)
  a (NW: ~ is_write a) 
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
  mem (SIM_MEM : forall l, sim_cell f acts sb rmw rf sc (mem l) l):
  sim_mem f acts0 sb0 rmw0 rf0 sc0 mem.
Proof.
red; ins.
specialize (SIM_MEM l); red in SIM_MEM; desf.
red; splits; eauto; ins.
specialize (SIMCELL b WRITE LOC from msg CELL).
unfold sim_cell_helper, sim_msg in *; desc; splits; eauto.
4: by ins; apply FROMRMW; eapply gstep_rf_rmw with (rf' := rf0); eauto.
all: ins.
all: destruct msg; ins.
all: eapply max_value_same_set; try edone.
all: simpl.
admit.
admit.
admit. 
Admitted.

(******************************************************************************)
(** * Lemmas for the write step   *)
(******************************************************************************)

Lemma Writable_cur_rwr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l) t) 
   : Time.lt t (f' a).
Proof.
red in CUR; desf.
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
Qed.

Lemma Writable_cur_scr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l) t) 
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in CUR; desf.
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
Qed.

Lemma Writable_sc_map acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (SCMAP: max_value f (S_tm acts sb rmw rf l) t)
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in SCMAP; desf.
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
  red in INa; red in INa; desc.
  eapply S_tm_sc with (b:=y); eauto with acts.
  eapply S_tmr_mon; eauto.
apply SC_AT_END; eauto.
apply S_tmr_domb in INa; done.
- intro; subst; eauto with acts. 
Qed.

Lemma Writable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
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
  a l v o (LABa : lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
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
  a l v o (LABa : lab a = Astore l v o)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
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
    all:  try   rewrite !tm_find_singleton; desf; ins.
    all:  try   rewrite time_join_bot.
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

(******************************************************************************)
(** * Lemmas for the fence step   *)
(******************************************************************************)

Lemma commit_step_scfence acts sb rmw rf mo sc sc_map acts0 sb0 rmw0 rf0 mo0 sc0
  (COH : Coherent acts sb rmw rf mo sc)
  f (MONOTONE : monotone mo f)
  (SIM_SC_MAP : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  a o_r o_w (LABa : lab a = Afence o_r o_w)
  (F: is_sc_fence a)
  (ACQ: is_acq a)
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
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
    by eapply gstep_S_tm_fence; eauto.

  unfold sim_commit, sim_acq, sim_cur, sim_rel; splits; ins; desf.

all: try rewrite TimeMap.le_join_r with (r := TimeMap.join _ _).
all: try eapply max_value_same_set; try apply K; 
     eauto using gstep_t_cur_urr_scfence,
     gstep_t_cur_rwr_scfence,
     gstep_t_cur_srr_scfence, (* TYPO *)
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
  (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 a)
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
            (sc ax_st') a)
   (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
           (rf ax_st') (mo ax_st') (sc ax_st')) 
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.read l v o)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; desc. 
  destruct ax_st, ax_st'; simpl; ins.

generalize (gstep_read_rf COH GSTEP LABa); intro; desc.

assert (E: exists from rel, Cell.get (f b) ((Configuration.memory op_st) l) = 
          Some (from, {| Message.val:=v; Message.released:=rel |})).
  cdes GSTEP; cdes INC; cdes WF'.
  eapply get_cell; try edone. 
  rewrite <- ACT_STEP in *; try edone.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.
assert (LOC_B: Gevents.loc b = Some l). 
  unfold Gevents.loc; destruct (lab b); ins; desf.

cdes SIM_MEM. specialize (SIM_MEM l); red in SIM_MEM; desc.
specialize (SIMCELL b WRITE_B LOC_B from (Message.mk v rel) E).
red in SIMCELL; desc. 

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
            (sc ax_st') a)
   (COH' : Coherent (acts ax_st') (sb ax_st') (rmw ax_st') 
           (rf ax_st') (mo ax_st') (sc ax_st')) 
   lang st st'
   (STATE : Language.step lang (Some (ProgramEvent.write l v o)) st st'),
  proof_obligation ax_st ax_st' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; ins; desc.
  destruct ax_st, ax_st'; simpl; ins.

  generalize (new_f GSTEP MONOTONE); intro; desc.
  eexists _,_,_,_,_,_,_; splits; eauto.
  - eapply Thread.step_write; eauto.
  econstructor; eauto.
  * red in COMMIT; desc; eapply Writable_full; eauto.
  * admit.
  - exists f'; splits; try done.
  * eapply commit_step_write; eauto.
  * eapply sc_map_step_write; eauto.
  * admit. 
Admitted.


Lemma ax_op_sim_step_update :
  forall op_st ax_st ax_st'
         a_r l v_r o_r (LABar : lab a_r = Aload l v_r o_r)
         a_w v_w o_w (LABaw : lab a_w = Astore l v_w o_w)
         mc_mid
  (GSTEPr : gstep (acts ax_st) (sb ax_st) (rmw ax_st) 
             (rf ax_st) (mo ax_st) (sc ax_st) (acts mc_mid) 
             (sb mc_mid) (rmw mc_mid) (rf mc_mid) 
             (mo mc_mid) (sc mc_mid) a_r)
  (GSTEPw : gstep (acts mc_mid) (sb mc_mid) (rmw mc_mid) 
             (rf mc_mid) (mo mc_mid) (sc mc_mid) (acts ax_st') 
             (sb ax_st') (rmw ax_st') (rf ax_st') 
             (mo ax_st') (sc ax_st') a_w)
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
            (sc ax_st') a)
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
    by destruct a as [??[]]; ins; destruct o_w; ins. 
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

(* Lemma ax_sim_op :
  forall op_st ax_st (SIM: sim op_st ax_st) op_st' e tid (OPSTEP: Configuration.step tid e op_st op_st'),
  exists ax_st', m_step ax_st ax_st' /\ sim op_st' ax_st'.
Proof. *)


