(******************************************************************************)
(** * The axiomatic machine simulates the promise-free machine  *)
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
Require Import SimRel SimPreservation.
Require Import SmallStep.


Set Implicit Arguments.
Remove Hints plus_n_O.

Require Import Setoid Permutation.

Hint Resolve gstep_wf gstep_inc coh_wf.

Definition GMsim op_st ax_st :=
  << COH: Coherent (acts (exec ax_st)) (sb (exec ax_st)) (rmw (exec ax_st)) 
    (rf (exec ax_st)) (mo (exec ax_st)) (sc (exec ax_st)) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << NO_PROMISES: forall i foo local 
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: (ts ax_st) = IdentMap.map fst (Configuration.threads op_st) >>/\
  << TIME: exists f_from f_to, sim_time (Configuration.threads op_st)
     (Configuration.sc op_st) (Configuration.memory op_st) (exec ax_st) f_from f_to >>.

Definition get_program_event (e:ThreadEvent.t) : option ProgramEvent.t :=
  match e with
  |ThreadEvent.read loc _ val _ ord => Some (ProgramEvent.read loc val ord)
  |ThreadEvent.write loc _ _ val _ ord => Some (ProgramEvent.write loc val ord)
  |ThreadEvent.update loc _ _ valr valw _ _ ordr ordw => 
      Some (ProgramEvent.update loc valr valw ordr ordw)
  |ThreadEvent.fence ordr ordw => Some (ProgramEvent.fence ordr ordw)
  |ThreadEvent.syscall ev => Some (ProgramEvent.syscall ev)
  | _ => None
  end.

Lemma GMsim_helper tss G ths sc_map mem 
  (COH: Coherent (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G))
  (WF_OP_ST: Configuration.wf (Configuration.mk ths sc_map mem))
  (NO_PROMISES: forall i foo local (TID: IdentMap.find i ths = Some (foo, local)),
         local.(Local.promises) = Memory.bot)
  (STATES: tss = IdentMap.map fst ths)
  f_from f_to (TIME: sim_time ths sc_map mem G f_from f_to)
  tid pf e lang st lc st' lc' ths' sc_map' mem' 
  (THS2: ths' = IdentMap.add tid (existT Language.state lang st', lc') ths) 
  (TID: IdentMap.find tid ths = Some (existT Language.state lang st, lc))
  (STEP: Thread.step pf e (Thread.mk lang st lc sc_map mem) 
    (Thread.mk lang st' lc' sc_map' mem'))
  (PFREE: ThreadEvent.is_promising e = None)
  G' (MSTEP: mstep G G' (get_program_event e) (Some tid))
  f_from' (F_FROM: forall b, In b (acts G) -> f_from' b = f_from b)
  f_to' (F_TO: forall b, In b (acts G) -> f_to' b = f_to b)
  (MONOTONE: monotone (mo G') f_to')
  (SIM_TVIEW: forall foo local
        (TID: IdentMap.find tid ths' = Some (foo,local)),
        sim_tview f_to' (acts G') (sb G') (rmw G') (rf G') (sc G') 
                        local.(Local.tview) (Some tid))
  (SIM_SC_MAP: forall l, max_value f_to' (S_tm (acts G') (sb G') (rmw G') (rf G') l) 
                                     (LocFun.find l sc_map'))
  (SIM_MEM: sim_mem f_from' f_to' (acts G') (sb G') (rmw G') (rf G') (sc G') mem'):
  exists ax_st', step {| ts:=tss; exec:=G |}  ax_st' /\ 
    GMsim (Configuration.mk ths' sc_map' mem')  ax_st'.
Proof.
unfold GMsim in *; desc.
rewrite THS2.
destruct STEP; try by destruct STEP; ins.
eexists  {| ts:=  IdentMap.add tid (existT _ _ st') tss; exec:= G' |}; splits.
- admit.
  (* inv STEP.  *)
  (* all: econstructor; ins; try edone. *)
  (* all: try rewrite STATES. *)
  (* all: rewrite IdentMap.Facts.map_o; unfold option_map; ins; desf; eauto. *)
- by destruct MSTEP; subst; eauto.
- admit.
  (* eapply Configuration.step_future; eauto using no_promises_consistent. *)
  (* econs; eauto. *)
  (* eexists; splits; try econs. *)
  (* by eapply Progress.program_step_promise; eauto. *)
- admit.
  (* intro; simpl; rewrite IdentMap.gsspec; ins; desf; simpl. *)
  (* by eapply Progress.program_step_promise; eauto. *)
  (* by eapply NO_PROMISES; eauto. *)
- ins; rewrite IdentMap.map_add; simpl; by rewrite STATES.
- unfold sim_time in *; ins; desc.
  eexists f_from',f_to'; splits; eauto; ins.
  rewrite IdentMap.gsspec in TID0; desf; ins; simpl.
  eapply SIM_TVIEW; eauto using UsualFMapPositive.UsualPositiveMap'.gss.
  apply SIM_TVIEW0 in TID0.
  inv STEP; inv MSTEP; try by unfold get_program_event in *; ins; desf.
  by eapply sim_tview_other_threads_silent; eauto.
  all: eapply sim_tview_other_threads; eauto 2.
  all: try eapply sim_tview_other_threads; eauto 2.
  all: try intro; subst; eauto.
  all: congruence.
Admitted.

Require Import Omega.

Lemma fresh_id (acts: list event) tid lb:
  exists a, << THREAD_ID: thread a = tid >> /\ <<LABEL: lab a = lb >> /\ 
  <<FRESH: ~ In a acts >>.
Proof.
eexists (Event (1 + fold_right (fun x c => S (id x + c)) 0 acts) _ _); splits; try by simpl; eauto.
generalize 1; generalize 0; induction acts; ins.
intro; desf; desf; eauto.
destruct a; ins; desf; omega.
rewrite <- plus_Sn_m, Const.add_assoc in H; eapply IHacts; eauto.
Qed.

(******************************************************************************)
(** * Lemmas for silent step  *)
(******************************************************************************)

Lemma GMsim_silent ts G op_st tid lang st1 st2 lc2 
  (SIM: GMsim op_st {| ts:= ts; exec:= G |})
  (STATE: Language.step lang None st1 st2)
  (TID: IdentMap.find tid (Configuration.threads op_st) =
      Some (existT (fun lang : Language.t => Language.state lang) lang st1, lc2)):
  exists ax_st', step {| ts:= ts; exec:= G |} ax_st' /\
      GMsim (Configuration.mk 
        (IdentMap.add tid (existT Language.state lang st2, lc2) 
          (Configuration.threads op_st))
        (Configuration.sc op_st)
        (Configuration.memory op_st)) ax_st'.
Proof.
destruct op_st; ins.
unfold GMsim in *; desc; ins.
unfold sim_time in *; desc.
eapply GMsim_helper with (e:=ThreadEvent.silent) (tid:=tid); eauto.

econs; ins; eauto.
econs 2. econs; eauto.
admit.
(* ins; eapply SIM_TVIEW. *)
(* rewrite IdentMap.gsspec in TID0; desf; ins; simpl; eauto. *)
(* by exfalso; auto. *)
Admitted.

(******************************************************************************)
(** * Lemmas about well-formedness of the new graph  *)
(******************************************************************************)

Lemma wf_new_acts acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a): WfACTS (a :: acts).
Proof.
cdes WF.
unfold WfACTS in *; desc; splits.
by intros; right; eauto.
by intros; destruct IN; desf; eauto.
Qed.

Lemma wf_new_sb acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a): WfSB (a :: acts) (sb +++ sb_ext acts a).
Proof.
cdes WF.
unfold WfSB in *; desc; splits; ins.
all: try by destruct SB; unfold sb_ext, seq, eqv_rel in *; desc; subst; eauto.
- destruct SB; eauto. 
  unfold sb_ext, seq, eqv_rel, init_pair in *; desf; subst; eauto.
  left; splits; eauto; eapply thread_proper; eauto.
- unfold sb_ext, Relation_Operators.union, seq, eqv_rel, init_pair in *; desf; subst; eauto.
  unfold WfACTS in *; desc; eauto 10.
- intros x A; red in A; desf; unfold sb_ext, seq, eqv_rel in *; desf; eauto.
- intros x y z A B.
  unfold sb_ext, Relation_Operators.union, seq, eqv_rel in *; desf; eauto.
  by exfalso; apply FRESH; eauto.
  by exfalso; apply FRESH; eauto.
  right; eexists; splits; eauto.
  exists z; splits; eauto.
  apply SB_TID in A; desf.
  left; congruence.
  right; red in A; desc; eauto.
  exfalso.
  apply SB_TID in A; desf.
  eapply init_proper_thread; eauto.
  eapply proper_non_init; red in A; desc; eauto.
- desf; unfold sb_ext, seq, eqv_rel, Relation_Operators.union; eauto 10.
  exploit SB_TOT; eauto; ins; desf; eauto.
Qed.

Lemma wf_new_rmw acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a): WfRMW (sb +++ sb_ext acts a) rmw.
Proof.
cdes WF.
unfold WfRMW in *; desc; splits; ins.
- by left; eauto.
- destruct SB.
  left; eapply RMW_SBI; eauto.
  unfold sb_ext, seq, eqv_rel in *; desc; subst.
  by exfalso; apply FRESH; eapply rmw_actb; eauto.
- destruct SB.
  left; eapply RMW_SBI'; eauto.
  unfold sb_ext, seq, eqv_rel in *; desc; subst.
  right; exists b; splits; eauto_red using rmw_actb.
  exists c; splits; eauto.
  destruct H0.
  assert (RMW' := RMW).
  apply RMW_SB in RMW.
  apply WF_SB in RMW.
  desf.
  by left; congruence.
  apply RMW_DOMa in RMW'.
  by exfalso; eapply read_non_write; red in RMW; desc; eauto using init_is_write.
  by exfalso; eapply read_non_write with (a:=z); eauto using init_is_write.
Qed.

Lemma wf_new_rf acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a)
  (NON_READ: ~ is_read a) : WfRF (a :: acts) rf.
Proof.
cdes WF.
unfold WfRF in *; desc; splits; ins; eauto.
exploit RF_TOT; eauto; desf.
Qed.

Lemma wf_new_mo acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a)
  (NON_WRITE: ~ is_write a) : WfMO (a :: acts) mo.
Proof.
cdes WF.
unfold WfMO in *; desc; splits; ins; eauto.
red; ins; desf.
all: try by exfalso; eapply read_non_write; eauto.
eapply MO_TOT; splits; eauto.
Qed.

Lemma wf_new_sc acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a): WfSC (a :: acts) (sc +++ sc_ext acts a).
Proof.
cdes WF.
unfold WfSC in *; desc; splits; ins; eauto.
all: try unfold Relation_Operators.union, sc_ext in *; desf; eauto.
- intros x A; desf; eauto.
- intros x y z A B; desf; eauto 10.
  exfalso; eapply FRESH; eauto.
- red; ins; desf; eauto 8.
  assert (sc a0 b \/ sc b a0).
    eauto.
  desf; eauto.
Qed.

(******************************************************************************)
(** * Lemmas for read step  *)
(******************************************************************************)

Definition new_G_read G a b :=
{| acts:=(a :: acts G); sb:=(sb G +++ sb_ext (acts G) a);
           rmw:=(rmw G) ; rf:=(rf G +++ singl_rel b a); mo:= (mo G);
           sc:=(Machine.sc G +++ sc_ext (acts G) a) |}.

Lemma exists_gstep_read acts sb rmw rf mo sc a 
  (WF: Wf acts sb rmw rf mo sc)
  (FRESH: ~ In a acts) (PROPER: is_proper a) (READa: is_read a)
  b (INb: In b acts) (WRITEb: is_write b) 
  (LOC: exists l, loc b = Some l /\ loc a = Some l) (VAL: val b = val a):
  gstep acts sb rmw rf mo sc 
      (a :: acts) (sb +++ sb_ext acts a)
      rmw (rf +++ singl_rel b a) mo (sc +++ sc_ext acts a) a a.
Proof.
red; splits; eauto.
by unfold sb_ext, Relation_Operators.union, eqv_rel, seq; eauto 8.
by red; eauto.
by unfold sc_ext, Relation_Operators.union; eauto.
by red; unfold inclusion, Relation_Operators.union; splits; ins; eauto.
red; splits.
- eby eapply wf_new_acts.
- eby eapply wf_new_sb.
- eby eapply wf_new_rmw.
- cdes WF; unfold WfRF in *; desc; splits; ins.
  all: try unfold Relation_Operators.union, singl_rel in *; desf; eauto.
  all: try by exfalso; apply FRESH; eauto.
  exploit RF_TOT; eauto; ins; desc; eauto.
- eapply wf_new_mo; eauto 2 with acts.
- eby eapply wf_new_sc.
Qed.

Lemma new_G_read_NoPromises acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  (COH: Coherent acts sb rmw rf mo sc)  
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a a)
  b (NEQ: b <> a) :
  NoPromises sb' (rf +++ (singl_rel b a)) sc'.
Proof.
cdes GSTEP; cdes COH.
exploit gstep_sb; eauto.
exploit gstep_sc; eauto.
intros Usb Usc; rewrite Usb, Usc.
red; rewrite !unionA, (unionAC _ rf), 2!(unionAC _ sc), <- 2!unionA, unionC.
assert (MAX: forall x y,
  (sb_ext acts a +++ (singl_rel b a +++ sc_ext acts a)) x y -> y = a).
  by intros x y R; unfold sb_ext, singl_rel, sc_ext, seq, eqv_rel, Relation_Operators.union in R; desf.
apply acyclic_decomp_u_1; try done.
- ins; apply MAX in R; subst.
  unfold Relation_Operators.union in R'; desf;
  eapply FRESH; [eapply sb_acta| eapply rf_acta| eapply sc_acta]; edone.
- red; red; ins.
  eapply cycle_disj; cycle 1; try edone.
  ins; apply MAX in R; subst.
  unfold sb_ext, singl_rel, sc_ext, seq, eqv_rel, Relation_Operators.union in R'; desf; auto.
Qed.

Lemma new_G_read_coherent 
  acts sb rmw rf mo sc sc_map memory tview a
  (COH: Coherent acts sb rmw rf mo sc)
  f_from f_to (MONOTONE: monotone mo f_to)
  (SIM_TVIEW: sim_tview f_to acts sb rmw rf sc tview (thread a))
  (SIM_SC_MAP: forall l, max_value f_to (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  (SIM_MEM: sim_mem f_from f_to acts sb rmw rf sc memory)
  l v released o from b
  (READABLE: TView.readable tview.(TView.cur) l (f_to b) released o)
  (INb: In b acts) (WRITEb: is_write b) (LOCb: loc b = Some l)
  (HELPERb: sim_mem_helper f_to acts sb rmw rf sc b from v (View.unwrap released))
  (LABEL: lab a = Aload l v o)
  (FRESH: ~ In a acts)
  acts' sb' rmw' rf' mo' sc'
  (NEW_G: new_G_read {| acts:=acts; sb:=sb; rmw:=rmw; rf:=rf; mo:=mo; sc:=sc |}
   a b = {| acts:=acts'; sb:=sb'; rmw:=rmw'; rf:=rf'; mo:=mo'; sc:=sc' |})
  (GSTEP: gstep acts sb rmw rf mo sc 
               acts' sb' rmw' rf' mo' sc' a a):
  Coherent acts' sb' rmw' rf' mo' sc'.
Proof.
unfold new_G_read in *; ins; desf.

exploit gstep_hb_read; eauto.
right; edone.
intro HB.
 
assert (forall x y (MOxy: mo' x y), In y acts).
  ins; eapply mo_actb; eauto.

assert (forall x y (MOxy: mo' x y), is_write y).
  ins; eapply mo_domb; eauto. 

assert (forall x y (MOxy: mo' x y) (LOC: loc x = Some l), (loc y = Some l)).
  ins; eapply loceq_mo in MOxy; eauto.
  rewrite <- MOxy; done.

destruct READABLE; desc.
red in SIM_TVIEW; desc.
red in CUR; desc.
specialize (CUR_UR l).
specialize (CUR_RW l).
specialize (CUR_SC l).

cdes COH; red; splits; eauto.
- red; ins; destruct RF as [RF1|RF2].
  by eapply Crmw; eauto.
  by red in RF2; desc; desf; eapply rmw_acta in RMW; eauto.
- red; ins; eapply gstep_hb_a in HB0; try edone.
  destruct RF; unfold singl_rel in *; desf; eauto 2.
  eby apply FRESH; eapply hb_acta.
  eby intro; subst; apply FRESH; eapply mo_acta.
- red; ins; eapply gstep_hb_a in HB0; eauto 2.
  eby intro; subst; apply FRESH; eapply mo_acta.
- red; ins; destruct RF; unfold singl_rel in *; desf.
  eapply gstep_hb_a in HB0; eauto 2.
  eby intro; subst; apply FRESH; eapply rf_actb.
  apply HB in HB0; destruct HB0 as [?|[c[B[C|D]]]]; 
  unfold sb_ext, eqv_rel, seq in *; desc; try subst z z0.
  eby apply FRESH; eapply hb_actb.
  eby eapply max_value_le; eauto; repeat (eexists; splits; eauto).
  eby eapply Coherent_urr_rel; eauto; repeat (eexists; splits; eauto).
- red; ins; destruct RF; unfold singl_rel in *; desf; try eby eapply max_elt_hb.
  apply HB in HB0; clear HB.
  destruct RF'; unfold singl_rel in *; desf; destruct HB0 as [?|HB0]; eauto 2.
  by apply FRESH; eapply rf_actb; try edone;
    unfold Relation_Operators.union, sb_ext, seq, eqv_rel in *; desf; subst; eauto.
  eby apply FRESH; eapply hb_actb.
  destruct HB0 as [d A];
  unfold Relation_Operators.union, sb_ext, eqv_rel, seq in *; desc.
  assert (rwr acts sb rmw' rf sc l b0 d).
    by right; repeat (eexists; splits; eauto).
  destruct A0; desc; subst z z0.
  * eapply max_value_le with (tm:=View.rlx (TView.cur tview)); eauto.
    by red in RLX; rewrite LABEL in *; ins; auto.
    by exists d; repeat (eexists; splits; eauto).
  * eby eapply Coherent_rwr_rel.
- red; ins; destruct RF; unfold singl_rel in *; desf; try eby eapply max_elt_hb.
  eapply gstep_hb_a in HB0; try edone; cycle 1.
  eby intro; subst; eapply max_elt_hb.
  destruct RF'; desf.
  * eapply gstep_hb_a in HB1; eauto 2.
    eby intro; subst; eapply FRESH; eapply rf_actb.
  * apply HB in HB1; clear HB.
    destruct HB1 as [?|HB1].
    eby apply FRESH; eapply hb_actb.
    destruct HB1 as [e A];
    unfold Relation_Operators.union, sb_ext, eqv_rel, seq in *; desc.
    assert (urr acts sb rmw' rf sc l b0 e).
      by clear A0; unfold urr, rfhbsc_opt, seq, eqv_rel, clos_refl in *; desf; eauto 25. 
    destruct A0; desc; subst z z0.
    + eapply max_value_le; eauto.
      by exists e; repeat (eexists; splits; eauto).
    + eby eapply Coherent_urr_rel.
- red; ins; destruct RF; unfold singl_rel in *; 
  desf; eauto 2; eby eapply max_elt_rmw.
- red; ins.
  assert (RFHBF_: b0 = d \/
          (exists c, clos_refl rf b0 c /\ hb acts sb rmw' rf c d /\ is_sc_fence d)).
    destruct RFHBF as [X|[c [RF' [HB' F]]]]; auto.
    right; exists c; splits; try edone.
    destruct RF' as [?|[X|Y]]; unfold singl_rel in *; desc; subst; try by econs.
    eby exfalso; eapply max_elt_hb.
    eapply gstep_hb_a in HB'; try edone.
    eby intro; subst; eapply max_elt_sc.
  clear RFHBF.
  destruct SC as [SC|X]; cycle 1; unfold sc_ext in *; desc; subst.
  by unfold is_sc_wf in *; destruct a as [??[]]; desf; ins.
  apply HB in HB0; clear HB.
  destruct HB0 as [X|HB0].
  destruct RF; unfold singl_rel in *; desc; subst; eauto 2.
  eby apply FRESH; eapply hb_actb.
  assert (f=a).
   by unfold Relation_Operators.union, sb_ext, seq, eqv_rel, singl_rel in *; desf.
  subst f.
  destruct RF as [?|RF]; subst.
  by eapply FRESH, rf_actb; eauto.
  red in RF; desc; subst a0.
  unfold Relation_Operators.union, sb_ext, seq, eqv_rel, singl_rel in *.
  assert (rfhbsc_opt acts sb rmw' rf l b0 d).
   by clear HB0; red; unfold seq, eqv_rel, clos_refl in *; desf; eauto 20.
  destruct HB0 as [z HB0].
  assert (SC':=SC).
  eapply sc_domb in SC'; try edone.
  destruct SC' as [Ef|Ew].
  * assert (urr acts sb rmw' rf sc l b0 z).
    by unfold urr, seq, eqv_rel, clos_refl in *; desf; eauto 10.
    destruct HB0 as [HB0 [SB|REL']]; desc; subst z1 z0.
    eapply max_value_le; eauto.
    exists z,z; splits; eauto.
    by repeat (eexists; splits; eauto).
    eby eapply Coherent_urr_rel.
  * assert (is_write e).
     by destruct e as [??[]]; ins.
    assert (Ordering.le Ordering.seqcst o).
     by exploit SCread; try edone; intro SCa; red in SCa; destruct (lab a); ins; desf.
    assert (scr acts sb rmw' rf sc l b0 z).
     by right; unfold seq, eqv_rel, clos_refl in *; desf; eauto 10.
    destruct HB0 as [HB0 [SB|REL']]; desc; subst z1 z0.
    + eapply max_value_le with (tm:=View.sc (TView.cur tview)); eauto.
      exists z,z; splits; eauto.
      repeat (eexists; splits; eauto).
    + red in HELPERb; desc; red in SIMMSG; desc; specialize (SC0 l).
      eapply max_value_le with (tm:=View.sc (View.unwrap released)); eauto; ins.
      exists z; splits; eauto.

- red; ins.
  assert (RFHBF_: b0 = d \/
        (exists c, clos_refl rf b0 c /\ hb acts sb rmw' rf c d /\ is_sc_fence d)).
    destruct RFHBF as [X|[c [RF' [HB' F]]]]; auto.
    right; exists c; splits; try edone.
    destruct RF' as [?|[X|Y]]; unfold singl_rel in *; desc; subst; try by econs.
    eby exfalso; eapply max_elt_hb.
    eapply gstep_hb_a in HB'; eauto 2.
    intro; subst; eapply max_elt_sc; eauto.
  clear RFHBF.
  destruct SC as [SC|]; cycle 1; unfold sc_ext in *; desc; subst.
  by unfold is_sc_wf in *; destruct a as [??[]]; desf; ins.
  destruct HB0 as [|HB0]; subst; eauto 3.
  desc; apply HB in HB0; clear HB.
  destruct HB0 as [|HB0]; eauto 4.
  assert (a0=a); subst.
    by unfold Relation_Operators.union, sb_ext, seq, eqv_rel, singl_rel in *; desf; eauto.
  eapply mo_doma in MO; try edone.
  by destruct a as [??[]]; ins.
- eapply new_G_read_NoPromises; try edone.
  by intro; subst; eauto with acts.
Qed.

Lemma GMsim_read ts G tid lang st1 st2 lc1 lc2 threads sc_map mem
  (SIM: GMsim (Configuration.mk threads sc_map mem) {| ts:= ts; exec:= G |})
  (TID: IdentMap.find tid threads =
        Some (existT (fun lang : Language.t => Language.state lang) lang st1, lc1))
  l to v released o 
  (STATE: Language.step lang (Some (ProgramEvent.read l v o)) st1 st2)
  (LOCAL: Local.read_step lc1 mem l to v released o lc2):
  exists ax_st', step {| ts:= ts; exec:= G |} ax_st' /\
    GMsim (Configuration.mk (IdentMap.add tid (existT Language.state lang st2, lc2)
                                 threads) sc_map mem)
 ax_st'.
Proof.
unfold GMsim in *; desc; ins.
unfold sim_time in *; desc.
assert (LOCAL':=LOCAL).
destruct LOCAL'; ins; subst.
assert (SIM_MEM':= SIM_MEM).
specialize (SIM_MEM' l); desc.
specialize (SIMCELL to from v released GET); desc.

generalize (fresh_id (acts G) (Some tid) (Aload l v o)); intro; desc.

exploit exists_gstep_read; eauto with acts.
by red; eauto.
by exists l; splits; eauto with acts; unfold loc; desf.
by red in SIMCELL4; desc; rewrite <- VAL; unfold val; desf.
intro GSTEP.

eapply GMsim_helper with 
  (e:=ThreadEvent.read l to v released o) 
  (tid:=tid)  
  (G':= new_G_read G a b); eauto.
- by red; eauto.
- econs 2. econs; eauto.
- eapply read; eauto.
  unfold get_program_event; eauto.
  eapply new_G_read_coherent; eauto.
  by rewrite THREAD_ID; eauto.
  by rewrite SIMCELL3; eauto.
- ins.
  assert (LAB: exists o, lab b = Astore l v o); desc.
    red in SIMCELL4; desc.
    unfold Gevents.loc, is_write, val, lab in *.
    destruct b as [??[]]; ins; desf; eauto.
  exploit tview_step_read; eauto.
  * by right; red; eauto.
  * by apply SIMCELL4; rewrite THREAD_ID; eauto.
  * by rewrite THREAD_ID in *; eapply SIM_TVIEW; eauto.
  * rewrite IdentMap.gsspec in TID0; desf; ins.
    eby rewrite THREAD_ID in *.
- ins; eapply max_value_same_set; try edone.
  by ins; rewrite gstep_S_tm_other; eauto with acts.
- eapply memory_step_nonwrite; eauto.
  eapply new_G_read_coherent; eauto.
  rewrite THREAD_ID in *; eauto.
  by rewrite SIMCELL3; eauto.
  by eauto 3 with acts.
Qed.

(******************************************************************************)
(** * Lemmas for write step  *)
(******************************************************************************)

Definition new_mo acts f_to a to:=
  (fun x y => y = a /\ In x acts /\ is_write x /\ 
    loc x = loc a /\ Time.lt (f_to x) to)  \2/ 
  (fun x y => x = a /\ In y acts /\ is_write y /\ 
    loc y = loc a /\ Time.lt to (f_to y)).

Lemma wf_new_mo_write acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
  a (FRESH: ~ In a acts) (PROPER: is_proper a) (WRITE: is_write a)
  f_to to (MON: monotone mo f_to) 
  (NEQ: forall b, In b acts /\ is_write b /\ loc b = loc a -> f_to b <> to):
  WfMO (a :: acts) (mo +++ new_mo acts f_to a to).
Proof.
cdes WF; cdes WF_MO.
unfold new_mo, Relation_Operators.union.
red; splits.
- ins; desf; eauto_red using mo_acta.
- ins; desf; eauto_red using mo_actb.
- ins; desf; eauto_red using mo_doma.
- ins; desf; eauto_red using mo_domb.
- ins; desf; eauto.
  all: eapply write_has_location in MO1; desc; exists l; split; congruence.
- red; ins; desf; eauto.
- red; ins; desf; eauto.
  all: try eby exfalso; apply FRESH; eapply mo_acta.
  all: try eby exfalso; apply FRESH; eapply mo_actb.
  all: try eby exfalso; eapply Time.lt_strorder, Time.lt_strorder.
  * assert (Time.lt to (f_to z)).
    eapply MON in H0.
    eby eapply Time.lt_strorder.
    right; right; splits; eauto.
    specialize (MO_LOC y z H0); desc; congruence.
  * assert (Time.lt (f_to x) to).
    eapply MON in H.
    eby eapply Time.lt_strorder.
    right; left; splits; eauto.
    specialize (MO_LOC x y H); desc; congruence.
  * assert (Time.lt (f_to x) (f_to z)).
    eby eapply Time.lt_strorder.
    left; splits; eauto.
    eapply write_has_location in WRITE; desc.
    eapply wf_mo_tot with (l:=l); eauto; try congruence.
    intro MO.
    eapply MON in MO.
    eby eapply Time.lt_strorder,Time.lt_strorder.
    intro; subst.
    eby eapply Time.lt_strorder.
- assert (L: forall c, In c acts /\ is_write c /\ loc c = loc a -> 
    Time.lt (f_to c) to \/ Time.lt to (f_to c)).
    ins; destruct (Time.le_lt_dec (f_to c) to); auto.
    rewrite Time.le_lteq in *; desf; auto.
    eby edestruct NEQ.
  unfold is_total in *; ins; desf; rewrite IWa1,IWb1 in *.
  * destruct (L a0); eauto 10.
  * destruct (L b); eauto 10.
  * by exploit (MO_TOT l a0); eauto; ins; desf; eauto.
Qed.

Lemma new_f_to_monotone acts sb rmw rf mo sc (WF: Wf acts sb rmw rf mo sc)
f_to a to (MON: monotone mo f_to) 
(FRESH: ~ In a acts) (PROPER: is_proper a) (WRITE: is_write a)
  (NEQ: forall b, In b acts /\ is_write b /\ loc b = loc a -> f_to b <> to):
monotone (mo +++ new_mo acts f_to a to) (upd f_to a to).
Proof.
unfold monotone, upd, Relation_Operators.union, new_mo in *; ins; desf.
eby exfalso; desf; cdes WF; eapply WF_MO.
all: desf; eauto; try edone.
eby exfalso; apply FRESH; eapply mo_acta.
eby exfalso; apply FRESH; eapply mo_actb.
Qed.

Definition new_rmw (a_r a_w: event) := fun x y => a_r <> a_w /\ x= a_r /\ y = a_w.

Definition new_G_write G a_r a f_to to :=
  {| acts:=(a :: acts G); sb:=(sb G +++ sb_ext (acts G) a);
           rmw:= (rmw G +++ new_rmw a_r a) ; rf:=(rf G); 
           mo:= (mo G) +++ new_mo (acts G) f_to a to;
           sc:=(Machine.sc G +++ sc_ext (acts G) a) |}.

Lemma exists_gstep_write acts sb rmw rf mo sc a 
  (WF: Wf acts sb rmw rf mo sc)
  (FRESH: ~ In a acts) (PROPER: is_proper a) (WRITEa: is_write a)
  f_to to (WF_MO': WfMO (a :: acts) (mo +++ new_mo acts f_to a to)):
  gstep acts sb rmw rf mo sc 
      (a :: acts) (sb +++ sb_ext acts a)
      rmw rf (mo +++ new_mo acts f_to a to) (sc +++ sc_ext acts a) a a.
Proof.
red; splits; eauto.
by unfold sb_ext, Relation_Operators.union, eqv_rel, seq; eauto 8.
by red; eauto.
by unfold sc_ext, Relation_Operators.union; eauto.
by red; unfold inclusion, Relation_Operators.union; splits; ins; eauto.
red; splits; try done.
- eby eapply wf_new_acts.
- eby eapply wf_new_sb.
- eby eapply wf_new_rmw.
- eapply wf_new_rf; eauto 2 with acts.
- eby eapply wf_new_sc.
Qed.

Lemma new_G_non_read_NoPromises acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  (COH: Coherent acts sb rmw rf mo sc)  
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a):
  NoPromises sb' rf sc'.
Proof.
cdes GSTEP; cdes COH.
exploit gstep_sb; eauto.
exploit gstep_sc; eauto.
intros Usb Usc; rewrite Usb, Usc.
red; rewrite !unionA, (unionAC _ rf), (unionAC _ sc), <- 2!unionA, unionC.
assert (MAX: forall x y,
  (sb_ext acts a +++ sc_ext acts a) x y -> y = a).
  by intros x y R; unfold sb_ext, singl_rel, sc_ext, seq, eqv_rel, Relation_Operators.union in R; desf.
apply acyclic_decomp_u_1; try done.
- ins; apply MAX in R; subst.
  unfold Relation_Operators.union in R'; desf;
  eapply FRESH; [eapply sb_acta| eapply rf_acta| eapply sc_acta]; edone.
- red; red; ins.
  eapply cycle_disj; cycle 1; try edone.
  ins; apply MAX in R; subst.
  unfold sb_ext, singl_rel, sc_ext, seq, eqv_rel, Relation_Operators.union in R'; desf; auto.
Qed.

Lemma new_G_update_coherent 
  acts sb rmw rf mo sc sc_map memory tview a
  (COH: Coherent acts sb rmw rf mo sc)
  f_from f_to (MONOTONE: monotone mo f_to)
  (SIM_TVIEW: sim_tview f_to acts sb rmw rf sc tview (thread a))
  (SIM_SC_MAP: forall l, max_value f_to (S_tm acts sb rmw rf l) (LocFun.find l sc_map))
  (SIM_MEM: sim_mem f_from f_to acts sb rmw rf sc memory)
  l v o to
  (NEW_TO: forall x, In x acts /\ is_write x /\ loc x = Some l /\ 
            Time.lt (f_from x) to /\ Time.le to (f_to x) -> False)
  (WRITABLE: TView.writable tview.(TView.cur) sc_map l to o)
  (LABEL: lab a = Astore l v o)
  (FRESH: ~ In a acts)
  acts' sb' rmw' rf' mo' sc' 
  (NEW_MO: mo' = mo +++ new_mo acts f_to a to)
  a_r
  (NEW_G: new_G_write {| acts:=acts; sb:=sb; rmw:=rmw; rf:=rf; mo:=mo; sc:=sc |}
   a_r a f_to to = {| acts:=acts'; sb:=sb'; rmw:=rmw'; rf:=rf'; mo:=mo'; sc:=sc' |})
  (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a_r a)
  (UPDATE: forall x a0, In x acts /\ is_write x /\ loc x = Some l /\ 
    a_r <> a /\ rf a0 a_r /\ Time.lt (f_to x) to /\ Time.lt (f_to a0) (f_to x) -> False):
  Coherent acts' sb' rmw' rf' mo' sc'.
Proof.
unfold new_G_write in *; ins; desf.

exploit gstep_hb_write; eauto with acts.
intro HB.

assert (forall b, loc b = loc a -> loc b = Some l).
  by ins; unfold loc in *; destruct a as [??[]]; desf.

destruct WRITABLE; desc; red in SIM_TVIEW; desc; red in CUR; desc.
specialize (CUR_UR l); specialize (CUR_RW l); specialize (CUR_SC l).
clear SC1. (* this assumption is redundant *)
cdes COH.
red; splits; eauto.
- admit. (* follows from other conditions?!*)
- red; ins; destruct MO as [MO1|MO2].
  eapply gstep_hb_a in HB0; eauto 2.
  eby intro; subst; eapply FRESH; eapply mo_acta.
  red in MO2; desf.
  eby eapply FRESH; eapply rf_acta.
  apply HB in HB0.
  destruct HB0 as [[HB0|HB0]|HB0].
  eby eapply FRESH; eapply hb_actb.
  all: eapply max_value_lt with (tm := (View.rlx (TView.cur tview))); eauto. 
  * unfold seq, sb_ext, seq, eqv_rel, singl_rel in *; desc; subst z1 z0.
    repeat eexists; splits; eauto.
    right; repeat eexists; splits; eauto.
  * unfold sb_ext, seq, eqv_rel, singl_rel in *;desc; subst z0 z.
    repeat eexists; splits; eauto.
    right; repeat eexists; splits; eauto.
- red; ins; destruct MO as [MO1|MO2].
  eapply gstep_hb_a in HB0; eauto 2.
  eby intro; subst; eapply FRESH; eapply mo_acta.
  red in MO2; desf; apply HB in HB0; destruct HB0 as [[?|[??]]|?]; desc.
  all: try eby eapply FRESH; eapply hb_acta.
  all: try eby eapply FRESH; eapply hb_actb.
  all: try eby unfold sb_ext, seq, eqv_rel in *; desf.
  all: unfold sb_ext, seq, eqv_rel, singl_rel in *; desc; subst z0 z.
  all: eapply max_value_lt with (tm := (View.rlx (TView.cur tview))); eauto.
  all: repeat eexists; splits; eauto.
  all: left; repeat eexists; splits; eauto.
- red; ins; apply HB in HB0; destruct HB0 as [[?|[??]]|?]; desc; 
    try eby unfold sb_ext, seq, eqv_rel in *; desc; subst c z0; 
    eapply FRESH; eapply rf_actb.
  destruct MO as [?|MO]; eauto 2.
  red in MO; desf.
  eby eapply FRESH; eapply hb_acta.
  eby eapply FRESH; eapply rf_acta.
- red; ins.
  destruct MO as [MO1|MO2]; cycle 1.
  eby red in MO2; desf; eapply FRESH; eapply rf_acta.
  apply HB in HB0; destruct HB0 as [[?|[??]]|?]; desc; eauto 2;
  eby unfold sb_ext, seq, eqv_rel in *; desc; subst d z0; 
    eapply FRESH; eapply rf_actb.
- red; ins.
  destruct MO as [MO1|MO2]; cycle 1.
  eby red in MO2; desf; eapply FRESH; eapply rf_acta.
  apply HB in HB0; destruct HB0 as [[?|[??]]|?]; desc.
  all: try eby unfold sb_ext, seq, eqv_rel in *; desc; subst d z0 z;
    destruct a as [??[]]; ins.
  apply HB in HB1; destruct HB1 as [[?|[??]]|?]; desc; eauto 2.
  all: eby unfold sb_ext, seq, eqv_rel in *; desc; subst e z0; 
    eapply FRESH; eapply rf_actb.
- red; ins.
unfold Relation_Operators.union, new_mo, singl_rel, new_rmw in *; desf; eauto 2.
all: try eby eapply FRESH; eapply rf_acta.
all: try eby eapply FRESH; eapply rmw_actb.
all: try eby eapply FRESH; eapply mo_actb.
all: try eby eapply FRESH; eapply mo_acta.
all: try by eapply UPDATE; splits; eauto 2.
{ assert (loc a = Some l).
    by destruct a as [??[]]; ins; desf.
  assert(loc c = Some l /\ loc d = Some l /\ loc a0 = Some l); desc.
    red in WF; desc.
    red in WF_RMW; desc.
    splits; by apply RMW_LOC in RMW; desc; congruence.
  assert (exists m, Memory.get l (f_to c) memory = Some (f_to a0, m)); desc.
    eapply SIM_MEM; eauto.
    red; eauto.
  assert (TF: f_to a0 = f_from c).
    specialize (SIM_MEM l); desc.
    destruct m.
    exploit (SIMCELL (f_to c) (f_to a0)); try edone.
    ins; desc.
    assert (b=c); subst.
      eby cdes COH; cdes WF; eapply monotone_injective.
    done.

  eapply NEW_TO; splits; eauto.
  by rewrite <- TF; done.
  by eapply Time.le_lteq; eauto.
}
- red; ins.
  eapply gstep_hb_a in HB0; try edone; cycle 1.
  eby intro; subst; eapply FRESH; eapply rf_actb.
  destruct SC as [SCo|SCn]; cycle 1.
  eby unfold sc_ext in *; desc; subst e; eapply FRESH; eapply hb_acta.
  assert (a <> d).
    eby intro; subst; eapply FRESH; eapply sc_acta.
  assert (RFHBF_: b = d \/
          (exists c, clos_refl rf' b c /\ hb acts sb rmw rf' c d /\ is_sc_fence d)).
    destruct RFHBF as [X|[c [RF' [HB' F]]]]; auto.
    right; exists c; splits; try edone.
    eapply gstep_hb_a in HB'; eauto.
  clear RFHBF.
  destruct MO as [?|MO]; eauto 2.
  destruct MO; desc; subst; unfold clos_refl in *; desf; auto.
  eby eapply FRESH; eapply hb_acta.
  all: eby eapply FRESH; eapply rf_acta.
- red; ins.

  assert (a <> d).
    destruct SC; unfold sc_ext in *; desc; intro; subst; eapply FRESH; try edone.
    eby eapply sc_acta.

  assert (RFHBF_: b = d \/
          (exists c, clos_refl rf' b c /\ hb acts sb rmw rf' c d /\ is_sc_fence d)).
    destruct RFHBF as [X|[c [RF' [HB' F]]]]; auto.
    right; exists c; splits; try edone.
    eapply gstep_hb_a in HB'; eauto.
  clear RFHBF.

  assert (MO': mo a0 b \/ a0=a /\ In b acts /\ is_write b /\ 
      loc b = loc a /\ Time.lt to (f_to b)).
    destruct MO as [?|MO]; auto.
    destruct MO; auto; desc; subst b.
    exfalso; destruct RFHBF_ as [A|B]; auto; desc.
    destruct B; try subst c.
    eby eapply FRESH; eapply hb_acta.
    eby eapply FRESH; eapply rf_acta.
  clear MO.

  destruct (classic (e=a)) as [EQ|NEW]; subst.
  * destruct SC as [?|SC].
    eby eapply FRESH; eapply sc_actb.
    unfold sc_ext in *; desc.
    destruct HB0 as [HB0|HB0]; cycle 1; try subst a0; desc.
    by destruct a as [??[]]; ins.
    destruct MO' as [?|MO]; desc.
    eby eapply FRESH; eapply mo_acta.
    assert (rfhbsc_opt acts sb rmw rf' l b d).
     by red; unfold clos_refl, eqv_rel, seq; desf; eauto 15.
    eapply max_value_lt with (tm:= sc_map); eauto.
    by eapply SC2; destruct a as [??[]]; unfold is_sc_wf in *; ins; desf.
    by eexists d,d; splits; red; eauto.
  * destruct SC as [SC|?]; cycle 1.
    by unfold sc_ext in *; desc; subst; auto.
    destruct HB0 as [?|HB0]; try subst a0; desc.
    by destruct MO' as [MO'|?]; desc; eauto 3.
    apply HB in HB0; destruct HB0 as [[?|[??]]|?]; desc.
    + destruct MO' as [MO'|?]; desc; eauto 4.
    eby subst a0; eapply FRESH; eapply hb_actb.
    + unfold sb_ext, eqv_rel, seq in *; desc; subst z0 z a0.
      destruct MO' as [?|MO']; desc.
      eby eapply FRESH; eapply mo_acta.
      eapply max_value_lt with (tm:= View.rlx (TView.cur tview)); eauto.
      eexists x,x; splits.
      left; unfold c_cur, rwr, urr, rfhbsc_opt, clos_refl, eqv_rel, seq in *; desf; eauto 30.
      by splits; try eexists; eauto.
    + unfold sb_ext, eqv_rel, seq in *; desc; subst z0 z a0.
      destruct MO' as [?|MO']; desc.
      eby eapply FRESH; eapply mo_acta.
      eapply max_value_lt with (tm:= View.rlx (TView.cur tview)); eauto.
      eexists e, e; splits.
      left; unfold c_cur, rwr, urr, rfhbsc_opt, clos_refl, eqv_rel, seq in *; desf; eauto 30.
      splits; try eexists; eauto.
- eby eapply new_G_non_read_NoPromises.
Admitted.

Lemma fresh_to acts sb rmw rf sc tid lang st1 lc1 threads mem f_from f_to
  (NO_PROMISES : forall i foo local, IdentMap.find i threads = Some (foo, local) ->
              Local.promises local = Memory.bot)
  (SIM_MEM : sim_mem f_from f_to acts sb rmw rf sc mem)
  (TID : IdentMap.find tid threads = Some (existT (fun lang => Language.state lang) lang st1, lc1))
  l from to v o a (LABEL : lab a = Astore l v o)
  promises2 mem2 kind released
  (WRITE : Memory.write (Local.promises lc1) mem l from to v released promises2 mem2 kind):
  forall b : event, In b acts /\ is_write b /\ loc b = loc a -> f_to b <> to.
Proof.
red; ins; desf.
specialize (SIM_MEM l); desc.
eapply (DOM b); splits; eauto 2 with acts.
by destruct a as [??[]]; ins; desf.
destruct WRITE, PROMISE.
- eapply Memory.add_get0; eauto.
- eapply Memory.split_get0; eauto.
- erewrite NO_PROMISES in PROMISES; try edone.
  eapply Memory.lower_get0 in PROMISES.
  by rewrite Memory.bot_get in *. 
Qed.

Lemma memory_helper tid lang st1 lc1 threads mem  
  (NO_PROMISES : forall i foo local, IdentMap.find i threads = Some (foo, local) ->
              Local.promises local = Memory.bot)
  (TID : IdentMap.find tid threads = Some (existT (fun lang => Language.state lang) lang st1, lc1))l from to v 
  promises2 mem2 kind released
  (WRITE : Memory.write (Local.promises lc1) mem l from to v released promises2 mem2 kind):
  kind = Memory.op_kind_add /\ promises2 = Memory.bot /\ exists promises0, 
 << ADD: Memory.add mem l from to v released mem2 >> /\
 << REMOVE: Memory.remove promises0 l from to v released promises2 >>.
Proof.
destruct WRITE, PROMISE; splits; eauto. 
all: erewrite NO_PROMISES in PROMISES; try edone.
all: try apply Memory.split_get0 in PROMISES.
all: try apply Memory.lower_get0 in PROMISES.
all: try by desc; rewrite Memory.bot_get in *.
apply Memory.ext; ins.
by rewrite (Memory.remove_o _ _ REMOVE), (Memory.add_o _ _ PROMISES), Memory.bot_get;
desf; ins; desf.
Qed.

Lemma disjoint_to acts sb rmw rf mo sc mem
  (COH : Coherent acts sb rmw rf mo sc)
  f_from f_to (MONOTONE : monotone mo f_to)
  (SIM_MEM : sim_mem f_from f_to acts sb rmw rf sc mem)
  l from to v o a (LABEL : lab a = Astore l v o)
  mem2 released (ADD : Memory.add mem l from to v released mem2)
  x (IN: In x acts) (WRITEx: is_write x) (LOC: loc x = Some l)
  (TIMElt: Time.lt (f_from x) to) (TIMEto: Time.le to (f_to x)) : False.
Proof.
  assert (exists v, val x = Some v); desc.
    by destruct x as [??[]]; try exists v0; ins; desf.
  exploit sim_mem_get; eauto.
  cdes COH; cdes WF; eauto.
  intro M; desc.
  destruct ADD, ADD.
  eapply DISJOINT; try edone.
  econs; ins; eauto.
  by eapply Time.le_lteq; eauto.
Qed.

Lemma GMsim_write ts G tid lang st1 st2 lc1 lc2 threads sc_map mem sc_map' mem'
  (SIM: GMsim (Configuration.mk threads sc_map mem) {| ts:= ts; exec:= G |})
  (TID: IdentMap.find tid threads =
        Some (existT (fun lang : Language.t => Language.state lang) lang st1, lc1))
  l from to v released o kind
  (STATE: Language.step lang (Some (ProgramEvent.write l v o)) st1 st2)
  (LOCAL: Local.write_step lc1 sc_map mem l
          from to v None released o lc2 sc_map' mem' kind):
  exists ax_st', step {| ts:= ts; exec:= G |} ax_st' /\
    GMsim (Configuration.mk 
        (IdentMap.add tid (existT Language.state lang st2, lc2) threads) sc_map' mem')
     ax_st'.
Proof.
generalize (fresh_id (acts G) (Some tid) (Astore l v o)); intro; desc.
unfold GMsim, sim_time in *; desc; ins.
assert (LOCAL':=LOCAL).
destruct LOCAL'; ins; subst.

assert (is_proper a).
by red; eauto.

assert (kind = Memory.op_kind_add /\ promises2 = Memory.bot /\ exists promises0, 
 << ADD: Memory.add mem l from to v (TView.write_released (Local.tview lc1) sc_map l to None o) mem2 >> /\
 << REMOVE: Memory.remove promises0 l from to v (TView.write_released (Local.tview lc1) sc_map l to None o) promises2 >>).
eby eapply memory_helper.
desc; subst promises2.

assert (forall b : event, In b (acts G) -> upd f_to a to b = f_to b).
  by unfold upd; desf; ins; desf.

assert (forall b : event, In b (acts G) -> upd f_from a from b = f_from b).
  by unfold upd; desf; ins; desf.

assert (MONOTONE': monotone (mo (new_G_write G a a f_to to)) (upd f_to a to)).
  by eapply new_f_to_monotone; eauto 2 using fresh_to with acts.

assert (sim_tview f_to (acts G) (sb G) (rmw G) (rf G) (sc G) (Local.tview lc1) (thread a)).
  by rewrite THREAD_ID in *; eapply SIM_TVIEW; eauto.

assert (NEW_RMW: rmw G +++ new_rmw a a <--> rmw G).
unfold Relation_Operators.union, new_rmw.
split; unfold inclusion; ins; desf; eauto; try edone.

exploit exists_gstep_write; eauto with acts.
by eapply wf_new_mo_write with (to:=to); eauto 2 using fresh_to with acts.
intro GSTEP.
rewrite <- NEW_RMW in GSTEP at 2.
eapply GMsim_helper with 
    (e:=ThreadEvent.write l from to v 
      (TView.write_released (Local.tview lc1) sc_map l to None o) o) 
    (tid:=tid) (f_to:=f_to) (f_to':=upd f_to a to) 
    (f_from:=f_from) (f_from':=upd f_from a from)
    (G':= new_G_write G a a f_to to); eauto.
* red; splits; eauto.
* econs 2. econs; eauto.
* eapply write; eauto.
  unfold get_program_event; eauto.
  eapply new_G_update_coherent with (a_r:=a); eauto.
  eby ins; desc; eapply disjoint_to.
  eby ins; desc.
* ins.
  rewrite IdentMap.gsspec in TID0; desf; ins; try edone.
  pattern to at 2; erewrite <- upds with (b:=to).
  rewrite <- THREAD_ID; eapply tview_step_write; eauto.
* ins; pattern to at 2; erewrite <- upds with (b:=to).
  eapply sc_map_step_write; eauto.
* ins; eapply memory_step_write; eauto.
  eapply WF_OP_ST.
  rewrite !upds.
  eby eapply MemoryFacts.MemoryFacts.write_time_lt.
  erewrite NO_PROMISES in WRITE; try edone.
  by rewrite !upds; desf.
Qed.

(******************************************************************************)
(** * Lemmas for update step  *)
(******************************************************************************)

Lemma exists_gstep_update acts sb rmw rf mo sc a_r a_w 
  (COH: Coherent acts sb rmw rf mo sc)
  (FRESHr: ~ In a_r acts) (PROPERr: is_proper a_r) (READ: is_read a_r)
  acts_m sb_m rmw_m rf_m mo_m sc_m       
  (GSTEPr: gstep acts sb rmw rf mo sc acts_m sb_m rmw_m rf_m mo_m sc_m a_r a_r)
  (COHm: Coherent acts_m sb_m rmw_m rf_m mo_m sc_m)
  (FRESHw: ~ In a_w acts_m) (PROPERw: is_proper a_w) (WRITE: is_write a_w)
  l (LOCr: loc a_r = Some l) (LOCw: loc a_w = Some l) (TID: thread a_r = thread a_w)
  f_to to (WF_MO': WfMO (a_w :: acts_m) (mo_m +++ new_mo acts_m f_to a_w to)):
  gstep acts_m sb_m rmw_m rf_m mo_m sc_m
      (a_w :: acts_m) (sb_m +++ sb_ext acts_m a_w)
      (rmw_m +++ singl_rel a_r a_w) rf_m (mo_m +++ new_mo acts_m f_to a_w to) 
(sc_m +++ sc_ext acts_m a_w) a_r a_w.
Proof.
red; splits; eauto.
by unfold sb_ext, Relation_Operators.union, eqv_rel, seq; eauto 8.
by right; splits; eauto; intro; subst; destruct a_w as [??[]]; ins.
by unfold sc_ext, Relation_Operators.union; eauto.
by red; unfold inclusion, Relation_Operators.union; splits; ins; eauto.
cdes GSTEPr; desc; cdes WF'; cdes WF_RMW.
red; splits; try done.
- eby eapply wf_new_acts.
- eby eapply wf_new_sb.
- red; splits; try by unfold Relation_Operators.union, singl_rel; ins; desf; eauto.
  * unfold Relation_Operators.union, singl_rel, sb_ext, eqv_rel, seq; ins; desf; eauto.
    right; exists a_r; splits; eauto.
    by left.
  * unfold Relation_Operators.union; ins; desf.
    + by left; eapply RMW_SBI; edone.
    + unfold singl_rel in *; desf.
       eby exfalso; apply FRESHw; eapply sb_actb.
    + unfold singl_rel, sb_ext, eqv_rel, seq in *; desf; eauto.
       eby exfalso; apply FRESHw; eapply rmw_actb.
       red in WF_SB; desc.
       left. eapply SB_INIT.
       red; splits; eauto.
       eby eapply no_rmw_from_init.
       eby eapply rmw_acta.
    + unfold singl_rel, sb_ext, eqv_rel, seq in *; desf; eauto; subst z0 z b a; left.
       eapply SB_AT_END; eauto.
       by left; congr.
       eby destruct SB3; subst.
       red in WF_SB; desc.
       eapply SB_INIT.
       red; splits; eauto.
       by left.
  * unfold Relation_Operators.union, singl_rel, sb_ext, eqv_rel, seq; ins; desf; eauto; try by edone.
    eby exfalso; eapply max_elt_sb with (acts:=acts).
    right.
    exists b; splits; eauto.
    eby eapply rmw_actb.
    exists c.
    splits; eauto.
    apply RMW_SB in RMW.
    red in WF_SB; desc.
    eapply SB_TID in RMW; desf. 
    left; congr.
    exfalso.
    eapply  init_proper_thread.
    red in RMW; desc; eauto. edone.
    done.
    exfalso; eapply proper_non_init.
    eby eapply no_rmw_from_init.
    exfalso; eapply proper_non_init.
    eby eapply no_rmw_from_init.
    done.
- eapply wf_new_rf; eauto 2 with acts.
- eby eapply wf_new_sc.
Qed.

Lemma GMsim_update ts G tid lang st1 st2 lc1 lc2 lc3 threads sc_map mem sc_map' mem'
  (SIM: GMsim (Configuration.mk threads sc_map mem) {| ts:= ts; exec:= G |})
  (TID: IdentMap.find tid threads =
        Some (existT (fun lang : Language.t => Language.state lang) lang st1, lc1))
  l to_r to_w v_r v_w released_r released_w o_r o_w kind
  (STATE: Language.step lang (Some (ProgramEvent.update l v_r v_w o_r o_w)) st1 st2)
  (LOCAL1: Local.read_step lc1 mem l to_r v_r released_r o_r lc3) 
  (LOCAL2: Local.write_step lc3 sc_map mem l
          to_r to_w v_w released_r released_w o_w lc2 sc_map' mem' kind):
  exists ax_st', step {| ts:= ts; exec:= G |} ax_st' /\
    GMsim (Configuration.mk 
        (IdentMap.add tid (existT Language.state lang st2, lc2) threads) sc_map' mem')
     ax_st'.
Proof.
generalize (fresh_id (acts G) (Some tid) (Aload l v_r o_r)); intro; desc.
unfold GMsim, sim_time in *; desc; ins.
assert (LOCAL1':=LOCAL1).
destruct LOCAL1'; ins; subst.
assert (SIM_MEM':= SIM_MEM).
specialize (SIM_MEM' l); desc.
assert (SIMCELL':= SIMCELL).
specialize (SIMCELL' to_r from v_r released_r GET); desc.
cdes SIMCELL'4; desc.

assert (LAB: exists o_b, lab b = Astore l v_r o_b); desc.
by unfold loc, is_write, val, lab in *; destruct b as [??[]]; ins; desf; eauto 2.

assert (is_proper a).
by red; eauto.

generalize (fresh_id (a :: acts G) (Some tid) (Astore l v_w o_w)); intro; desc.

assert (LOCAL2':=LOCAL2).
destruct LOCAL2'; ins; subst.

assert (is_proper a0).
by red; eauto.

assert (kind = Memory.op_kind_add /\ promises2 = Memory.bot /\ exists promises0, 
 << ADD: Memory.add mem l (f_to b) to_w v_w 
(TView.write_released
             (TView.read_tview (Local.tview lc1) l (f_to b) released_r o_r) sc_map
             l to_w released_r o_w) mem2 >> /\
 << REMOVE: Memory.remove promises0 l (f_to b) to_w v_w 
(TView.write_released
             (TView.read_tview (Local.tview lc1) l (f_to b) released_r o_r) sc_map
             l to_w released_r o_w) promises2 >>).
 eby eapply memory_helper.
desc; subst promises2.

 assert (forall b : event, In b (a :: acts G) -> upd f_to a0 to_w b = f_to b).
  by unfold upd; desf; ins; desf; exfalso; apply FRESH0; eauto.
 
assert (forall b : event, In b (acts G) -> upd f_to a0 to_w b = f_to b).
  by unfold upd; desf; ins; desf; exfalso; apply FRESH0; eauto.

 assert (forall c : event, In c (a :: acts G) -> upd f_from a0 (f_to b) c = f_from c).
  by unfold upd; desf; ins; desf; exfalso; apply FRESH0; eauto.
 
assert (forall c : event, In c (acts G) -> upd f_from a0 (f_to b) c = f_from c).
  by unfold upd; desf; ins; desf; exfalso; apply FRESH0; eauto.

assert (gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) (a :: acts G)
  (sb G +++ sb_ext (acts G) a) (rmw G) (rf G +++ singl_rel b a) 
  (mo G) (sc G +++ sc_ext (acts G) a) a a).
{ eapply exists_gstep_read; eauto with acts.
  by exists l; splits; eauto with acts; unfold loc; desf.
  rewrite <- VAL; unfold val; desf. }

assert (COHr: Coherent (a :: acts G) (sb G +++ sb_ext (acts G) a) (rmw G)
  (rf G +++ singl_rel b a) (mo G) (sc G +++ sc_ext (acts G) a)).
{ eapply new_G_read_coherent; eauto.
  by rewrite THREAD_ID in *; eauto. }

assert (sim_mem f_from f_to (a :: acts G) (sb G +++ sb_ext (acts G) a) 
  (rmw G) (rf G +++ singl_rel b a) (sc G +++ sc_ext (acts G) a) mem).
{ eapply memory_step_nonwrite with (acts:=acts G); eauto.
  by destruct a as [??[]]; ins; desf. }

assert (MONOTONE': monotone (mo (new_G_write (new_G_read G a b) a a0 f_to to_w))
 (upd f_to a0 to_w)).
{ eapply new_f_to_monotone; eauto 2 with acts.
  eby eapply fresh_to. }

assert (sim_tview f_to (acts G) (sb G) (rmw G) (rf G) (sc G) (Local.tview lc1) (thread a)).
  by rewrite THREAD_ID in *; eapply SIM_TVIEW; eauto.

assert (forall l0, max_value f_to
    (S_tm (a :: acts G) (sb G +++ sb_ext (acts G) a) (rmw G) 
     (rf G +++ singl_rel b a) l0) (LocFun.find l0 sc_map)).
{ ins; eapply max_value_same_set; try edone.
  by ins; rewrite gstep_S_tm_other; eauto 3 with acts. }

assert (sim_tview f_to (a :: acts G) (sb G +++ sb_ext (acts G) a) 
  (rmw G) (rf G +++ singl_rel b a) (sc G +++ sc_ext (acts G) a)
  (TView.read_tview (Local.tview lc1) l (f_to b) released_r o_r) (thread a0)).
{ rewrite THREAD_ID0, <- THREAD_ID.
  eapply tview_step_read with (acts:= acts G); eauto.
  by right; red; eauto. }

assert (SIM_MEMr: sim_mem f_from f_to 
 (a :: acts G) (sb G +++ sb_ext (acts G) a) 
  (rmw G) (rf G +++ singl_rel b a) (sc G +++ sc_ext (acts G) a) mem).
eby eapply memory_step_nonwrite with (acts:= acts G); eauto 3 with acts.


assert (NEW_RMW: new_rmw a a0 <--> singl_rel a a0).
by unfold new_rmw, singl_rel; split; unfold inclusion; ins; desf; splits; eauto.

exploit (@exists_gstep_update (acts G)); 
eauto 2 with acts.

destruct a as [??[]]; ins; desf.
destruct a0 as [??[]]; ins; desf.
congr.
eapply wf_new_mo_write; try edone.
by apply COHr.
by eauto with acts.
by eapply fresh_to; eauto.

intro GSTEP.

 rewrite <- NEW_RMW in GSTEP.

eapply GMsim_helper with 
    (e:=ThreadEvent.update l (f_to b) to_w v_r v_w released_r 
    (TView.write_released
              (TView.read_tview (Local.tview lc1) l (f_to b) released_r o_r) sc_map l
              to_w released_r o_w) o_r o_w)
    (tid:=tid) (f_to:=f_to) (f_to':=upd f_to a0 to_w) 
    (f_from:=f_from) (f_from':=upd f_from a0 (f_to b))
    (G':= new_G_write (new_G_read G a b) a a0 f_to to_w); eauto.
* red; splits; eauto.
* econs 2. econs; eauto.
* eapply update with (a_r:=a) (a_w:=a0) (G_mid:= new_G_read G a b) ; try done.
  admit.
  eapply new_G_update_coherent with (a_r:=a) (acts:= a:: acts G); try edone.
  eby ins; desc; eapply disjoint_to.

unfold Relation_Operators.union, singl_rel; ins; desc.
destruct H15; try by  apply FRESH; eapply rf_actb; eauto.
desc; subst.

  assert (exists v, val x = Some v); desc.
    by destruct x as [??[]]; try exists v; ins; desf.

assert (exists rel : option View.t,
  Memory.get l (f_to x) mem =
  Some (f_from x, {| Message.val := v; Message.released := rel |}) /\
  sim_mem_helper f_to 
(a :: acts G) (sb G +++ sb_ext (acts G) a) 
          (rmw G) (rf G +++ singl_rel b a) (sc G +++ sc_ext (acts G) a) x (f_from x) v (View.unwrap rel)).
by eapply sim_mem_get;   cdes COHr; cdes WF; eauto.


desc.
  destruct ADD, ADD.
  eapply DISJOINT with (to2:=f_to x); try edone.
  econs; ins; eauto.
  by eapply Time.le_lteq; eauto.
econs; ins; vauto.
specialize (SIMCELL (f_to x) (f_from x) v rel H15); desc.
red in SIMCELL4; desc.
rewrite <- SIMCELL3; done.

* ins; rewrite IdentMap.gsspec in TID0; desf; ins; try edone.
  + pattern to_w at 2; erewrite <- upds with (a:=a0) (b:=to_w). 
    rewrite <- THREAD_ID0.
    eapply tview_step_write; eauto.
  + admit.
* ins; pattern to_w at 2; erewrite <- upds with (b:=to_w).
  eapply sc_map_step_write with (acts:=a:: acts G); eauto.
* admit.
  (* eapply memory_step_update with (prev:=a); try edone. *)
  (* by right. *)
  (* eapply WF_OP_ST. *)
  (* eby rewrite !upds; eapply MemoryFacts.MemoryFacts.write_time_lt. *)
  (* erewrite NO_PROMISES in WRITE; try edone. *)
  (* rewrite !upds; desf. *)
  (* red in SIM_MEMr; desc. *)
  (* specialize (SIM_MEMr l); desc. *)
  (* specialize (SIMCELL0 (f_to b) (f_from b) v_r released_r GET); desc. *)
  (* red in SIMCELL5; desc. *)
  (* assert (b=b0); subst; try done. *)
  (* eapply monotone_injective with (acts:= (a :: acts G)) (f:= f_to); try edone. *)
  (* by right. *)
  (* eby eapply COHr. *)
Admitted.

(******************************************************************************)
(** * Lemmas for fence step  *)
(******************************************************************************)
Definition new_G_fence G a :=
{| acts:=(a :: acts G); sb:=(sb G +++ sb_ext (acts G) a);
           rmw:=(rmw G) ; rf:=(rf G); mo:= (mo G);
           sc:=(Machine.sc G +++ sc_ext (acts G) a) |}.

Lemma exists_gstep_fence acts sb rmw rf mo sc a 
  (WF: Wf acts sb rmw rf mo sc)
  (FRESH: ~ In a acts) (PROPER: is_proper a) (FENCEa: is_fence a):
  gstep acts sb rmw rf mo sc 
      (a :: acts) (sb +++ sb_ext acts a)
      rmw rf mo (sc +++ sc_ext acts a) a a.
Proof.
red; splits; eauto.
by unfold sb_ext, Relation_Operators.union, eqv_rel, seq; eauto 8.
by red; eauto.
by unfold sc_ext, Relation_Operators.union; eauto.
by red; unfold inclusion, Relation_Operators.union; splits; ins; eauto.
red; splits; try done.
- eby eapply wf_new_acts.
- eby eapply wf_new_sb.
- eby eapply wf_new_rmw.
- eapply wf_new_rf; eauto 2 with acts.
- eby eapply wf_new_mo; eauto 2 with acts.
- eby eapply wf_new_sc.
Qed.

Lemma new_G_fence_coherent 
  acts sb rmw rf mo sc a
  (COH: Coherent acts sb rmw rf mo sc)
  or ow (LABEL: lab a = Afence or ow)
  (FRESH: ~ In a acts)
  acts' sb' rmw' rf' mo' sc' 
  (NEW_G: new_G_fence {| acts:=acts; sb:=sb; rmw:=rmw; rf:=rf; mo:=mo; sc:=sc |}
   a = {| acts:=acts'; sb:=sb'; rmw:=rmw'; rf:=rf'; mo:=mo'; sc:=sc' |})
  (GSTEP: gstep acts sb rmw rf mo sc 
               acts' sb' rmw' rf' mo' sc' a a):
  Coherent acts' sb' rmw' rf' mo' sc'.
Proof.
unfold new_G_fence in *; ins; desf.

cdes COH.
red; splits; eauto.
- red; ins.
eapply gstep_hb_a in HB; eauto 2.
eby intro; subst; apply FRESH; eapply mo_acta.
- red; ins.
eapply gstep_hb_a in HB; eauto 2.
eby intro; subst; apply FRESH; eapply mo_acta.
- red; ins.
eapply gstep_hb_a in HB; eauto 2.
eby intro; subst; apply FRESH; eapply rf_actb.
- red; ins.
eapply gstep_hb_a in HB; eauto 2.
eby intro; subst; apply FRESH; eapply rf_actb.

- red; ins.
eapply gstep_hb_a in HB; eauto 3.
eapply gstep_hb_a in HB0; eauto 3.
eby intro; subst; apply FRESH; eapply rf_actb.
intro; subst d; eapply max_elt_hb; eauto.
- red; ins.
eapply gstep_hb_a in HB; eauto 3;
desf; red in SC; unfold sc_ext in *; desf; eauto 3.
all: try eby apply FRESH; eapply hb_acta.
eapply gstep_hb_a in RFHBF0; eauto 2.
by eapply Cscr; eauto.
all: try eby intro; subst; apply FRESH; eapply sc_acta.
all: try eby intro; subst; apply FRESH; eapply rf_actb.
- red; ins.
assert (hb (a :: acts) (sb +++ sb_ext acts a) rmw' rf' e a0 -> hb acts sb rmw' rf' e a0).
  eapply gstep_hb_a; eauto 3.
  eby intro; subst; apply FRESH; eapply mo_acta.

assert (forall c g, sc d g /\ hb (a :: acts) (sb +++ sb_ext acts a) rmw' rf' c d ->
  hb acts sb rmw' rf' c d).
  ins; desc; eapply gstep_hb_a; eauto 3.
  eby intro; subst; apply FRESH; eapply sc_acta.
 desf; red in SC; unfold sc_ext in *; desf.
all: try by eapply Csc; eauto 7.
all: try eby apply FRESH; eapply mo_acta.
all: try by eapply max_elt_hb; eauto.
- eby eapply new_G_non_read_NoPromises.
Qed.

Lemma GMsim_fence ts G tid lang st1 st2 lc1 lc2 threads sc_map mem sc_map' 
  (SIM: GMsim (Configuration.mk threads sc_map mem) {| ts:= ts; exec:= G |})
  (TID: IdentMap.find tid threads =
        Some (existT (fun lang : Language.t => Language.state lang) lang st1, lc1))
  or ow
  (STATE: Language.step lang (Some (ProgramEvent.fence or ow)) st1 st2)
  (LOCAL: Local.fence_step lc1 sc_map or ow lc2 sc_map'):
  exists ax_st', step {| ts:= ts; exec:= G |} ax_st' /\
    GMsim (Configuration.mk 
        (IdentMap.add tid (existT Language.state lang st2, lc2) threads) sc_map' mem)
     ax_st'.
Proof.
generalize (fresh_id (acts G) (Some tid) (Afence or ow)); intro; desc.
unfold GMsim, sim_time in *; desc; ins.
assert (LOCAL':=LOCAL).
destruct LOCAL'; ins; subst.
assert (is_proper a).
  by red; eauto.
exploit exists_gstep_fence; eauto with acts.
intro GSTEP.
eapply GMsim_helper with 
    (e:=ThreadEvent.fence or ow)
    (tid:=tid) (f_to:=f_to) (f_to':=f_to) 
    (f_from:=f_from) (f_from':=f_from)
    (G':= new_G_fence G a); eauto.
- red; splits; eauto.
- econs 2. econs; eauto.
- eapply fence; eauto.
  unfold get_program_event; eauto.
  eapply new_G_fence_coherent; try edone.
- ins.
  rewrite IdentMap.gsspec in TID0; desf; ins; try edone.
  rewrite <- THREAD_ID.
  destruct (classic (is_sc a));
    [ eapply tview_step_scfence|eapply tview_step_rafence]; eauto.
  eby  rewrite THREAD_ID in *; eapply SIM_TVIEW.
  eby eapply WF_OP_ST.
  eby  rewrite THREAD_ID in *; eapply SIM_TVIEW.
- unfold new_G_fence; ins.
  eapply sc_map_step_fence; eauto.
  eby rewrite THREAD_ID in *; eapply SIM_TVIEW.
- eapply memory_step_nonwrite; eauto.
  eapply new_G_fence_coherent; eauto.
  by eauto 3 with acts.
Qed.

(******************************************************************************)
(** * Main theorem  *)
(******************************************************************************)

Lemma small_step_sim :
  forall ax_st op_st (SIM: GMsim op_st ax_st) op_st' e tid
  (OPSTEP: small_step false tid e op_st op_st'),
  exists ax_st', (step ax_st ax_st') /\ GMsim op_st' ax_st'.
Proof.
admit.
(* ins; destruct ax_st as [ts G]. *)
(* destruct OPSTEP; destruct STEP; ins. *)
(* by destruct STEP; ins; desf. *)
(* inv STEP. *)
(* - eapply GMsim_silent; edone. *)
(* - destruct op_st; eapply GMsim_read; edone. *)
(* - destruct op_st; eapply GMsim_write; edone. *)
(* - destruct op_st; eapply GMsim_update; edone. *)
(* - destruct op_st; eapply GMsim_fence; edone. *)
(* - admit. *)
Admitted.

(* lemma about machine step? *)
