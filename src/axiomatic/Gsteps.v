(******************************************************************************)
(** * Definitions of Graph Steps   *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Vbase ExtraRelations.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.
Require Import Time.
Require Import Configuration.
Require Import Memory.
Require Import Thread.
Require Import Commit.

Require Import Gevents.
Require Import model.

Set Implicit Arguments.
Remove Hints plus_n_O.




Section Graph_steps.

Variable acts : list event.
Variable sb : event -> event -> Prop. 
Variable rmw : event -> event -> Prop. 
Variable rf : event -> event -> Prop. 
Variable mo : event -> event -> Prop. 
Variable sc : event -> event -> Prop. 
Variable acts' : list event.  
Variable sb' : event -> event -> Prop. 
Variable rmw' : event -> event -> Prop. 
Variable rf' : event -> event -> Prop. 
Variable mo' : event -> event -> Prop. 
Variable sc' : event -> event -> Prop. 

(******************************************************************************)
(** * Graph inclusion   *)
(******************************************************************************)

Definition graph_inclusion : Prop :=
      << INC_ACT: forall x (IN: In x acts), In x acts' >> /\
      << INC_SB: inclusion sb sb' >> /\
      << INC_RMW: inclusion rmw rmw' >> /\
      << INC_RF: inclusion rf rf' >> /\
      << INC_MO: inclusion mo mo' >> /\
      << INC_SC: inclusion sc sc' >>.

(******************************************************************************)
(** * Lemmas about graph inclusion   *)
(******************************************************************************)

Definition set_mon (f f' : event -> Prop) := 
forall (WF: Wf acts sb rmw rf mo sc) (INC: graph_inclusion) a (H: f a), f' a.

Definition relation_mon (R R' : event -> event -> Prop) := 
forall (WF: Wf acts sb rmw rf mo sc) (INC: graph_inclusion) a b (H: R a b), R' a b.

Lemma seq_mon R1 R1' R2 R2' (A: relation_mon R1 R1') (B:relation_mon R2 R2'): 
 relation_mon (R1;;R2) (R1';;R2').
Proof.
red; ins.
red in WF, INC; desc.
red in H; desc.
exists z; splits; [eapply A|eapply B]; done.
Qed.

Lemma union_mon R1 R1' R2 R2' (A: relation_mon R1 R1') (B:relation_mon R2 R2'): 
 relation_mon (R1 +++ R2) (R1' +++ R2').
Proof.
red; ins.
red in WF, INC; desc.
red in H; desf.
left; apply A; done.
right; apply B; done.
Qed.


Lemma tc_mon R R' (A: relation_mon R R'): relation_mon (tc R) (tc R'). 
Proof.
red; ins.
eapply clos_trans_monotonic.
red in A.
red; intros; apply A; edone.
done.
Qed.

Lemma clos_refl_mon R R' (A: relation_mon R R'): relation_mon (clos_refl R) (clos_refl R'). 
Proof.
red; ins; unfold clos_refl in *; desf; eauto.
Qed.

Lemma eqv_rel_mon f f' (A: set_mon f f'): relation_mon (eqv_rel f) (eqv_rel f'). 
Proof.
red; ins.
unfold eqv_rel in *; desc; eauto.
Qed.

Lemma restr_eq_rel_mon T (f: _ -> T) R R' (A: relation_mon R R'): relation_mon (restr_eq_rel f R) (restr_eq_rel f R'). 
Proof.
red; ins.
unfold restr_eq_rel in *; desc; eauto.
Qed.

Lemma id_set_mon f: set_mon f f. 
Proof.
red; ins.
Qed.

Lemma dom_rel_mon  R R' (A: relation_mon R R'): set_mon (dom_rel R) (dom_rel R').
Proof.
unfold dom_rel; red; ins; desc.
exists y. apply A; done.
Qed.


Hint Resolve
 seq_mon union_mon tc_mon clos_refl_mon eqv_rel_mon 
 restr_eq_rel_mon id_set_mon dom_rel_mon : gstep_mon.

Lemma act_mon : set_mon (fun a => In a acts) (fun a => In a acts').
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma sb_mon : relation_mon sb sb'.
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma rmw_mon : relation_mon rmw rmw'.
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma rf_mon : relation_mon rf rf'.
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma mo_mon : relation_mon mo mo'.
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma sc_mon : relation_mon sc sc'.
Proof. red; ins; red in INC; desc; auto. Qed.
Lemma useq_mon : relation_mon (useq rmw rf) (useq rmw' rf').
Proof. unfold useq; eauto using rmw_mon,rf_mon with gstep_mon. Qed.
Lemma rseq_mon : relation_mon (rseq acts sb rmw rf) (rseq acts' sb' rmw' rf').
Proof. unfold rseq; eauto 15 using act_mon, sb_mon, useq_mon with gstep_mon. Qed.
Lemma rel_mon : relation_mon (rel acts sb rmw rf) (rel acts' sb' rmw' rf').
Proof. unfold rel; eauto 15 using sb_mon, rseq_mon with gstep_mon. Qed.
Lemma sw_mon : relation_mon (sw acts sb rmw rf) (sw acts' sb' rmw' rf').
Proof. unfold sw; eauto 15 using sb_mon, rf_mon, rel_mon with gstep_mon. Qed.
Lemma hb_mon : relation_mon (hb acts sb rmw rf) (hb acts' sb' rmw' rf').
Proof. unfold hb; eauto 15 using sb_mon, sw_mon with gstep_mon. Qed.
Lemma hbsc_mon : relation_mon (hbsc acts sb rmw rf sc) (hbsc acts' sb' rmw' rf' sc').
Proof. unfold hbsc; eauto 15 using sc_mon, hb_mon with gstep_mon. Qed.
Lemma ur_mon : relation_mon (ur_relation acts sb rmw rf sc) (ur_relation acts' sb' rmw' rf' sc').
Proof. unfold ur_relation; eauto 15 using act_mon, rf_mon, hb_mon, hbsc_mon with gstep_mon. Qed.
Lemma rw_mon : relation_mon (rw_relation acts sb rmw rf sc) (rw_relation acts' sb' rmw' rf' sc').
Proof. unfold rw_relation; eauto 15 using ur_mon, act_mon, rf_mon, hb_mon with gstep_mon. Qed.
Lemma scr_mon : relation_mon (sc_relation acts sb rmw rf sc) (sc_relation acts' sb' rmw' rf' sc').
Proof. unfold sc_relation; eauto 15 using rw_mon, act_mon, rf_mon, hb_mon, hbsc_mon with gstep_mon. Qed.
Lemma m_rel_ur_mon l : relation_mon (m_rel_ur acts sb rmw rf sc l) (m_rel_ur acts' sb' rmw' rf' sc' l).
Proof. unfold m_rel_ur, m_rel. eauto 15 using act_mon,ur_mon,rel_mon with gstep_mon. Qed.
Lemma m_rel_rw_mon l : relation_mon (m_rel_rw acts sb rmw rf sc l) (m_rel_rw acts' sb' rmw' rf' sc' l).
Proof. unfold m_rel_rw, m_rel. eauto 15 using act_mon,rw_mon,rel_mon with gstep_mon. Qed.
Lemma m_rel_sc_mon l : relation_mon (m_rel_sc acts sb rmw rf sc l) (m_rel_sc acts' sb' rmw' rf' sc' l).
Proof. unfold m_rel_sc, m_rel. eauto 15 using act_mon,scr_mon,rel_mon with gstep_mon. Qed.

Lemma c_cur_ur_mon i x : set_mon (c_cur_ur acts sb rmw rf sc i x) (c_cur_ur acts' sb' rmw' rf' sc' i x).
Proof. unfold c_cur_ur, c_cur ;eauto 20 using act_mon,ur_mon with gstep_mon. Qed.
Lemma c_cur_rw_mon i x : set_mon (c_cur_rw acts sb rmw rf sc i x) (c_cur_rw acts' sb' rmw' rf' sc' i x).
Proof. unfold c_cur_rw, c_cur ;eauto 20 using act_mon,rf_mon,rel_mon,rw_mon with gstep_mon. Qed.
Lemma c_cur_sc_mon i x : set_mon (c_cur_sc acts sb rmw rf sc i x) (c_cur_sc acts' sb' rmw' rf' sc' i x).
Proof. unfold c_cur_sc, c_cur ;eauto 20 using act_mon,rf_mon,rel_mon,scr_mon with gstep_mon. Qed.

Lemma c_acq_ur_mon i x : set_mon (c_acq_ur acts sb rmw rf sc i x) (c_acq_ur acts' sb' rmw' rf' sc' i x).
Proof. unfold c_acq_ur, c_acq ;eauto 20 using m_rel_ur_mon,rf_mon with gstep_mon. Qed.
Lemma c_acq_rw_mon i x : set_mon (c_acq_rw acts sb rmw rf sc i x) (c_acq_rw acts' sb' rmw' rf' sc' i x).
Proof. unfold c_acq_rw, c_acq ;eauto 20 using m_rel_rw_mon,rf_mon with gstep_mon. Qed.
Lemma c_acq_sc_mon i x : set_mon (c_acq_sc acts sb rmw rf sc i x) (c_acq_sc acts' sb' rmw' rf' sc' i x).
Proof. unfold c_acq_sc, c_acq ;eauto 20 using m_rel_sc_mon,rf_mon with gstep_mon. Qed.


Hint Resolve
 act_mon sb_mon rmw_mon rf_mon mo_mon sc_mon
 useq_mon rseq_mon rel_mon sw_mon hb_mon hbsc_mon
 ur_mon rw_mon scr_mon
 c_cur_ur_mon c_cur_rw_mon c_cur_sc_mon 
 c_acq_ur_mon c_acq_rw_mon c_acq_sc_mon : gstep_mon.
(* ADD *)

(******************************************************************************)
(** * Graph step   *)
(******************************************************************************)

Definition gstep a : Prop :=
      << FRESH: ~ In a acts >> /\
      << ACT_STEP: acts' = a :: acts >> /\
      << SB_STEP: forall x y, sb' x y <-> sb x y \/ (thread x = thread a /\ ~(x=a) /\ y = a) >> /\
      << RMW_STEP: rmw' <--> rmw >> /\
      << SC_AT_END: forall (SCa: is_sc a) x (SCa: is_sc x), sc' x a >> /\
      << INC: graph_inclusion >> /\
      << COH: Coherent acts'  sb' rmw' rf' mo' sc' >>.

(******************************************************************************)
(** * Basics    *)
(******************************************************************************)

Lemma gstep_coh  a (GSTEP: gstep a) : Coherent acts'  sb' rmw' rf' mo' sc'.
Proof. cdes GSTEP; done. Qed.

Lemma gstep_inc  a (GSTEP: gstep a) : graph_inclusion.
Proof. cdes GSTEP; cdes COH; done. Qed.

Hint Resolve gstep_coh gstep_inc coh_wf.

(******************************************************************************)
(** * Added node is a dead end   *)
(******************************************************************************)

Definition gstep_de (R : relation event):=
  forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (H: R a x), False.

Definition gstep_wde (R: relation event):=
  forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (H: R a x), a=x.

Lemma gstep_eqv_rel_wde f : gstep_wde (eqv_rel f).
Proof.
red; ins; eauto.
red in H; desc; auto.
Qed.

Lemma gstep_restr_eq_rel_wde T (f: _ -> T) R (A: gstep_wde R): gstep_wde (restr_eq_rel f R). 
Proof.
red; ins. unfold restr_eq_rel in *; desc; eauto.
Qed.

Lemma gstep_restr_eq_rel_de T (f: _ -> T) R (A: gstep_de R): gstep_de (restr_eq_rel f R). 
Proof.
red; ins. unfold restr_eq_rel in *; desc; eauto.
Qed.

Lemma gstep_de_wde R (H: gstep_de R ) : gstep_wde R.
Proof.
red; ins; exfalso; eauto.
Qed.

Lemma gstep_de_seq_R_de T R (H: gstep_de T) : gstep_de (T;;R).
Proof.
red; ins; unfold seq in *; desc.
eby eapply H.
Qed.

Lemma gstep_wde_seq_de_de T R (H_T: gstep_wde T) (H_R: gstep_de R): gstep_de (T;;R).
Proof.
red; ins; unfold seq in *; desc.
apply H_T in H; eauto.
subst.
eapply H_R; try edone.
Qed.

Lemma gstep_wde_seq_wde_wde T R (H_T: gstep_wde T) (H_R: gstep_wde R): gstep_wde (T;;R).
Proof.
red; ins; unfold seq in *; desc.
apply H_T in H; eauto.
subst.
eapply H_R; try edone.
Qed.

Lemma gstep_wde_union_wde_wde T R (H_T: gstep_wde T) (H_R: gstep_wde R): gstep_wde (T +++ R).
Proof.
red; ins; unfold seq in *; desc.
red in H; desf. 
eby eapply H_T.
eby eapply H_R.
Qed.

Lemma gstep_de_union_de_de T R (H_T: gstep_de T) (H_R: gstep_de R): gstep_de (T +++ R).
Proof.
red; ins; unfold seq in *; desc.
red in H; desf. 
eby eapply H_T.
eby eapply H_R.
Qed.

Lemma gstep_clos_refl_wde_wde R (H: gstep_wde R) : gstep_wde (clos_refl R).
Proof.
red; ins.
destruct H0; eauto.
Qed.

Lemma gstep_clos_refl_de_wde R (H: gstep_de R) : gstep_wde (clos_refl R).
Proof.
apply gstep_clos_refl_wde_wde; apply gstep_de_wde; done.
Qed.

Lemma gstep_tc_de_de R (H: gstep_de R) : gstep_de (tc R).
Proof.
red; ins. apply clos_trans_t1n_iff in H0.
destruct H0; eauto.
Qed.

Hint Resolve
 gstep_eqv_rel_wde gstep_restr_eq_rel_de gstep_restr_eq_rel_wde gstep_de_wde
 gstep_de_seq_R_de gstep_wde_seq_de_de gstep_wde_seq_wde_wde gstep_wde_union_wde_wde
 gstep_de_union_de_de gstep_clos_refl_wde_wde gstep_tc_de_de : gstep_de.

Lemma gstep_sb_de : gstep_de sb'.
Proof.
red; ins; cdes GSTEP; cdes INC.
apply SB_STEP in H; desf; try edone.
cdes COH; cdes WF; cdes WF_SB; apply SB_ACTa in H; edone.
Qed.

Lemma gstep_rmw_de : gstep_de rmw'.
Proof.
red; ins; cdes GSTEP; cdes INC.
apply RMW_STEP in H.
apply FRESH.
red in COH; desc.
eapply rmw_acta; edone.
Qed.

Lemma gstep_rf_de : gstep_de rf'.
Proof.
red; ins; cdes COH; cdes WF; cdes WF_RF.
cdes GSTEP; cdes INC.
cdes COH0; cdes WF0; cdes WF_RF0.
destruct (classic (x=a)) as [|N]; subst.
eapply irr_rf with (rf:=rf'); try edone.
assert(exists z, rf z x).
  eapply RF_TOT.
  specialize (RF_ACTb0 a x H); destruct RF_ACTb0; try done.
  by exfalso; eauto.
  specialize (RF_DOMb0 a x H); done.
desc.
assert (H1: z=a). 
  apply INC_RF in H0; eapply RF_FUN0; edone.
apply RF_ACTa in H0.
rewrite H1 in *.
auto.
Qed.

Lemma gstep_sc_de : gstep_de sc'.
Proof.
red; ins; cdes GSTEP; cdes INC; cdes COH0; cdes WF; cdes WF_SC.
by eapply SC_IRR; apply SC_AT_END; eauto.
Qed.

Lemma gstep_useq_de : gstep_de (useq rmw' rf').
Proof. unfold useq; eauto using gstep_rf_de with gstep_de. Qed. 
Lemma gstep_rseq_wde : gstep_wde (rseq acts' sb' rmw' rf').
Proof. unfold rseq; eauto 11 using gstep_sb_de, gstep_useq_de with gstep_de. Qed. 
Lemma gstep_rel_wde : gstep_wde (rel acts' sb' rmw' rf').
Proof. unfold rel; eauto 11 using gstep_sb_de, gstep_rseq_wde with gstep_de. Qed. 
Lemma gstep_sw_de : gstep_de (sw acts' sb' rmw' rf').
Proof. unfold sw; eauto 11 using gstep_rel_wde, gstep_rf_de with gstep_de. Qed. 
Lemma gstep_hb_de : gstep_de (hb acts' sb' rmw' rf').
Proof. unfold hb; eauto 11 using gstep_sb_de, gstep_sw_de with gstep_de. Qed. 
Lemma gstep_hbsc_de : gstep_de (hbsc acts' sb' rmw' rf' sc').
Proof. unfold hbsc; eauto 11 using gstep_hb_de, gstep_sc_de with gstep_de. Qed. 
Lemma gstep_ur_wde : gstep_wde (ur_relation acts' sb' rmw' rf' sc').
Proof. unfold ur_relation; eauto 11 using gstep_rf_de, gstep_hbsc_de, gstep_hb_de with gstep_de. Qed. 
Lemma gstep_rw_wde : gstep_wde (rw_relation acts' sb' rmw' rf' sc').
Proof. unfold rw_relation; eauto 11 using gstep_ur_wde, gstep_rf_de, gstep_hb_de with gstep_de. Qed. 
Lemma gstep_scr_wde : gstep_wde (sc_relation acts' sb' rmw' rf' sc').
Proof. unfold sc_relation; eauto 11 using gstep_rw_wde, gstep_rf_de, gstep_hbsc_de, gstep_hb_de with gstep_de. Qed. 

Hint Resolve
  gstep_sb_de  gstep_rmw_de  gstep_rf_de gstep_sc_de  gstep_useq_de gstep_rseq_wde 
  gstep_rel_wde gstep_sw_de gstep_hb_de gstep_hbsc_de gstep_ur_wde 
  gstep_rw_wde  gstep_scr_wde : gstep_de.

(******************************************************************************)
(** * New edges only to the added event    *)
(******************************************************************************)

Definition gstep_a (R R': relation event):=
  forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x y (NEQ: y <> a) (H: R' x y), R x y.

Lemma gstep_clos_refl_a R R' (H: gstep_a R R') : gstep_a (clos_refl R) (clos_refl R').
Proof.
red; ins.
destruct H0.
by subst; eauto.
by right; eauto.
Qed.

Lemma gstep_a_union_a_a R R' T T' (H2: gstep_a T T') (H3: gstep_a R R'): 
  gstep_a (R +++ T) (R' +++ T').
Proof.
red; ins.
destruct H; desc.
left; eapply H3; edone.
right; eapply H2; edone.
Qed.

Lemma gstep_a_seq_wde_a_a R R' T T' (H1: gstep_wde T') (H2: gstep_a T T') (H3: gstep_a R R'): 
  gstep_a (R;;T) (R';;T').
Proof.
red; ins.
destruct H; desc.
exists x0; split.
eapply H3; try edone.
intro; subst; apply NEQ, eq_sym, H1; eauto.
eby eapply H2.
Qed.

Lemma gstep_tc_wde_a_a R R' (H1: gstep_wde R') (H2: gstep_a R R'): gstep_a (tc R) (tc R').
Proof.
  red; ins.
rewrite clos_trans_tn1_iff in H.
induction H.
- apply t_step.
eapply H2; eauto.
- apply t_trans with (y:=y).
rewrite <- clos_trans_tn1_iff in H0.
apply IHclos_trans_n1.
intro; subst.
apply NEQ.
symmetry; apply H1; try done.
apply t_step.
eapply H2; eauto.
Qed.

Lemma gstep_eqv_rel_a :
  gstep_a (eqv_rel (fun a : event => In a acts))
          (eqv_rel (fun a : event => In a acts')).
Proof.
  unfold eqv_rel, gstep_a, gstep; ins; desf; ins; desf; exfalso; eauto.
Qed.

Lemma gstep_id_a P : gstep_a P P.
Proof.
  done.
Qed.

Lemma gstep_restr_eq_rel_loc_a R R' (H: gstep_a R R'): gstep_a (restr_eq_rel loc R) (restr_eq_rel loc R').
Proof.
unfold restr_eq_rel, gstep_a in *.
ins; desf; eauto.
Qed.

Hint Resolve 
gstep_clos_refl_a gstep_a_seq_wde_a_a gstep_eqv_rel_a gstep_a_union_a_a
gstep_id_a gstep_tc_wde_a_a gstep_restr_eq_rel_loc_a: gstep_a.

Lemma gstep_sb_a : gstep_a sb sb'.
Proof.
red; ins; cdes GSTEP; cdes INC.
apply SB_STEP in H; desf; try edone.
Qed.

Lemma gstep_rmw_a : gstep_a rmw rmw'.
Proof.
red; ins; cdes GSTEP; cdes INC.
apply RMW_STEP; done.
Qed.

Lemma gstep_rf_a : gstep_a rf rf'.
Proof.
red; ins; cdes GSTEP; cdes INC; cdes COH; cdes WF; cdes WF_RF; cdes COH0; cdes WF0; cdes WF_RF0.
rewrite ACT_STEP in *.
assert(exists z, rf z y).
  eapply RF_TOT.
  specialize (RF_ACTb0 x y H); destruct RF_ACTb0; try done.
  by exfalso; eauto.
  specialize (RF_DOMb0 x y H); done.
desc.
assert (H1: z=x); try eapply RF_FUN0; eauto.
rewrite H1 in *; done.
Qed.

Lemma gstep_sc_a : gstep_a sc sc'.
Proof.
red; ins; cdes GSTEP; cdes INC; unnw.
cdes COH0; cdes WF; cdes WF_SC.
assert (x<>a).
  intro H1. rewrite H1 in *. eby eapply gstep_sc_de.
destruct (classic (x=y)) as [E|N].
  by rewrite E in *; exfalso; eapply SC_IRR; edone.
cdes COH; cdes WF0; eapply WF_SC0 in N; splits; eauto; rewrite ACT_STEP in *.
- destruct N; try done.
  edestruct SC_IRR; eauto.
- specialize (SC_ACTa _ _ H).
  destruct SC_ACTa; try done.
  exfalso; auto.
- specialize (SC_ACTb _ _ H).
  destruct SC_ACTb; try done.
  exfalso; apply NEQ; done.
Qed.

Lemma gstep_useq_a : gstep_a (useq rmw rf) (useq rmw' rf').
Proof. unfold useq; eauto 11 using gstep_rmw_a,gstep_rf_a with gstep_a gstep_de. Qed. 
Lemma gstep_rseq_a : gstep_a (rseq acts sb rmw rf) (rseq acts' sb' rmw' rf').
Proof. unfold rseq; eauto 30 using gstep_useq_a,gstep_sb_a with gstep_a gstep_de. Qed.
Lemma gstep_rel_a : gstep_a (rel acts sb rmw rf) (rel acts' sb' rmw' rf').
Proof. unfold rel; eauto 30 using gstep_rseq_a,gstep_sb_a with gstep_a gstep_de. Qed.
Lemma gstep_sw_a : gstep_a (sw acts sb rmw rf) (sw acts' sb' rmw' rf').
Proof. unfold sw; eauto 30 using gstep_rel_a,gstep_rf_a,gstep_sb_a with gstep_a gstep_de. Qed.
Lemma gstep_hb_base_a : gstep_a (sb +++ sw acts sb rmw rf) (sb' +++ sw acts' sb' rmw' rf').
Proof. eauto using gstep_sb_a,gstep_sw_a with gstep_a gstep_de. Qed.
Lemma gstep_hb_a : gstep_a (hb acts sb rmw rf) (hb acts' sb' rmw' rf').
Proof. unfold hb; eauto using gstep_hb_base_a with gstep_a gstep_de. Qed.
Lemma gstep_hbsc_a : gstep_a (hbsc acts sb rmw rf sc) (hbsc acts' sb' rmw' rf' sc').
Proof. unfold hbsc; eauto 15 using gstep_sc_a, gstep_hb_a with gstep_a gstep_de. Qed.
Lemma gstep_ur_a : gstep_a (ur_relation acts sb rmw rf sc) (ur_relation acts' sb' rmw' rf' sc').
Proof. unfold ur_relation; eauto 30 using gstep_hbsc_a,gstep_hb_a,gstep_rf_a with gstep_a gstep_de. Qed.
Lemma gstep_rw_a : gstep_a (rw_relation acts sb rmw rf sc) (rw_relation acts' sb' rmw' rf' sc').
Proof. unfold rw_relation; eauto 30 using gstep_ur_a,gstep_hb_a,gstep_rf_a with gstep_a gstep_de. Qed.
Lemma gstep_scr_a : gstep_a (sc_relation acts sb rmw rf sc) (sc_relation acts' sb' rmw' rf' sc').
Proof. unfold sc_relation; eauto 30 using gstep_rw_a,gstep_hbsc_a,gstep_hb_a,gstep_rf_a with gstep_a gstep_de. Qed.
Lemma gstep_c_cur_ur_relation_a i l: gstep_a (c_cur i l (ur_relation acts sb rmw rf sc)) (c_cur i l (ur_relation acts' sb' rmw' rf' sc')).
Proof. unfold c_cur; eauto 30 using gstep_ur_a with gstep_a gstep_de. Qed.
Lemma gstep_c_cur_rw_relation_a i l: gstep_a (c_cur i l (rw_relation acts sb rmw rf sc)) (c_cur i l (rw_relation acts' sb' rmw' rf' sc')).
Proof. unfold c_cur; eauto 30 using gstep_rw_a with gstep_a gstep_de. Qed.
Lemma gstep_c_cur_sc_relation_a i l: gstep_a (c_cur i l (sc_relation acts sb rmw rf sc)) (c_cur i l (sc_relation acts' sb' rmw' rf' sc')).
Proof. unfold c_cur; eauto 30 using gstep_scr_a with gstep_a gstep_de. Qed.


(* Lemma gstep_m_rel_ur_a l: gstep_a (m_rel_ur acts sb rmw rf sc l) (m_rel_ur acts' sb' rmw' rf' sc' l).
Proof. unfold c_cur; eauto 30 using gstep_ur_a with gstep_a gstep_de. Qed.
 *)

Hint Resolve 
gstep_sb_a gstep_rmw_a  gstep_rf_a  gstep_sc_a gstep_useq_a gstep_rseq_a 
 gstep_rel_a  gstep_sw_a gstep_hb_base_a gstep_hb_a gstep_hbsc_a
 gstep_ur_a gstep_rw_a gstep_scr_a
 gstep_c_cur_ur_relation_a gstep_c_cur_rw_relation_a gstep_c_cur_sc_relation_a: gstep_a.

Lemma gstep_dom_rel_a R R' (H: gstep_a R R') : 
  forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (IN: dom_rel R' x), dom_rel R x \/ R' x a.
Proof.
ins.
red in IN; desc.
destruct (classic (y=a)).
- subst; auto. 
- left; eexists; eapply H; edone.
Qed.

Hint Resolve gstep_dom_rel_a : gstep_a.

Lemma gstep_c_cur_ur_a i l : 
forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (IN: c_cur_ur acts' sb' rmw' rf' sc' i l x), 
c_cur_ur acts sb rmw rf sc i l x \/ c_cur i l (ur_relation acts' sb' rmw' rf' sc') x a.
Proof. eauto using gstep_dom_rel_a, gstep_c_cur_ur_relation_a. Qed.

Lemma gstep_c_cur_rw_a i l : 
forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (IN: c_cur_rw acts' sb' rmw' rf' sc' i l x), 
c_cur_rw acts sb rmw rf sc i l x \/ c_cur i l (rw_relation acts' sb' rmw' rf' sc') x a.
Proof. eauto using gstep_dom_rel_a, gstep_c_cur_rw_relation_a. Qed.

Lemma gstep_c_cur_sc_a i l : 
forall a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
           x (IN: c_cur_sc acts' sb' rmw' rf' sc' i l x), 
c_cur_sc acts sb rmw rf sc i l x \/ c_cur i l (sc_relation acts' sb' rmw' rf' sc') x a.
Proof. eauto using gstep_dom_rel_a, gstep_c_cur_sc_relation_a. Qed.


(******************************************************************************)
(** * Various lemmas about gstep   *)
(******************************************************************************)

Lemma gstep_read_rf
  a l v o_a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  (READ: lab a = Aload l v o_a) : 
  (exists b, << RFb: (rf' b a) >> /\ << INb: In b acts >> /\ 
             << LABb: exists o_b, lab b = Astore l v o_b >>).
Proof.
cdes GSTEP; cdes INC; unnw.
cdes COH0; cdes WF; cdes WF_MO.
cdes COH; cdes WF; cdes WF_MO.
desf; ins.
cdes WF_RF; cdes WF_MO; cdes INC.
exploit (RF_TOT a). by left; eauto. by red; rewrite READ; done.
intros; desc. exploit rf_lv; try edone; intro; desc.
eexists _. splits; eauto.
apply RF_ACTa in x0; destruct x0; eauto.
exfalso; subst; destruct (lab a0); ins.
Qed.

Lemma gstep_mo 
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x y (NEQx: x <> a) (NEQy: y <> a) (MO: mo' x y): mo x y.
Proof.
cdes GSTEP; cdes INC; unnw.
cdes COH0; cdes WF; cdes WF_MO.
specialize (MO_LOC _ _ MO).
destruct (classic (x=y)) as [E|N].
  by rewrite E in *; exfalso; eapply MO_IRR; edone.
cdes COH; cdes WF0; eapply WF_MO0 in N; splits; eauto; rewrite ACT_STEP in *.
- destruct N; try done.
  edestruct MO_IRR; eauto.
- specialize (MO_ACTa _ _ MO).
  destruct MO_ACTa; try done.
  exfalso; apply NEQx; done.
- specialize (MO_ACTb _ _ MO).
  destruct MO_ACTb; try done.
  exfalso; apply NEQy; done.
Qed.

Lemma gstep_non_write_mo 
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  (NOT_WRITE: ~ is_write a) : mo <--> mo'.
Proof.
cdes GSTEP; cdes INC.
split; auto.
intros x y H.
cdes COH0; cdes WF; cdes WF_MO.
specialize (MO_DOMa _ _ H); red in MO_DOMa.
specialize (MO_DOMb _ _ H); red in MO_DOMb.
unfold is_write in *.
eapply gstep_mo; try edone;
by intro A; rewrite A in *; edestruct (lab a); ins.
Qed.


Lemma gstep_non_sc_sc 
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  (NON_SC: ~ is_sc a) : sc <--> sc'.
Proof.
cdes GSTEP; cdes INC.
split; auto.
intros x y H.
cdes COH0; cdes WF; cdes WF_SC.
specialize (SC_DOMa _ _ H); red in SC_DOMa.
specialize (SC_DOMb _ _ H); red in SC_DOMb.
unfold is_sc in *.
eapply gstep_sc_a; try edone;
by intro A; rewrite A in *; edestruct (lab a); ins.
Qed.

Lemma gstep_rf_rmw
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) :
  rf ;; rmw <--> rf' ;; rmw'.
Proof.
  split; ins; desf.
- unfold inclusion; intros; eapply seq_mon; eauto with gstep_mon. 
- eauto with gstep_mon.
  intros x y H.
  destruct H; desc.
  exists x0; split.
  * eapply gstep_rf_a; try edone.
    intro; subst; eapply gstep_rmw_de; try edone.
  * cdes GSTEP; apply RMW_STEP; done.
Qed.

Lemma gstep_useq
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) :
  useq rmw rf <--> useq rmw' rf'.
Proof.
split; ins; desf. 
by unfold inclusion; eauto using useq_mon.
intros x y H.
apply clos_trans_t1n_iff in H.
induction H.
- apply t_step; eapply gstep_rf_rmw; edone.
- eapply t_trans with (y:=y).
  apply t_step; eapply gstep_rf_rmw; edone.
  red in IHclos_trans_1n; done.
Qed.

(******************************************************************************)
(** * More lemmas about gstep   *)
(******************************************************************************)

Lemma gstep_sb
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) :
  sb' <--> sb +++ (fun x y => In x acts /\ thread x = thread y) ;; eqv_rel (eq a).
Proof.
cdes GSTEP; cdes INC.
cdes COH0; cdes WF; cdes WF_SB.
split; red; ins; unfold union, seq, eqv_rel in *.
exploit SB_ACTa; try edone; 
exploit SB_ACTa; try edone;
exploit SB_TID; try edone; 
rewrite SB_STEP in *; desf; ins; desf; try subst a; try subst x; eauto 8;
try by exfalso; eauto 1.
rewrite SB_STEP; desf; eauto.
subst y; right; splits; eauto; congruence.
Qed.

Lemma gstep_rmw
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) :
  rmw' <--> rmw.
Proof.
apply GSTEP.
Qed.

Lemma gstep_rf
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) b (RFb: rf' b a) :
  rf' <--> rf +++ (fun x y => x = b /\ y = a).
Proof.
split; unfold union; red; ins.
  destruct (classic (y = a)); subst.
    by cdes GSTEP; cdes INC; cdes COH0; cdes WF; cdes WF_RF; eauto.
  by eapply gstep_rf_a in H; vauto.
desf; eauto using rf_mon.
Qed.

Lemma restr_eq_union:
  forall (X : Type) (rel rel' : relation X) (B : Type) (f : X -> B),
  restr_eq_rel f (rel +++ rel') <--> 
  restr_eq_rel f rel +++
  restr_eq_rel f rel'.
Admitted.

Lemma restr_eq_seq_eqv_rel:
  forall (X : Type) (rel : relation X) (B : Type) (f : X -> B) dom,
  restr_eq_rel f (rel ;; eqv_rel dom) <--> 
  restr_eq_rel f rel ;; eqv_rel dom.
Admitted.

Lemma clos_refl_union1:
  forall (X : Type) (rel rel' : relation X),
  clos_refl (rel +++ rel') <--> 
  clos_refl rel +++ rel'.
Admitted.

Lemma seq2:
  forall (X : Type) (rel rel' rel'' : relation X) (EQ: rel ;; rel' <--> rel'') r,
  rel ;; rel' ;; r <--> rel'' ;; r.
Proof.
  ins; rewrite <- EQ, seqA; vauto.
Qed.

Lemma gstep_in_acts   a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) : 
  eqv_rel ((In (A:=event))^~ acts') <--> 
  eqv_rel ((In (A:=event))^~ acts) +++ eqv_rel (eq a).
Admitted.

Lemma gstep_a_acts 
  a (GSTEP: gstep a) :
  eqv_rel (eq a);; eqv_rel (fun a => In a acts) <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
  cdes GSTEP; eauto.
Qed.

Ltac relsimp := 
  repeat first 
  [rewrite unionFr | rewrite unionrF | rewrite seqFr | rewrite seqrF 
  | rewrite restr_eq_seq_eqv_rel 
  | rewrite restr_eq_union 
  | rewrite clos_refl_union1 
  | rewrite seqA
  | rewrite seq_union_l | rewrite seq_union_r ]; try done; try reflexivity.

Lemma gstep_a_write 
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) b (RFb: rf' b a) :
  eqv_rel (eq a);; eqv_rel is_write <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
  eapply rf_to_non_read with (acts:=acts'); eauto.
intro; unfold is_read,is_write in *; destruct (lab y); ins.
Qed.

Lemma seq_eq_contra A (dom: A -> Prop) a (GOAL: ~ dom a) :
  eqv_rel (eq a);; eqv_rel dom <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
Qed.

Lemma seq_eq_contra2 A (dom: A -> Prop) a (GOAL: ~ dom a) r :
  eqv_rel (eq a);; eqv_rel dom ;; r <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
Qed.


Lemma gstep_rseq
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) b (RFb: rf' b a) :
  rseq acts' sb' rmw' rf' <--> 
  rseq acts sb rmw rf.
Proof.
unfold rseq; rewrite <- gstep_useq, gstep_in_acts, gstep_sb; eauto; relsimp.
repeat (rewrite (seq2 (gstep_a_write COH GSTEP RFb)); relsimp).
Qed.

Lemma gstep_rel
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) b (RFb: rf' b a) :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf.
Proof.
unfold rel; rewrite gstep_rseq, gstep_sb; eauto; relsimp.
unfold rseq at 3; rewrite (seq2 (gstep_a_acts GSTEP)); relsimp.
Qed.

Lemma gstep_sw
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) b (RFb: rf' b a) :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ rel acts sb rmw rf ;; (fun x y => x = b /\ y = a) ;; eqv_rel is_ra.
Proof.
unfold sw; rewrite gstep_rel, gstep_rf, gstep_sb; eauto; relsimp.
rewrite seq_eq_contra2; relsimp.
Admitted.

(*
Lemma gstep_sw_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  b (RFb: (rf' b a)) x (SW: sw acts' sb' rmw' rf' x a): rel acts sb rmw rf x b /\ is_ra a.
Proof.
unfold sw, seq, eqv_rel in *; desc.
subst.
destruct SW1; desc; subst.
- assert (z=b). eapply gstep_rf_b; edone.
  subst; split; try done.
  eapply gstep_rel_a; try edone.
  intro; subst; eapply irr_rf; cdes GSTEP; cdes COH0; cdes WF; edone.
- exfalso.
  cdes GSTEP; cdes COH0; cdes WF; cdes WF_RF.
  specialize (RF_DOMb b a RFb).
  unfold is_rfence, is_read in *; destruct (lab a); ins.
Qed.

Lemma gstep_hb_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) (HB: hb acts' sb' rmw' rf' x a): 
  exists c, (clos_refl (hb acts sb rmw rf)) x c /\ 
   (In c acts /\ thread c = thread a \/ rel acts sb rmw rf c b /\ is_ra a).
Proof.
cdes GSTEP.
apply t_rt_step in HB; desc.
exists z; split.
  rewrite clos_refl_transE in HB; desf; vauto; right.
  eapply gstep_hb_a; try rewrite ACT_STEP; eauto.
  by intro; subst a; eapply irr_hb, t_step, HB0; eauto. 
destruct HB0; eauto using gstep_sb_b, gstep_sw_b.
Qed.

Lemma gstep_ur_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) (UR: ur_relation acts' sb' rmw' rf' sc' x a)
  (NEQ: x <> a) : exists c, (ur_relation acts sb rmw rf sc) x c /\ 
   (In c acts /\ thread c = thread a \/ rel acts sb rmw rf c b /\ is_ra a).
Proof.
cut ((ur_relation acts' sb' rmw' rf' sc' ;; hb acts' sb' rmw' rf') x a). 
{ cdes GSTEP.
  intro X; destruct X as (? & ? & X); eapply gstep_hb_b in X; try edone; desc.
  eexists; split; [|edone].
  eapply gstep_ur_a in H; eauto.
  by destruct X; try subst x0; eauto using ur_hb.
  intro; subst x0; destruct X; try subst a.
  by apply FRESH; desf; eapply rel_acta; eauto.
  by apply FRESH; desf; eapply hb_acta; eauto.
}
{
unfold ur_relation in *.
apply seqA in UR; red in UR; desc. 
red in UR0; desf. 
destruct UR as [z [UR1 UR2]]; desc.
red in UR1; desc; subst.
red in UR2; desf; subst; try by exfalso; auto.
red in UR2; desc.
exfalso; eapply rf_to_non_read with (acts:=acts'); eauto;
unfold seq, eqv_rel in *; desc; subst; eauto with acts.
eexists; splits; try edone.
apply seqA.
eexists; eauto.
}
Qed.

Lemma gstep_rw_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) (RW: rw_relation acts' sb' rmw' rf' sc' x a)
  (NEQa: x <> a) (NEQb: x <> b) : exists c, (rw_relation acts sb rmw rf sc) x c /\ 
   (In c acts /\ thread c = thread a \/ rel acts sb rmw rf c b /\ is_ra a).
Proof.
destruct RW as [UR|RW].
eapply gstep_ur_b in UR; eauto; desc; eauto using ur_in_rw.
unfold seq, eqv_rel, clos_refl in *; desf.
- assert (z=b).
  cdes GSTEP; cdes COH0; cdes WF; cdes WF_RF; eapply RF_FUN; edone.
  eby subst; exfalso.
- eapply gstep_rf_a in RW0; try edone.
  eapply gstep_hb_b in RW1; try edone.
  desc.
  exists c; splits; try done.
  assert (In z acts).
    by eapply rf_acta; eauto.
  right; unfold seq, eqv_rel in *; eauto 10.
  intro; subst.
  eapply irr_hb with (acts:=acts'); eauto.
Qed.

Lemma gstep_scr_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) (SC: sc_relation acts' sb' rmw' rf' sc' x a)
  (NEQa: x <> a) (NEQb: x <> b) : 
   is_sc a \/ exists c, (sc_relation acts sb rmw rf sc) x c /\ 
   (In c acts /\ thread c = thread a \/ rel acts sb rmw rf c b /\ is_ra a).
Proof.
destruct (classic (is_sc a)); eauto. right.
destruct SC as [RW|SC].
eapply gstep_rw_b in RW; eauto; desc; eauto using rw_in_sc.
unfold seq, eqv_rel in *; desc.
destruct SC2; subst; try by exfalso; apply H; eapply hbsc_domb with (acts:=acts'); eauto.
eapply gstep_hb_b in H0; try edone.
desc; exists c; splits; try done.
eapply gstep_hbsc_a in SC1; eauto.
destruct SC0; subst.
  assert (In z0 acts).
    by eapply hbsc_acta; eauto.
red; unfold seq, eqv_rel,clos_refl; right; eauto 15.

exists z0. splits; eauto. exists z0; splits; eauto.

splits; eauto.
eau

unfold clos_refl; eauto 20.
red. eauto 10.
Qed.

(******************************************************************************)
(** * More lemmas about gstep   *)
(******************************************************************************)

Lemma gstep_new_ur0
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l x (CUR: c_cur_ur acts sb rmw rf sc (thread a) l x) : 
    ur_relation acts' sb' rmw' rf' sc' x a.
Proof.
unfold c_cur_ur, dom_rel, c_cur, eqv_rel, seq in *; desc; subst.
eapply ur_hb.
eapply ur_mon; eauto.
apply sb_in_hb; cdes GSTEP;  apply SB_STEP.
right; splits; try done.
intro; subst.
apply FRESH; eapply ur_actb; eauto.
Qed.

Lemma gstep_new_rw0
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l x (CUR: c_cur_rw acts sb rmw rf sc (thread a) l x) : 
    rw_relation acts' sb' rmw' rf' sc' x a.
Proof.
unfold c_cur_rw, dom_rel, c_cur, eqv_rel, seq in *; desc; subst.
eapply rw_hb.
eapply rw_mon; eauto.
apply sb_in_hb; cdes GSTEP;  apply SB_STEP.
right; splits; try done.
intro; subst.
apply FRESH; eapply rw_actb; eauto.
Qed.

Lemma gstep_new_sc0
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l x (CUR: c_cur_sc acts sb rmw rf sc (thread a) l x) : 
    sc_relation acts' sb' rmw' rf' sc' x a.
Proof.
unfold c_cur_sc, dom_rel, c_cur, eqv_rel, seq in *; desc; subst.
eapply scr_hb.
eapply scr_mon; eauto.
apply sb_in_hb; cdes GSTEP;  apply SB_STEP.
right; splits; try done.
intro; subst.
apply FRESH; eapply scr_actb; eauto.
Qed.

Lemma gstep_new_ur_relation
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_ur acts sb rmw rf sc l x b) (RA: is_ra a) : 
  ur_relation acts' sb' rmw' rf' sc' x a.
Proof.
red in REL; red in REL; red in REL; unfold seq,eqv_rel in *; desf.
eapply ur_hb with (b:=z0).
apply ur_mon; eauto.
apply sw_in_hb; exists b.
splits; eauto using rel_mon.
repeat eexists; splits; eauto.
Qed.

Lemma gstep_new_rw_relation
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_rw acts sb rmw rf sc l x b) (RA: is_ra a) : 
  rw_relation acts' sb' rmw' rf' sc' x a.
Proof.
red in REL; red in REL; red in REL; unfold seq,eqv_rel in *; desf.
eapply rw_hb with (b:=z0).
apply rw_mon; eauto.
apply sw_in_hb; exists b.
splits; eauto using rel_mon.
repeat eexists; splits; eauto.
Qed.

Lemma gstep_new_sc_relation
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_sc acts sb rmw rf sc l x b) (RA: is_ra a) : 
  sc_relation acts' sb' rmw' rf' sc' x a.
Proof.
red in REL; red in REL; red in REL; unfold seq,eqv_rel in *; desf.
eapply scr_hb with (b:=z0).
apply scr_mon; eauto.
apply sw_in_hb; exists b.
splits; eauto using rel_mon.
repeat eexists; splits; eauto.
Qed.


Lemma gstep_new_ur
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_ur acts sb rmw rf sc l x b) (RA: is_ra a) : 
  c_cur_ur acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,x; splits; red; splits; eauto.
eapply m_rel_doma1; eauto.
eapply m_rel_doma2; eauto.
exists a; splits; try by red; eauto.
eapply gstep_new_ur_relation; eauto.
Qed.

Lemma gstep_new_acq_ur
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_ur acts sb rmw rf sc l x b) (RA: is_rlx a) : 
  c_acq_ur acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,b; splits; eauto.
by apply m_rel_ur_mon; eauto.
unfold eqv_rel.
repeat (eexists; splits; eauto).
Qed.

Lemma gstep_new_acq_rw
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_rw acts sb rmw rf sc l x b) (RA: is_rlx a) : 
  c_acq_rw acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,b; splits; eauto.
by apply m_rel_rw_mon; eauto.
unfold eqv_rel.
repeat (eexists; splits; eauto).
Qed.

Lemma gstep_new_acq_sc
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_sc acts sb rmw rf sc l x b) (RA: is_rlx a) : 
  c_acq_sc acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,b; splits; eauto.
by apply m_rel_sc_mon; eauto.
unfold eqv_rel.
repeat (eexists; splits; eauto).
Qed.


Lemma gstep_new_rw1
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_rw acts sb rmw rf sc l x b) (RA: is_ra a) : 
  c_cur_rw acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,x; splits; red; splits; eauto.
eapply m_rel_doma1; eauto.
eapply m_rel_doma2; eauto.
exists a; splits; try by red; eauto.
eapply gstep_new_rw_relation; eauto.
Qed.

Lemma gstep_new_rw2
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  b (RFb: (rf' b a)) l (LOC: loc b = Some l): 
  c_cur_rw acts' sb' rmw' rf' sc' (thread a) l b.
Proof.
exists a,b; splits; red; splits; eauto.
eapply rf_doma with (rf:=rf'); eauto.
exists a; splits.
eapply rf_in_rw; eauto.
red; eauto.
Qed.

Lemma gstep_new_sc1
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (REL: m_rel_sc acts sb rmw rf sc l x b) (RA: is_ra a) : 
  c_cur_sc acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,x; splits; red; splits; eauto.
eapply m_rel_doma1; eauto.
eapply m_rel_doma2; eauto.
exists a; splits; try by red; eauto.
eapply gstep_new_sc_relation; eauto.
Qed.

Lemma gstep_new_sc2
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  b (RFb: (rf' b a)) l (LOC: loc b = Some l): 
  c_cur_sc acts' sb' rmw' rf' sc' (thread a) l b.
Proof.
exists a,b; splits; red; splits; eauto.
eapply rf_doma with (rf:=rf'); eauto.
exists a; splits.
eapply rw_in_sc; eauto.
eapply rf_in_rw; eauto.
red; eauto.
Qed.

(* Lemma gstep_new_sc3
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x l (S_TM: S_tm acts sb rmw rf l x) (SC: is_sc a) : 
  c_cur_sc acts' sb' rmw' rf' sc' (thread a) l x.
Proof.
exists a,x; splits; red; splits; eauto.
eapply S_tm_dom1; eauto.
eapply S_tm_dom2; eauto.
red in S_TM; red in S_TM; desc.
exists a,b; splits; red; splits; eauto.
eapply rf_doma with (rf:=rf'); eauto.
exists a; splits.
eapply rw_in_sc; eauto.
eapply rf_in_rw; eauto.
red; eauto.
Qed. *)

Lemma gstep_c_cur_ur_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (UR: c_cur (thread a) l (ur_relation acts' sb' rmw' rf' sc') x a)
  (NEQ: x <> a) : 
c_cur_ur acts sb rmw rf sc (thread a) l x \/
exists c, (ur_relation acts sb rmw rf sc) x c /\ rel acts sb rmw rf c b /\ is_ra a.
Proof.
red in UR; unfold seq, eqv_rel in *; desc; subst.
eapply gstep_ur_b in UR0; try edone.
desf; unfold c_cur_ur, dom_rel, c_cur; eauto 6.
Qed. 

Lemma gstep_c_cur_rw_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (RW: c_cur (thread a) l (rw_relation acts' sb' rmw' rf' sc') x a)
  (NEQ: x <> a) : 
    c_cur_rw acts sb rmw rf sc (thread a) l x \/ 
    x = b /\ loc b = Some l \/
    exists c, (rw_relation acts sb rmw rf sc) x c /\ rel acts sb rmw rf c b /\ is_ra a.
Proof.
red in RW; unfold seq, eqv_rel in *; desc; subst.
destruct (classic (z=b)); subst; eauto.
eapply gstep_rw_b in RW0; try edone.
desf; unfold c_cur_rw, dom_rel, c_cur; eauto 6.
Qed. 

Lemma gstep_c_cur_sc_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (SC: c_cur (thread a) l (sc_relation acts' sb' rmw' rf' sc') x a)
  (NEQ: x <> a) : 
    c_cur_sc acts sb rmw rf sc (thread a) l x \/ 
    is_sc a \/
    x = b /\ loc b = Some l \/
    exists c, (sc_relation acts sb rmw rf sc) x c /\ rel acts sb rmw rf c b /\ is_ra a.
Proof.
red in SC; unfold seq, eqv_rel in *; desc; subst.
destruct (classic (z=b)); subst; eauto.
eapply gstep_scr_b in SC0; try edone.
desf; unfold c_cur_sc, dom_rel, c_cur; eauto 8.
Qed. 

Lemma gstep_c_acq_ur_b
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  x b (RFb: (rf' b a)) l (UR: c_acq acts' sb' rmw' rf' (thread a) l (ur_relation acts' sb' rmw' rf' sc') x a):
m_rel_ur acts sb rmw rf sc l x b /\ is_rlx a.
Proof.
red in UR; unfold seq, eqv_rel in *; desc; subst.
splits; try done. 
assert (z=b).
cdes GSTEP; cdes COH0; cdes WF; cdes WF_RF.
eapply RF_FUN; eauto.
subst.

eapply gstep_ur_b in UR0; try edone.
desf.
- left; exists c. exists z. splits. red; eauto. eexists; splits; eauto. red; eauto.
- right; exists c; splits; done.
Qed. 

Lemma gstep_c_cur_ur_other_threads
     a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
     i (NEQ: thread a <> i) l b :
     c_cur_ur acts' sb' rmw' rf' sc' i l b <-> c_cur_ur acts sb rmw rf sc i l b.
Proof.
split; intro H; desc.
- eapply gstep_c_cur_ur_a in H; destruct H; try edone.
  eapply c_cur_domb in H; cdes COH; try edone.
- eapply c_cur_ur_mon; eauto.
Qed.

Lemma gstep_c_cur_rw_other_threads
     a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
     i (NEQ: thread a <> i) l b :
     c_cur_rw acts' sb' rmw' rf' sc' i l b <-> c_cur_rw acts sb rmw rf sc i l b.
Proof.
split; intro H; desc.
- eapply gstep_c_cur_rw_a in H; destruct H; try edone.
  eapply c_cur_domb in H; cdes COH; try edone.
- eapply c_cur_rw_mon; eauto.
Qed.

Lemma gstep_c_cur_sc_other_threads
     a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
     i (NEQ: thread a <> i) l b :
     c_cur_sc acts' sb' rmw' rf' sc' i l b <-> c_cur_sc acts sb rmw rf sc i l b.
Proof.
split; intro H; desc.
- eapply gstep_c_cur_sc_a in H; destruct H; try edone.
  eapply c_cur_domb in H; cdes COH; try edone.
- eapply c_cur_sc_mon; eauto.
Qed.

Lemma gstep_c_cur_ur
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l b (RFb: (rf' b a)) i x :
  c_cur_ur acts' sb' rmw' rf' sc' i l x <->
  c_cur_ur acts sb rmw rf sc i l x \/ 
  m_rel_ur acts sb rmw rf sc l x b /\ is_ra a /\ thread a = i.
Proof.
destruct (classic (thread a = i)) as [E|N]; subst; cycle 1.
{ 
split; intro.
eby left; eapply gstep_c_cur_ur_other_threads.
desf; try eby exfalso.
eapply gstep_c_cur_ur_other_threads; edone.
}
{
split; intro CUR'.
- assert (is_write x).
    eapply c_cur_ur_dom1 with (acts:=acts'); eauto.
  assert (loc x = Some l).
    eapply c_cur_ur_dom2 with (acts:=acts'); eauto.
  eapply gstep_c_cur_ur_a in CUR'; try edone.
  desf; eauto.
  eapply gstep_c_cur_ur_b in CUR'; try edone.
  desf; eauto.
  right; splits; eauto using ur_rel.
  by intro; subst; eapply rf_domb in RFb; eauto; 
    unfold is_read, is_write in *; destruct (lab a); ins.
- desf; try by apply c_cur_ur_mon; eauto.
  eapply gstep_new_ur; edone.
}
Qed.

Lemma gstep_c_cur_rw
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l b (RFb: (rf' b a)) i x :
  c_cur_rw acts' sb' rmw' rf' sc' i l x <->
  c_cur_rw acts sb rmw rf sc i l x \/ 
  m_rel_rw acts sb rmw rf sc l x b /\ is_ra a /\ thread a = i \/
  x=b /\ thread a = i /\ loc b = Some l.
Proof.
destruct (classic (thread a = i)) as [E|N]; subst; cycle 1.
{ 
split; intro.
eby left; eapply gstep_c_cur_rw_other_threads.
desf; try eby exfalso.
eapply gstep_c_cur_rw_other_threads; edone.
}
{
split; intro CUR'.
- destruct (classic (x = b)); subst.
  * right; right; splits; eauto.
    eapply c_cur_rw_dom2 with (acts:=acts'); eauto.
  * assert (is_write x).
      eapply c_cur_rw_dom1 with (acts:=acts'); eauto.
    assert (loc x = Some l).
      eapply c_cur_rw_dom2 with (acts:=acts'); eauto.
    eapply gstep_c_cur_rw_a in CUR'; try edone.
    desf; eauto.
    eapply gstep_c_cur_rw_b in CUR'; try edone.
    desf; eauto.
    right; left; splits; eauto using rw_rel.
    by intro; subst; eapply rf_domb in RFb; eauto; 
      unfold is_read, is_write in *; destruct (lab a); ins.
- desf; try by apply c_cur_rw_mon; eauto.
  all: try eby apply gstep_new_rw2.
  all: try eby eapply gstep_new_rw1.
}
Qed.

Lemma gstep_c_cur_sc
  a (COH: Coherent acts sb rmw rf mo sc) (GSTEP: gstep a) 
  l b (RFb: (rf' b a)) i x :
  c_cur_sc acts' sb' rmw' rf' sc' i l x <->
  c_cur_sc acts sb rmw rf sc i l x \/ 
  is_sc a /\ thread a = i \/
  x=b /\ thread a = i /\ loc b = Some l \/
  m_rel_sc acts sb rmw rf sc l x b /\ is_ra a /\ thread a = i.
Proof.
destruct (classic (thread a = i)) as [E|N]; subst; cycle 1.
{ 
split; intro.
eby left; eapply gstep_c_cur_sc_other_threads.
desf; try eby exfalso.
eapply gstep_c_cur_sc_other_threads; edone.
}
{
split; intro CUR'.
- destruct (classic (x = b)); subst.
  * right; right; left; splits; eauto.
    eapply c_cur_sc_dom2 with (acts:=acts'); eauto.
  * assert (is_write x).
      eapply c_cur_sc_dom1 with (acts:=acts'); eauto.
    assert (loc x = Some l).
      eapply c_cur_sc_dom2 with (acts:=acts'); eauto.
    eapply gstep_c_cur_sc_a in CUR'; try edone.
    desf; eauto.
    eapply gstep_c_cur_sc_b in CUR'; try edone.
    desf; eauto; try eby exfalso.
    right; right; right; splits; eauto using scr_rel.
    by intro; subst; eapply rf_domb in RFb; eauto; 
      unfold is_read, is_write in *; destruct (lab a); ins.
- desf; try by apply c_cur_sc_mon; eauto.
  try eby apply gstep_new_sc2.
  eby eapply gstep_new_sc1.
}
Qed.


*)

End Graph_steps.

Require Import Setoid Permutation.

Add Parametric Morphism : (graph_inclusion) with signature 
  (@Permutation _) ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==>
  (@Permutation _) ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==> iff as graph_inclusion_more.
Proof.
intros acts acts0 ACTS sb sb0 SB rmw rmw0 RMW rf rf0 RF mo mo0 MO sc sc0 SC.
intros acts' act0' ACTS' sb' sb0' SB' rmw' rmw0' RMW' rf' rf0' RF' mo' mo0' MO' sc' sc0' SC'.
unfold graph_inclusion; unnw; split; splits; desc;
try (by eauto using Permutation_in, Permutation_sym);
try (eapply inclusion_more; try (by apply same_relation_sym; edone); edone);
try (eapply inclusion_more; edone).
Qed.

Add Parametric Morphism : (gstep) with signature 
  eq ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==>
  eq ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==> eq  ==> iff as gstep_more.
Proof.
intros acts sb sb0 SB rmw rmw0 RMW rf rf0 RF mo mo0 MO sc sc0 SC.
intros acts' sb' sb0' SB' rmw' rmw0' RMW' rf' rf0' RF' mo' mo0' MO' sc' sc0' SC'.
intros a.
unfold gstep; unnw.
rewrite SB, RMW, RF, MO, SC, SB', RMW', RF', MO', SC'.
split; splits; desc; eauto; try (intros; apply SC'; eauto).
by intros; eapply iff_trans; [eby apply iff_sym, same_relation_exp|];
   rewrite H1; split; ins; desf; eauto; left; apply SB.
by intros; eapply iff_trans; [eby apply same_relation_exp|];
   rewrite H1; split; ins; desf; eauto; left; apply SB.
Qed.




