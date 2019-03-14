(******************************************************************************)
(** * Definitions of the axiomatic memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.

Require Import Gevents.

Set Implicit Arguments.
Remove Hints plus_n_O.

Ltac cdes H := 
  let H' := fresh H in assert (H' := H); red in H'; desc. 

Section Consistency.

  Variable acts : list event.  
  Variable sb rmw rf mo sc : event -> event -> Prop. 

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

  Definition useq := clos_trans (rf ;; rmw ;; <| is_rlx_rw |>).
   
  Definition rseq :=
    <| fun a => In a acts |> ;; 
    <| is_write |> ;;
    clos_refl (restr_eq_rel loc sb) ;;
    <| is_write |> ;;
    <| is_rlx_rw |> ;;
    clos_refl useq.
   
  Definition rel :=
    <| is_rel |> ;; 
    (<| is_write |> +++ <| is_fence |> ;; sb) ;; 
    rseq.
   
  Definition sw :=
    rel ;; rf ;; clos_refl (<| is_rlx_rw |> ;; sb ;; <| is_fence |>) ;; 
    <| is_acq |>.
   
  Definition hb :=
    clos_trans (sb +++ sw).

(******************************************************************************)
(** ** Additional derived relations for simulation *)
(******************************************************************************)

  Definition rfhbsc_opt l :=
    <| fun x => is_write x /\ loc x = Some l |> ;;
    <| fun x => In x acts |> ;;
    clos_refl (clos_refl rf ;; hb ;; <| is_sc_fence |>).

  Definition urr l := 
    (rfhbsc_opt l ;; (clos_refl sc) +++
    <| fun x => is_write x /\ loc x = Some l |> ;; rf ;; <| is_rlx_rw |>) ;; 
    clos_refl hb.

  Definition rwr l := 
    urr l +++ <| fun x => is_write x /\ loc x = Some l |> ;; rf ;; clos_refl hb.

  Definition c_rel i l' tmr :=  
    tmr ;; 
    <| is_rel |> ;; <| fun x => is_write x /\ loc x = Some l' \/ is_fence x |> ;;
    <| fun x => thread x = i \/ is_init x |>.

  Definition c_cur i tmr := 
    tmr ;; 
    <| fun x => thread x = i \/ is_init x |>.

  Definition c_acq i tmr :=  
    tmr ;; clos_refl (rel ;; rf ;; <| is_rlx_rw |>) ;;
    <| fun x => thread x = i \/ is_init x |>.

  Definition m_rel tmr :=
    tmr ;; rel.

  Definition S_tmr l := 
    rfhbsc_opt l ;; <| is_sc_fence |>. 

  Definition S_tm l := dom_rel (S_tmr l).

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

  Lemma sb_in_hb : inclusion sb hb.
  Proof. vauto. Qed.

  Lemma sw_in_hb : inclusion sw hb.
  Proof. vauto. Qed.

  Lemma hb_trans : transitive hb.
  Proof. vauto. Qed.

  Lemma urr_refl l : forall x (IN: In x acts) (WRITE: is_write x) 
                      (LOC: loc x = Some l), (urr l) x x.
  Proof.
  ins; exists x; splits; vauto.
  left; repeat (ins; exists x; splits; vauto).
  Qed.

  Lemma ur_in_rw l : inclusion (urr l) (rwr l).
  Proof. vauto. Qed.

  Section MonotonicityLemmas.

    Variables (tm tm' : relation event).
    Hypothesis (M: inclusion tm tm').
    Variables (i : thread_id) (l' : Loc.t).
    Ltac local_tac := unfold c_rel, c_cur, c_acq; rewrite M; try done.

    Lemma c_rel_mon : inclusion (c_rel i l' tm) (c_rel i l' tm').
    Proof. local_tac. Qed.

    Lemma c_cur_mon : inclusion (c_cur i tm) (c_cur i tm').
    Proof. local_tac. Qed.

    Lemma c_acq_mon : inclusion (c_acq i tm) (c_acq i tm').
    Proof. local_tac. Qed.

    Lemma c_rel_cur_mon : inclusion (c_rel i l' tm) (c_cur i tm').
    Proof. local_tac; rewrite !inclusion_seq_eqv_l; done. Qed.
  
    Lemma c_cur_acq_mon : inclusion (c_cur i tm) (c_acq i tm').
    Proof. local_tac; rewrite crE; rel_simpl. Qed.

    Lemma c_rel_acq_mon : inclusion (c_rel i l' tm) (c_acq i tm').
    Proof. local_tac; rewrite !inclusion_seq_eqv_l, crE; rel_simpl. Qed.

  End MonotonicityLemmas.

  Lemma hb_hb : inclusion (hb ;; hb) hb.
  Proof. unfold seq, inclusion; ins; desf; vauto. Qed.

  Lemma cr_hb_hb : inclusion (clos_refl hb ;; hb) hb.
  Proof. rewrite crE, seq_union_l, hb_hb; rel_simpl. Qed.

  Lemma cr_hb_cr_hb : inclusion (clos_refl hb ;; clos_refl hb) (clos_refl hb).
  Proof. unfold seq, inclusion, clos_refl; ins; desf; eauto.
         by right; eapply hb_hb; eexists; eauto. Qed.

  Lemma urr_hb l : inclusion (urr l ;; hb) (urr l).
  Proof.
    unfold urr. rewrite !seqA, cr_hb_hb; eauto with rel.
  Qed.

  Lemma urr_cr_hb l : inclusion (urr l ;; clos_refl hb) (urr l).
  Proof.
    unfold urr. rewrite !seqA, cr_hb_cr_hb; eauto with rel.
  Qed.

  Lemma rwr_hb l : inclusion (rwr l ;; hb) (rwr l). 
  Proof.
    unfold rwr; rewrite seq_union_l, urr_hb, !seqA, cr_hb_hb.
    eauto 8 with rel.
  Qed.

  Lemma rwr_cr_hb l : inclusion (rwr l ;; clos_refl hb) (rwr l). 
  Proof.
    unfold rwr; rewrite seq_union_l, urr_cr_hb, !seqA, cr_hb_cr_hb.
    eauto 8 with rel.
  Qed.

(******************************************************************************)
(** ** Well-formed relations *)
(******************************************************************************)

Definition WfACTS := 
  << ACTS_INIT: forall a (INIT: is_init a), In a acts >> /\
  << ACTS_TID: forall a (IN: In a acts), is_init a \/ is_proper a >>.

Definition WfSB := 
  << SB_ACTa: forall a b (SB: sb a b), In a acts >> /\
  << SB_ACTb: forall a b (SB: sb a b), In b acts >> /\
  << SB_TID: forall a b (SB: sb a b), 
              (thread a = thread b /\ is_proper a /\ is_proper b) \/ 
              (init_pair a b) >> /\
  << SB_INIT: forall a b (INIT: init_pair a b) (IN: In b acts), sb a b >> /\
  << SB_IRR: irreflexive sb >> /\
  << SB_T: transitive sb >> /\
  << SB_TOT: forall a b (SAME_TID: thread a = thread b) 
              (INa: In a acts) (INb: In b acts)
              (PROPERa: is_proper a) (PROPERb: is_proper b)
              (NEQ: a <> b), sb a b \/ sb b a >>.

Definition WfRMW := 
  << RMW_DOMa: forall a b (RMW: rmw a b), is_read a >> /\
  << RMW_DOMb: forall a b (RMW: rmw a b), is_write b >> /\
  << RMW_LOC: forall a b (RMW: rmw a b), exists l, (loc a = Some l) /\ (loc b = Some l) >> /\
  << RMW_SB: forall a b (RMW: rmw a b), sb a b >> /\
  << RMW_SBI: forall a b (RMW: rmw a b) c (SB: sb c b) (NEQ: c <> a), sb c a >> /\
  << RMW_SBI': forall a b (RMW: rmw a b) c (SB: sb a c) (NEQ: c <> b), sb b c >>.

Definition WfRF := 
  << RF_ACTa: forall a b (RF: rf a b), In a acts >> /\
  << RF_ACTb: forall a b (RF: rf a b), In b acts >> /\
  << RF_DOMa: forall a b (RF: rf a b), is_write a >> /\
  << RF_DOMb: forall a b (RF: rf a b), is_read b >> /\
  << RF_LOC: forall a b (RF: rf a b), exists l, (loc a = Some l) /\ (loc b = Some l) >> /\
  << RF_VAL: forall a b (RF: rf a b), (val a = val b) >> /\
  << RF_FUN: forall a b c (RF1: rf a c) (RF2: rf b c), a=b >> /\
  << RF_TOT: forall b (IN: In b acts) (READ: is_read b), exists a, rf a b >>.

Definition WfMO :=
  << MO_ACTa: forall a b (MO: mo a b), In a acts >> /\
  << MO_ACTb: forall a b (MO: mo a b), In b acts >> /\
  << MO_DOMa: forall a b (MO: mo a b), is_write a >> /\
  << MO_DOMb: forall a b (MO: mo a b), is_write b >> /\
  << MO_LOC: forall a b (MO: mo a b), exists l, (loc a = Some l) /\ (loc b = Some l) >> /\
  << MO_IRR: irreflexive mo >> /\
  << MO_T: transitive mo >> /\
  << MO_TOT: forall l, is_total (fun a => In a acts /\ is_write a /\ (loc a = Some l)) mo >>.

Definition WfSC :=
  << SC_ACTa: forall a b (SC: sc a b), In a acts >> /\
  << SC_ACTb: forall a b (SC: sc a b), In b acts >> /\
  << SC_DOMa: forall a b (SC: sc a b), is_sc_fence a >> /\
  << SC_DOMb: forall a b (SC: sc a b), is_sc_fence b >> /\
  << SC_IRR: irreflexive sc >> /\
  << SC_T: transitive sc >> /\
  << SC_TOT: is_total (fun a => In a acts /\ is_sc_fence a) sc >>.

Definition Wf :=
  << WF_ACTS : WfACTS >> /\
  << WF_SB   : WfSB >> /\
  << WF_RMW  : WfRMW >> /\
  << WF_RF   : WfRF >> /\
  << WF_MO   : WfMO >> /\
  << WF_SC   : WfSC >>.


(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma init_events_wf1 (C: Wf) a (IN: In a acts) : ~ is_init a <->  is_proper a.
Proof.
cdes C; cdes WF_ACTS; split; ins; unfold is_init, is_proper in *; desc.
specialize (ACTS_TID a IN); desf; eauto.
try exfalso; apply H; eauto.
intro; desc; desf.
Qed.

Lemma init_events_wf2 (C: Wf) a (IN: In a acts) : is_init a <->  ~ is_proper a.
Proof. generalize (init_events_wf1 C a IN); intros; tauto. Qed.

Lemma rf_lv (C: WfRF) x y (H: rf x y) l v o (LABR: lab y = Aload l v o)
 : exists o', lab x = Astore l v o'.
Proof.
  unfold WfRF in *; desc.
  specialize (RF_DOMa _ _ H).
  specialize (RF_LOC _ _ H); desf.
  specialize (RF_VAL _ _ H).
  unfold is_write, loc, val in *.
  destruct (lab x); destruct (lab y); ins; desf; eauto.
Qed.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Section WellFormedResults.

Definition loceq (R : event -> event -> Prop) := 
forall (WF: Wf) a b (H: R a b), loc a = loc b.

Lemma loceq_seq R T (A: loceq R) (B: loceq T) : loceq (R ;; T).
Proof.
red; ins. destruct H; desc; etransitivity.
eby apply A.
eby apply B.
Qed.

Lemma loceq_tc R (A: loceq R) : loceq (tc R).
Proof.
red; ins. 
induction H; eauto.
etransitivity; edone.
Qed.

Lemma loceq_clos_refl R (A: loceq R) : loceq (clos_refl R).
Proof.
red; ins. 
red in H; desf; subst; auto.
Qed.

Lemma loceq_restr_eq_rel_loc R : loceq (restr_eq_rel loc R).
Proof.
red; ins; red in H; desc; subst; done.
Qed.

Lemma loceq_eqv_rel f : loceq (eqv_rel f).
Proof.
red; ins; red in H; desc; subst; done.
Qed.

Hint Resolve
 loceq_seq
 loceq_tc
 loceq_clos_refl
 loceq_restr_eq_rel_loc
 loceq_eqv_rel
 : loceq.

Lemma loceq_rmw : loceq rmw.
Proof.
  red; ins; red in WF; desc.
  red in WF_RMW; desc; specialize (RMW_LOC _ _ H).
  unfold is_write, loc, val in *.
  destruct (lab a); ins; destruct b; ins; desf.
Qed.

Lemma loceq_rf : loceq rf.
Proof.
  red; ins; red in WF; desc.
  red in WF_RF; desf; specialize (RF_LOC _ _ H).
  unfold is_write, loc, val in *.
  destruct (lab a); ins; destruct b; ins; desf.
Qed.

Lemma loceq_mo : loceq mo.
Proof.
  red; ins; red in WF; desc.
  red in WF_MO; desf; specialize (MO_LOC _ _  H).
  unfold is_write, loc, val in *.
  destruct (lab a); ins; destruct (lab b); ins; desf.
Qed.

Lemma loceq_useq : loceq useq.
Proof.
unfold useq; eauto using loceq_rmw, loceq_rf with loceq.
Qed.

Lemma loceq_rseq : loceq rseq.
Proof.
unfold rseq; eauto 10 using loceq_useq with loceq.
Qed.


(******************************************************************************)
(** ** Domains and Codomains of relations  *)
(******************************************************************************)

Hypothesis WF: Wf.

Lemma sb_domb : domb sb is_proper.
Proof. cdes WF; cdes WF_SB.
red; ins.
specialize (SB_TID x y REL); desf.
red in SB_TID; desc; done.
Qed.
Lemma rmw_doma : doma rmw is_read.
Proof. cdes WF; cdes WF_RMW; eauto. Qed.
Lemma rmw_domb : domb rmw is_write.
Proof. cdes WF; cdes WF_RMW; eauto. Qed.
Lemma rf_doma : doma rf is_write.
Proof. cdes WF; cdes WF_RF; eauto. Qed.
Lemma rf_domb : domb rf is_read.
Proof. cdes WF; cdes WF_RF; eauto. Qed.
Lemma mo_doma : doma mo is_write.
Proof. cdes WF; cdes WF_MO; eauto. Qed.
Lemma mo_domb : domb mo is_write.
Proof. cdes WF; cdes WF_MO; eauto. Qed.
Lemma sc_doma : doma sc is_sc_fence.
Proof. cdes WF; cdes WF_SC; eauto. Qed.
Lemma sc_domb : domb sc is_sc_fence.
Proof. cdes WF; cdes WF_SC; eauto. Qed.
Lemma useq_doma : doma useq is_write.
Proof. unfold useq; eauto using rf_doma with rel. Qed.
Lemma useq_domb : domb useq is_write.
Proof. unfold useq; eauto using rmw_domb with rel. Qed.
Lemma rseq_doma : doma rseq is_write.
Proof. unfold rseq; eauto with rel. Qed.
Lemma rseq_domb : domb rseq is_write.
Proof. unfold rseq; rewrite <- !seqA; eauto using useq_domb with rel. Qed.
Lemma rel_doma : doma rel is_rel.
Proof. unfold rel; eauto with rel. Qed.
Lemma rel_domb : domb rel is_write.
Proof. unfold rel; eauto using rseq_domb with rel. Qed.
Lemma sw_doma : doma sw is_rel.
Proof. unfold sw; eauto using rel_doma with rel. Qed.
Lemma sw_domb : domb sw is_acq.
Proof. unfold sw; eauto with rel. Qed.

Lemma rfhbsc_opt_doma l : doma (rfhbsc_opt l) (fun a => is_write a /\ loc a = Some l).
Proof. unfold rfhbsc_opt; eauto with rel. Qed.
Lemma urr_doma l : doma (urr l) (fun a => is_write a /\ loc a = Some l).
Proof. unfold urr; eauto using rfhbsc_opt_doma with rel. Qed.
Lemma rwr_doma l : doma (rwr l) (fun a => is_write a /\ loc a = Some l).
Proof. unfold rwr; eauto using urr_doma with rel. Qed.

Lemma rfhbsc_opt_doma1 l : doma (rfhbsc_opt l) is_write.
Proof. red; ins; apply rfhbsc_opt_doma in REL; desf. Qed.
Lemma urr_doma1 l : doma (urr l) is_write.
Proof. red; ins; apply urr_doma in REL; desf. Qed.
Lemma rwr_doma1 l : doma (rwr l) is_write.
Proof. red; ins; apply rwr_doma in REL; desf. Qed.
Lemma rfhbsc_opt_doma2 l : doma (rfhbsc_opt l) (fun a => loc a = Some l).
Proof. red; ins; apply rfhbsc_opt_doma in REL; desf. Qed.
Lemma urr_doma2 l : doma (urr l) (fun a => loc a = Some l).
Proof. red; ins; apply urr_doma in REL; desf. Qed.
Lemma rwr_doma2 l : doma (rwr l) (fun a => loc a = Some l).
Proof. red; ins; apply rwr_doma in REL; desf. Qed.

Lemma c_rel_doma i l' tmr d: doma tmr d -> doma (c_rel i l' tmr) d.
Proof. unfold c_rel; eauto with rel. Qed.
Lemma c_rel_domb1 i l' tmr: domb (c_rel i l' tmr) (fun a => thread a = i \/ is_init a).
Proof. unfold c_rel; eauto with rel. Qed.
Lemma c_rel_domb2 i l' tmr: 
  domb (c_rel i l' tmr) (fun x => is_write x /\ loc x = Some l' \/ is_fence x). 
Proof. unfold c_rel; eauto with rel. Qed.
Lemma c_rel_domb3 i l' tmr: domb (c_rel i l' tmr) (is_rel).
Proof. unfold c_rel; rewrite <- !seqA; eauto with rel. Qed.

Lemma c_cur_doma i tmr d: doma tmr d -> doma (c_cur i tmr) d.
Proof. unfold c_cur; eauto with rel. Qed.
Lemma c_cur_domb i tmr: domb (c_cur i tmr) (fun a => thread a = i \/ is_init a).
Proof. unfold c_cur; eauto with rel. Qed.

Lemma c_acq_doma i tmr d: doma tmr d -> doma (c_acq i tmr) d.
Proof. unfold c_acq; eauto with rel. Qed.
Lemma c_acq_domb i tmr: domb (c_acq i tmr) (fun a => thread a = i \/ is_init a).
Proof. unfold c_acq; eauto with rel. Qed.

Lemma m_rel_doma tmr d: doma tmr d -> doma (m_rel tmr) d.
Proof. unfold m_rel; eauto with rel. Qed.
Lemma m_rel_domb tmr: domb (m_rel tmr) is_write.
Proof. unfold m_rel; eauto using rel_domb with rel. Qed.

Lemma S_tmr_doma l: doma (S_tmr l) (fun a => is_write a /\ loc a = Some l).
Proof. unfold S_tmr; eauto with rel. Qed.
Lemma S_tmr_doma1 l: doma (S_tmr l) is_write.
Proof. unfold doma; ins; exploit S_tmr_doma; ins; desc; eauto. Qed.
Lemma S_tmr_doma2 l: doma (S_tmr l) (fun a => loc a = Some l).
Proof. unfold doma; ins; exploit S_tmr_doma; ins; desc; eauto. Qed.
Lemma S_tmr_domb l: domb (S_tmr l) is_sc_fence.
Proof. unfold S_tmr; eauto 10 with rel. Qed.

Lemma rf_mo a b c (RF: rf a b) (MO: mo c b) : False.
Proof.
  exploit rf_domb; eauto.
  exploit mo_domb; eauto; ins.
  unfold is_read, is_write in *; destruct (lab b); ins; desf.
Qed.

Lemma inv_rf_mo a b c (RF: rf b a) (MO: mo a c) : False.
Proof.
  exploit rf_domb; eauto.
  exploit mo_doma; eauto; ins.
  unfold is_read, is_write in *; destruct (lab a); ins; desf.
Qed.

Lemma rel_rf a b c (RA: is_acq c) (REL: rel a b) (RF: rf b c) : sw a c.
Proof.
unfold WfRF,WfMO in *; desf.
eexists; splits; try edone.
unfold eqv_rel.
exists c; splits; try edone.
exists c; splits; try edone.
left; eauto.
Qed.

Lemma rf_rf a b c (RF: rf a b) (RF1: rf b c) : False.
Proof.
  exploit rf_doma; eauto.
  generalize (rf_domb RF); ins.
  unfold is_read, is_write in *; destruct (lab b); ins; desf.
Qed.

Lemma irr_rf a (RF: rf a a) : False.
Proof.
  eapply rf_rf; edone.
Qed.



(******************************************************************************)
(** ** Actions in graph *)
(******************************************************************************)

Local Notation "'acta' r" := (doma r (fun x => In x acts)) (at level 1).
Local Notation "'actb' r" := (domb r (fun x => In x acts)) (at level 1).

Lemma sb_acta : acta sb.
Proof. cdes WF; cdes WF_SB; eauto. Qed.
Lemma sb_actb : actb sb.
Proof. cdes WF; cdes WF_SB; eauto. Qed.
Lemma rmw_acta : acta rmw.
Proof. red; cdes WF; cdes WF_SB; cdes WF_RMW; eauto. Qed.
Lemma rmw_actb : actb rmw.
Proof. red; cdes WF; cdes WF_SB; cdes WF_RMW; eauto. Qed.
Lemma rf_acta : acta rf.
Proof. red; cdes WF; cdes WF_SB; cdes WF_RF; eauto. Qed.
Lemma rf_actb : actb rf.
Proof. red; cdes WF; cdes WF_SB; cdes WF_RF; eauto. Qed.
Lemma mo_acta : acta mo.
Proof. red; cdes WF; cdes WF_SB; cdes WF_MO; eauto. Qed.
Lemma mo_actb : actb mo.
Proof. red; cdes WF; cdes WF_SB; cdes WF_MO; eauto. Qed.
Lemma sc_acta : acta sc.
Proof. red; cdes WF; cdes WF_SB; cdes WF_SC; eauto. Qed.
Lemma sc_actb : actb sc.
Proof. red; cdes WF; cdes WF_SB; cdes WF_SC; eauto. Qed.

Hint Resolve 
  sb_acta rmw_acta rf_acta mo_acta sc_acta 
  sb_actb rmw_actb rf_actb mo_actb sc_actb : rel. 

Lemma useq_acta : acta useq. Proof. eauto with rel. Qed.
Lemma useq_actb : actb useq. Proof. eauto with rel. Qed.
Hint Resolve useq_acta useq_actb : rel. 
Lemma rseq_acta : acta rseq. Proof. eauto with rel. Qed.
Lemma rseq_actb : actb rseq. Proof. unfold rseq; rewrite <- !seqA; eauto 8 with rel. Qed.
Hint Resolve rseq_acta rseq_actb : rel. 
Lemma rel_acta : acta rel. Proof. unfold rel; rel_simpl; eauto with rel. Qed.
Lemma rel_actb : actb rel. Proof. eauto with rel. Qed.
Hint Resolve rel_acta rel_actb : rel. 
Lemma sw_acta : acta sw. Proof. eauto with rel. Qed.
Lemma sw_actb : actb sw. Proof. unfold sw; rewrite inclusion_seq_eqv_r; eauto with rel. Qed.
Hint Resolve sw_acta sw_actb : rel.
Lemma hb_acta : acta hb. Proof. eauto with rel. Qed.
Lemma hb_actb : actb hb. Proof. eauto with rel. Qed.
Hint Resolve hb_acta hb_actb : rel.
Lemma rfhbsc_opt_acta l : acta (rfhbsc_opt l). Proof. eauto with rel. Qed.
Lemma rfhbsc_opt_actb l : actb (rfhbsc_opt l). Proof. eauto with rel. Qed.
Hint Resolve rfhbsc_opt_acta rfhbsc_opt_actb : rel.
Lemma urr_acta l: acta (urr l). Proof. eauto 7 with rel. Qed.
Lemma urr_actb l: actb (urr l). Proof. unfold urr; rewrite <- seqA; eauto 7 with rel. Qed. 
Hint Resolve urr_acta urr_actb : rel.
Lemma rwr_acta l: acta (rwr l). Proof. eauto with rel. Qed.
Lemma rwr_actb l: actb (rwr l). Proof. unfold rwr; eauto with rel. Qed.
Hint Resolve rwr_acta rwr_actb : rel.

Lemma c_rel_actb i l' tm : actb tm -> actb (c_rel i l' tm).
Proof. unfold c_rel; rewrite <- !seqA; eauto with rel. Qed.
Lemma c_cur_actb i tm : actb tm -> actb (c_cur i tm).
Proof. unfold c_cur; eauto with rel. Qed.
Lemma c_acq_actb i tm : actb tm -> actb (c_acq i tm).
Proof. unfold c_acq; rewrite <- !seqA;
rewrite !inclusion_seq_eqv_r, !crE; rel_simpl; eauto 20 with rel. Qed.
Lemma m_rel_acta tm : acta tm -> acta (m_rel tm).
Proof. unfold m_rel; eauto with rel. Qed.
Lemma m_rel_actb tm : actb (m_rel tm).
Proof. unfold m_rel; eauto with rel. Qed.
Lemma S_tmr_acta l : acta (S_tmr l).
Proof. unfold S_tmr; eauto 10 with rel. Qed.
Lemma S_tmr_actb l : actb (S_tmr l).
Proof. eauto 10 with rel. Qed.

End WellFormedResults.

(******************************************************************************)
(** ** Coherence *)
(******************************************************************************)

Definition CoherentRW := 
  irreflexive (mo ;; rf ;; hb).
Definition CoherentWW := 
  irreflexive (mo ;; hb).
Definition CoherentWR := 
  irreflexive (mo ;; hb ;; transp rf).
Definition CoherentRR := 
  irreflexive (mo ;; rf ;; <| is_rlx_rw |> ;; hb ;; transp rf).
Definition CoherentRR':= 
  irreflexive (mo ;; rf ;; hb ;; <| is_rlx_rw |> ;; transp rf).
Definition CoherentRFR:= 
  irreflexive (mo ;; rf ;; hb ;; <| is_sc_fence |> ;; hb ;; transp rf).
Definition Atomicity  := 
  irreflexive (mo ;; mo ;; transp rmw ;; transp rf).
Definition CoherentSC := 
  irreflexive (mo ;; (clos_refl rf) ;; hb ;; sc ;; hb ;; (clos_refl (transp rf))).
Definition NoPromises := 
  acyclic (sb +++ rf +++ sc).

Definition Coherent :=
  << WF : Wf >> /\
  << Crw : CoherentRW >> /\
  << Cww : CoherentWW >> /\
  << Cwr : CoherentWR >> /\
  << Crr : CoherentRR >> /\
  << Crr' : CoherentRR' >> /\
  << Crfr : CoherentRFR >> /\
  << Cat : Atomicity >> /\
  << Csc : CoherentSC >> /\
  << Cnp : NoPromises >>.

Lemma coh_wf  (COH: Coherent) : Wf.
Proof. cdes COH; done. Qed.

Lemma wf_sb  (WF: Wf) : WfSB.
Proof. cdes WF; done. Qed.
Lemma wf_rmw  (WF: Wf) : WfRMW.
Proof. cdes WF; done. Qed.
Lemma wf_rf  (WF: Wf) : WfRF.
Proof. cdes WF; done. Qed.
Lemma wf_mo  (WF: Wf) : WfMO.
Proof. cdes WF; done. Qed.
Lemma wf_sc  (WF: Wf) : WfSC.
Proof. cdes WF; done. Qed.

Hint Resolve coh_wf wf_sb wf_rmw wf_rf wf_mo wf_sc.

Lemma wf_sc_tot (WF_SC: WfSC) a b 
  (INa: In a acts) (INb: In b acts)
  (SCa: is_sc_fence a) (SCb: is_sc_fence b)
  (NSC: ~ sc a b) (NEQ: a <> b) : sc b a.
Proof. cdes WF_SC; apply SC_TOT in NEQ; desf; eauto. Qed.

Lemma wf_mo_tot (WF_MO: WfMO) a b l
  (INa: In a acts) (INb: In b acts) (WRa: is_write a) (WRb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l)
  (NMO: ~ mo a b) (NEQ: a <> b) : mo b a.
Proof. cdes WF_MO; eapply MO_TOT in NEQ; desf; eauto. Qed.

(******************************************************************************)
(** ** Alternative presentation  *)
(******************************************************************************)

Lemma CoherentRWalt : CoherentRW <->
  forall a b (MO: mo a b) c (RF: rf b c) (HB: hb c a), False.
Proof.
unfold CoherentRW, irreflexive, seq.
split; ins; desf; eauto 8.
Qed.

Lemma CoherentWWalt : CoherentWW <->
  forall a b (MO: mo a b) (HB: hb b a), False.
Proof.
unfold CoherentWW, irreflexive, seq.
split; ins; desf; eauto 8.
Qed.

Lemma CoherentWRalt : CoherentWR <->
  forall a b (MO: mo a b) c (HB: hb b c) (RF: rf a c), False.
Proof.
unfold CoherentWR, irreflexive, seq.
split; ins; desf; eauto 8.
Qed.

Lemma CoherentRRalt : CoherentRR <->
  forall a b (MO: mo a b) c (RF: rf b c) d (HB: hb c d) 
      (RLX: is_rlx_rw c) (RF': rf a d), False.
Proof.
unfold CoherentRR, irreflexive, seq, eqv_rel, transp.
split; ins; desf; eauto 12.
Qed.

Lemma CoherentRR'alt : CoherentRR' <->
  forall a b (MO: mo a b) c (RF: rf b c) d (HB: hb c d) 
      (RLX: is_rlx_rw d) (RF': rf a d), False.
Proof.
unfold CoherentRR', irreflexive, seq, eqv_rel, transp.
split; ins; desf; eauto 12.
Qed.

Lemma CoherentRFRalt : CoherentRFR <->
  forall a b (MO: mo a b) c (RF: rf b c) d (HB: hb c d) 
      (FSC: is_sc_fence d) e (HB: hb d e) (RF': rf a e), False.
Proof.
unfold CoherentRFR, irreflexive, seq, eqv_rel, transp.
split; ins; desf; eauto 20.
Qed.

Lemma Atomicityalt : Atomicity <->
  forall a b (MO: mo a b) c (MO': mo b c) d (RMW: rmw d c) (RF: rf a d), False.
Proof.
unfold Atomicity, irreflexive, seq, eqv_rel, transp.
split; ins; desf; eauto 20.
Qed.

Lemma CoherentSCalt : CoherentSC <->
  forall a b c d e f (MO: mo a b) (RF: clos_refl rf b c) (HB: hb c d) 
         (SC: sc d e) (HB': hb e f) (RF': clos_refl rf a f), False.
Proof.
unfold CoherentSC, irreflexive, seq, eqv_rel, clos_refl, transp.
split; ins; desf; eauto 20.
Qed.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma inclusion_eqv_rt A dom (rel : relation A) :
  inclusion <| dom |> (clos_refl_trans rel).
Proof.
  unfold eqv_rel; red; ins; desf; vauto.
Qed.

Hint Immediate inclusion_eqv_rt : rel.

Section CoherenceProperties.

Hypothesis (COH: Coherent).

Lemma rmw_in_sb : inclusion rmw sb.
Proof. apply COH. Qed.

Lemma useq_in_sb_rf : inclusion useq (clos_trans (sb +++ rf)).
Proof.
  unfold useq; rewrite rmw_in_sb, inclusion_seq_eqv_r.
  eauto using inclusion_t_t2, inclusion_step2_ct with rel.
Qed.

Lemma rseq_in_sb_rf : inclusion rseq (clos_refl_trans (sb +++ rf)).
Proof.
  unfold rseq.
  rewrite !inclusion_seq_eqv_l, useq_in_sb_rf, inclusion_restr_eq, cr_of_t; ins.
  eapply inclusion_seq_rt; eauto with rel. 
Qed.

Lemma rel_in_sb_rf :inclusion rel (clos_refl_trans (sb +++ rf)).
Proof.
  unfold rel.
  rewrite !inclusion_seq_eqv_l, rseq_in_sb_rf; ins.
  eapply inclusion_seq_rt; eauto with rel. 
Qed.

Lemma sw_in_sb_rf : inclusion sw (clos_trans (sb +++ rf)).
Proof.
  unfold sw; rewrite !inclusion_seq_eqv_l, !inclusion_seq_eqv_r, rel_in_sb_rf; ins.
  rewrite <- rt_ct; apply inclusion_seq_mon; ins. 
  rewrite crE; rel_simpl; eauto using inclusion_step2_ct with rel. 
Qed.

Lemma hb_in_sb_rf : inclusion hb (clos_trans (sb +++ rf)).
Proof.
  unfold hb; rewrite sw_in_sb_rf; ins; eauto using inclusion_t_t2 with rel.
Qed.

Lemma hb_in_sb_rf_sc : inclusion hb (clos_trans (sb +++ rf +++ sc)).
Proof.
  rewrite hb_in_sb_rf; eauto with rel.
Qed.

Lemma irr_hb : irreflexive hb.
Proof.
  rewrite hb_in_sb_rf_sc; ins; apply COH.
Qed.

Lemma hb_mo a b (HB : hb a b) l
    (Wa : is_write a) (Wb : is_write b) 
    (LOCa: loc a = Some l) (LOCb: loc b = Some l) :
    mo a b.
Proof.
ins; eapply wf_mo_tot; eauto.
- eapply hb_actb; eauto.
- eapply hb_acta; eauto.
- intro. cdes COH; eapply Cww; unfold seq; eauto.
- intro; subst; eapply irr_hb; eauto.
Qed.

Lemma hb_in_sc x y (HB: hb x y) (A: is_sc_fence x) (B: is_sc_fence y) : sc x y.
Proof.
  destruct (classic (x=y)) as [|N]; subst.
    by apply irr_hb in HB; eauto.
  cdes COH; cdes WF; apply WF_SC in N; desc; intuition;
    try solve [eby eapply hb_acta | eby eapply hb_actb].
  eauto using hb_acta, hb_actb.
  exfalso; cdes COH; eapply Cnp, t_trans, hb_in_sb_rf_sc; vauto.
Qed.

Lemma hb_in_sc2 : inclusion (<| is_sc_fence |> ;; hb ;; <| is_sc_fence |>) sc.
Proof.
  rewrite seq_eqv_r, seq_eqv_l; red; ins; desf; eauto using hb_in_sc.
Qed.

Lemma sc_hb a b c (SC: sc a b) (HB: hb b c) (IS_SC: is_sc_fence c) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma hb_sc a b c (SC: sc b c) (HB: hb a b) (IS_SC: is_sc_fence a) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma BasicRMW : forall a b (MO: a=b \/ mo a b) c (RF: rf b c) (RMW: rmw c a), False.
Proof.
ins.
cdes COH; cdes WF; cdes WF_RMW.
destruct MO.
- subst.
  eapply Cnp with (x:=b).
  by eapply t_trans; eapply t_step; unfold union; eauto.
- eapply Crw; unfold seq; eauto 7 using sb_in_hb.
Qed.

Lemma rf_rmw_mo : inclusion (rf ;; rmw) mo.
Proof.
intros a b A; cdes COH.
red in WF; desc. 
red in WF_SB, WF_RMW, WF_RF, WF_MO; desc.
unfold seq in *; desf.
specialize (RF_DOMa a z A).
specialize (RF_LOC a z A).
specialize (RMW_DOMb z b A0).
specialize (RMW_LOC z b A0).
desf; eapply wf_mo_tot; eauto using BasicRMW.
Qed.

Lemma useq_mo : inclusion useq mo.
Proof.
 eapply inclusion_t_ind, COH.
 rewrite inclusion_seq_eqv_r; eauto using rf_rmw_mo. 
Qed.

Lemma rseq_mo : inclusion rseq (clos_refl mo).
Proof.
  unfold rseq.
  rewrite useq_mo, inclusion_seq_eqv_l, crE; rel_simpl.
  apply inclusion_union_l; [by rewrite !inclusion_seq_eqv_l|]. 
  rewrite <- !seqA; apply inclusion_seq_trans; ins.
    by apply cr_trans, COH.
  rewrite inclusion_seq_eqv_r.
  rewrite seq_eqv_l, seq_eqv_r; unfold restr_eq_rel in *; red; ins; desf.
  cdes COH; cdes WF; cdes WF_MO.
  assert (X: exists l, loc x = Some l); desc; try rewrite X in *.
    by unfold is_write, loc in *; destruct (lab x); ins; eauto.
  destruct (classic (x = y)) as [|N]; desf; vauto.
  right.
  eapply wf_mo_tot; eauto; try solve [eby eapply sb_acta | eby eapply sb_actb].
  intro; subst; eapply Cww; unfold seq; eauto using sb_in_hb.
Qed.

Lemma rel_mo : inclusion (<| is_write |> ;; rel) (clos_refl mo).
Proof.
  unfold rel; rewrite rseq_mo; rel_simpl.
  apply inclusion_union_l; [by rewrite !inclusion_seq_eqv_l|]. 
  unfold seq, eqv_rel; red; ins; desf; destruct z2 as [? ? []]; ins. 
Qed.

Lemma rel_hb_mo : inclusion rel (clos_refl hb ;; clos_refl mo).
Proof.
  unfold rel; rewrite rseq_mo, !inclusion_seq_eqv_l; rel_simpl.
  rewrite (crE hb), inclusion_seq_eqv_l; rel_simpl.
Qed.


Lemma basic_coherence_lemma a b (MO: mo a b) c 
  (RF: clos_refl rf b c) d (HB: clos_refl hb c d) (INV_RF: clos_refl rf a d)
  (RLX: a=d \/ c=d \/ b=c \/ is_rlx_rw d \/ is_rlx_rw c) : False.
Proof.
cdes COH; cdes WF; cdes WF_MO; cdes WF_RF.
unfold CoherentRW, CoherentWW, CoherentWR, CoherentRR, CoherentRR' in *.
unfold irreflexive, seq, transp, clos_refl, eqv_rel in *; desf; eauto 2;
try solve [eapply rf_mo; eauto| eapply inv_rf_mo; eauto|eapply irr_hb; eauto |
 eapply MO_IRR; erewrite RF_FUN; edone].
all: eauto 12.
Qed.

(******************************************************************************)
(** ** Basic properties of initialization *)
(******************************************************************************)

Lemma no_rmw_from_init a b (RMW: rmw a b) : is_proper a.
Proof.
cdes COH; cdes WF; cdes WF_SB; cdes WF_RMW.
assert (RMW' := RMW).
apply RMW_SB in RMW.
apply SB_TID in RMW.
desf.
red in RMW; desc.
unfold is_init, init_event in *; desc.
apply RMW_DOMa in RMW'.
destruct a as [??[]]; desf.
Qed.

Lemma no_mo_to_init a b (MO: mo a b) : is_proper b.
Proof.
apply init_events_wf1; eauto.
by eapply mo_actb; eauto.
intro.
cdes COH.
eapply Cww; unfold seq; eexists; split; eauto.
apply sb_in_hb.
cdes WF; cdes WF_SB.
apply SB_INIT; red; splits; eauto.
apply init_events_wf1; eauto.
by eapply mo_acta; eauto.
intro.
assert (a=b).
  by eapply same_init; eauto using loceq_mo.
subst; eapply WF_MO; edone.
by eapply mo_acta; eauto.
Qed.

Lemma no_hb_to_init a b (HB: hb a b) : is_proper b.
Proof.
cdes HB.
apply t_rt_step in HB; desc.
clear HB.
unfold union in *; desf.
by eapply sb_domb; eauto.
unfold sw, seq, eqv_rel in *; desf.
apply init_events_wf1; eauto.
by eapply hb_actb; eauto.
intro; eapply init_not_acq; eauto.
Qed.

Lemma no_rf_to_init a b (RF: rf a b) : is_proper b.
Proof.
apply init_events_wf1; eauto.
by eapply rf_actb; eauto.
intro.
eapply read_non_write.
eapply rf_domb; eauto.
eauto using init_is_write.
Qed.

Lemma no_sc_to_init a b (SC: sc a b) : is_proper b.
Proof.
apply init_events_wf1; eauto.
by eapply sc_actb; eauto.
intro.
eapply sc_domb in SC; eauto.
red in SC, H; desf.
Qed.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma eqv_doma A (d: A -> Prop) r (D: doma r d) :
  <| d |> ;; r <--> r.
Proof.
  rewrite seq_eqv_l; split; red; ins; desf; eauto.
Qed.

Lemma Coherent_urr l a b c 
  (MO: mo a b) (UR: urr l b c) (RF_INV: a=c \/ rf a c) : False.
Proof.
cdes COH; cdes WF; cdes WF_RF; cdes WF_MO; cdes WF_SC.
unfold urr, rfhbsc_opt, CoherentSC, CoherentRFR in *.
assert (forall a, is_sc_fence a /\ (is_write a \/ is_read a) -> False).
   ins; destruct a0 as [??[]]; ins; desf.
generalize basic_coherence_lemma; intro BASIC.
unfold irreflexive, seq, transp, eqv_rel, union in *; desf.
all: eauto 10 using hb_trans.
all: unfold clos_refl in *; desf; eauto.
all: eauto 10 using hb_trans.
all: eauto 20.
Qed.

Lemma Coherent_rwr l a b c 
  (MO: mo a b) (RW: rwr l b c) (RF_INV: a=c \/ (rf a c /\ is_rlx_rw c)) : False.
Proof.
  destruct RW.
  eapply Coherent_urr; eauto 9. tauto.
  unfold seq, clos_refl, eqv_rel in *.
  desf; try (by desf; eapply basic_coherence_lemma; eauto).
Qed.

Lemma step_seq_clos_refl R (TR: transitive R) (a b c : event) 
  (STEP: R a b) (RSTEP: clos_refl R b c): R a c.
Proof. destruct RSTEP; subst; eauto. Qed.
Lemma clos_refl_seq_step R (TR: transitive R) (a b c : event) 
  (STEP: R b c) (RSTEP: clos_refl R a b): R a c.
Proof. destruct RSTEP; subst; eauto. Qed.
Lemma clos_refl_seq_clos_refl R (TR: transitive R) (a b c : event) 
  (RSTEPa: clos_refl R a b) (RSTEPb: clos_refl R b c): clos_refl R a c.
Proof. destruct RSTEPa, RSTEPb; subst; eauto. right; eauto. Qed.

Lemma Coherent_urr_rel l a b c
  (MO: mo a b) (UR: urr l b c) (REL: rel c a) : False.
Proof.
  eapply rel_hb_mo in REL; destruct REL as (d & K & L).
  eapply Coherent_urr with (a:=d) (b:=b) (c:=d); eauto. 
    by red in L; desf; cdes COH; cdes WF; cdes WF_MO; eauto.
  eapply urr_cr_hb; unfold seq; eauto.
Qed.

Lemma Coherent_rwr_rel l a b c
  (MO: mo a b) (RW: rwr l b c) (REL: rel c a) : False.
Proof.
  unfold rwr, seq, eqv_rel in *; desc.
  destruct RW; desc; [by eapply Coherent_urr_rel; eauto|].
  eapply rel_hb_mo in REL; destruct REL as (d & K & L).
  eapply basic_coherence_lemma with (a:=d) (b:=b) (c:=z0) (d:=d); eauto; vauto.
    by red in L; cdes COH; cdes WF; cdes WF_MO; desf; eauto.
  eapply clos_refl_seq_clos_refl; eauto using hb_trans.
Qed.

Lemma Coherent_urr_sb l a b c d
  (MO: mo a b) (UR: urr l b c) (SB: sb c d) (RF_INV: a=d \/ rf a d) : False.
Proof.
  eapply Coherent_urr with (c:=d); try eauto.
  eapply urr_hb; try edone; eexists; split; eauto using sb_in_hb. 
Qed.

Lemma Coherent_rwr_sb l a b c d
  (MO: mo a b) (RW: rwr l b c) (SB: sb c d) (RF_INV: a=d \/ (rf a d /\ is_rlx_rw d)) : False.
Proof.
  eapply Coherent_rwr with (c:=d); try eauto.
  eapply rwr_hb; try edone; eexists; split; eauto using sb_in_hb.
Qed.

End CoherenceProperties.

End Consistency.

Definition t_rel tm (acts : list event) (sb rmw rf sc : relation event) i l' (l: Loc.t) :=  
  dom_rel (c_rel i l' (tm acts sb rmw rf sc l)).

Definition t_cur tm (acts : list event) (sb rmw rf sc : relation event) i (l: Loc.t) :=  
  dom_rel (c_cur i (tm acts sb rmw rf sc l)).

Definition t_acq tm (acts : list event) (sb rmw rf sc : relation event) i (l: Loc.t) :=  
  dom_rel (c_acq acts sb rmw rf i (tm acts sb rmw rf sc l)).

Definition msg_rel tm (acts : list event) (sb rmw rf sc : relation event) (l: Loc.t) :=
  m_rel acts sb rmw rf (tm acts sb rmw rf sc l).

Section Exports.

  Variable acts actsi : list event.
  Variables sb rmw rf mo sc : relation event.
  Hypothesis WF : Wf acts sb rmw rf mo sc.
  Variables i : thread_id.
  Variables l' l : Loc.t.
  Variables x y : event.

  Hint Resolve c_rel_doma c_cur_doma c_acq_doma.
  Hint Resolve urr_acta rwr_acta.
  Hint Resolve urr_actb rwr_actb.

  Lemma dom_in_acts rel (H: (doma rel (fun x => In x acts))) : 
    forall a (H1: dom_rel rel a), In a acts.
  Proof.
    unfold doma, dom_rel in *; ins; desf; eauto.
  Qed.

  Lemma acts_rel_urr : t_rel urr acts sb rmw rf sc i l' l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_rel_rwr : t_rel rwr acts sb rmw rf sc i l' l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.

  Lemma acts_cur_urr : t_cur urr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_cur_rwr : t_cur rwr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.

  Lemma acts_acq_urr : t_acq urr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto with rel. Qed.
  Lemma acts_acq_rwr : t_acq rwr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto with rel. Qed.

  Lemma acta_msg_urr : msg_rel urr acts sb rmw rf sc l x y -> In x acts.
  Proof. eapply m_rel_acta; eauto. Qed.
  Lemma acta_msg_rwr : msg_rel rwr acts sb rmw rf sc l x y -> In x acts.
  Proof. eapply m_rel_acta; eauto. Qed.

  Lemma actb_msg_urr : msg_rel urr acts sb rmw rf sc l x y -> In y acts.
  Proof. eapply m_rel_actb; eauto. Qed.
  Lemma actb_msg_rwr : msg_rel rwr acts sb rmw rf sc l x y -> In y acts.
  Proof. eapply m_rel_actb; eauto. Qed.

  Lemma acts_S_tm : S_tm acts sb rmw rf l x -> In x acts.
  Proof. eapply dom_in_acts; eauto 10 with rel. Qed.

  Lemma dom_dom_rel A (rel : relation A) f (H: doma rel f) a : dom_rel rel a -> f a. 
  Proof.
    unfold doma, dom_rel in *; ins; desf; eauto.
  Qed.

  Lemma msg_rel_urr_doma1: msg_rel urr acts sb rmw rf sc l x y ->  is_write x .
  Proof. apply m_rel_doma, urr_doma1. Qed.
  Lemma msg_rel_rwr_doma1: msg_rel rwr acts sb rmw rf sc l x y ->  is_write x .
  Proof. apply m_rel_doma, rwr_doma1. Qed.
  Lemma msg_rel_urr_doma2: msg_rel urr acts sb rmw rf sc l x y -> loc x = Some l.
  Proof. intro H; pattern x; revert H; apply m_rel_doma, urr_doma2. Qed.
  Lemma msg_rel_rwr_doma2: msg_rel rwr acts sb rmw rf sc l x y -> loc x = Some l.
  Proof. intro H; pattern x; revert H; apply m_rel_doma, rwr_doma2. Qed.

  Lemma t_rel_dom tmr d: 
    doma (tmr acts sb rmw rf sc l) d ->
    t_rel tmr acts sb rmw rf sc i l' l x -> d x .
  Proof. intro; apply dom_dom_rel; eauto with rel. Qed.
  Lemma t_acq_dom tmr d: 
    doma (tmr acts sb rmw rf sc l) d ->
    t_acq tmr acts sb rmw rf sc i l x -> d x .
  Proof. intro; apply dom_dom_rel; eauto with rel. Qed.
  Lemma t_cur_dom tmr d: 
    doma (tmr acts sb rmw rf sc l) d ->
    t_cur tmr acts sb rmw rf sc i l x -> d x .
  Proof. intro; apply dom_dom_rel; eauto with rel. Qed.

  Lemma S_tm_dom1 : S_tm acts sb rmw rf l x -> is_write x.
  Proof. apply dom_dom_rel; eauto using S_tmr_doma1 with rel. Qed.
  Lemma S_tm_dom2:  S_tm acts sb rmw rf l x -> loc x = Some l.
  Proof. apply dom_dom_rel with (f:= (fun a : event => loc a = Some l)). 
         eauto using S_tmr_doma2 with rel. Qed. 

  Section MonotonicityLemmas.

    Variables (tm tm' : list event -> relation event -> relation event -> relation event
                        -> relation event -> Loc.t -> relation event).
    Hypothesis (M: inclusion (tm acts sb rmw rf sc l) (tm' acts sb rmw rf sc l)).

    Ltac local_tac := unfold t_rel, t_cur, t_acq, dom_rel; ins; desf; 
                    eexists; eauto using c_rel_mon.

    Lemma t_rel_mon : 
      t_rel tm acts sb rmw rf sc i l' l x -> 
      t_rel tm' acts sb rmw rf sc i l' l x.
    Proof. local_tac; eapply c_rel_mon; eauto. Qed.

    Lemma t_cur_mon : 
      t_cur tm acts sb rmw rf sc i l x -> 
      t_cur tm' acts sb rmw rf sc i l x.
    Proof. local_tac; eapply c_cur_mon; eauto. Qed.

    Lemma t_acq_mon : 
      t_acq tm acts sb rmw rf sc i l x -> 
      t_acq tm' acts sb rmw rf sc i l x.
    Proof. local_tac; eapply c_acq_mon; eauto. Qed.

    Lemma t_rel_cur_mon : 
      t_rel tm acts sb rmw rf sc i l' l x -> 
      t_cur tm' acts sb rmw rf sc i l x.
    Proof. local_tac; eapply c_rel_cur_mon; eauto. Qed.
  
    Lemma t_cur_acq_mon : 
      t_cur tm acts sb rmw rf sc i l x -> 
      t_acq tm' acts sb rmw rf sc i l x.
    Proof. local_tac; eapply c_cur_acq_mon; eauto. Qed.

    Lemma t_rel_acq_mon :
      t_rel tm acts sb rmw rf sc i l' l x -> 
      t_acq tm' acts sb rmw rf sc i l x.
    Proof. local_tac; eapply c_rel_acq_mon; eauto. Qed.

  End MonotonicityLemmas.

End Exports.

Hint Resolve 
     acts_rel_urr acts_rel_rwr 
     acts_cur_urr acts_cur_rwr 
     acts_acq_urr acts_acq_rwr 
     acta_msg_urr acta_msg_rwr 
     actb_msg_urr actb_msg_rwr 
     acts_S_tm: acts.

Hint Resolve 
     inclusion_refl ur_in_rw 
     t_rel_mon t_cur_mon 
     t_acq_mon t_rel_cur_mon 
     t_cur_acq_mon t_rel_acq_mon : rel_mon.

Hint Resolve 
     msg_rel_urr_doma1 msg_rel_rwr_doma1
     msg_rel_urr_doma2 msg_rel_rwr_doma2
     (fun acts sb rmw rf sc i l' l x => 
        @t_rel_dom acts sb rmw rf sc i l' l x _ _ (urr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l' l x => 
        @t_rel_dom acts sb rmw rf sc i l' l x _ _ (rwr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l' l x => 
        @t_rel_dom acts sb rmw rf sc i l' l x _ _ (urr_doma2 (l:=l)))
     (fun acts sb rmw rf sc i l' l x => 
        @t_rel_dom acts sb rmw rf sc i l' l x _ _ (rwr_doma2 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_cur_dom acts sb rmw rf sc i l x _ _ (urr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_cur_dom acts sb rmw rf sc i l x _ _ (rwr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_cur_dom acts sb rmw rf sc i l x _ _ (urr_doma2 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_cur_dom acts sb rmw rf sc i l x _ _ (rwr_doma2 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_acq_dom acts sb rmw rf sc i l x _ _ (urr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_acq_dom acts sb rmw rf sc i l x _ _ (rwr_doma1 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_acq_dom acts sb rmw rf sc i l x _ _ (urr_doma2 (l:=l)))
     (fun acts sb rmw rf sc i l x => 
        @t_acq_dom acts sb rmw rf sc i l x _ _ (rwr_doma2 (l:=l)))
     urr_doma1 urr_doma2 rwr_doma1 rwr_doma2 S_tm_dom1 S_tm_dom2 : rel.

Require Import Setoid Permutation.

(* Add Parametric Morphism : transp with signature 
  same_relation ==> same_relation as transp_more.
Proof.
unfold restr_eq_rel, same_relation, inclusion; split; ins; desc; split; eauto.
Qed.  *)

Add Parametric Morphism : (restr_eq_rel loc) with signature 
  same_relation ==> same_relation as restr_eq_rel_loc_more.
Proof.
unfold restr_eq_rel, same_relation, inclusion; split; ins; desc; split; eauto.
Qed. 

Add Parametric Morphism : (useq) with signature 
  same_relation ==> same_relation ==> same_relation as useq_more.
Proof.
  unfold useq, same_relation; ins; repeat split; desc; unnw; eauto;
  eapply clos_trans_mori; eapply seq_mori, seq_mori; ins; eauto.
Qed. 

Add Parametric Morphism : (rseq) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as rseq_more.
Proof.
  by unfold rseq; ins; rewrite H, H0, H1.
Qed. 
 
Add Parametric Morphism : (rel) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as rel_more.
Proof.
  by unfold rel; ins; rewrite H, H0, H1.
Qed. 

Add Parametric Morphism : (sw) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as sw_more.
Proof.
  by unfold sw; ins; rewrite H, H0, H1.
Qed. 

Add Parametric Morphism : (hb) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as hb_more.
Proof.
  by unfold hb; ins; rewrite H, H0, H1.
Qed. 

Add Parametric Morphism : (WfACTS) with signature 
  eq ==> iff as WfACTS_more.
Proof.
  done.
Qed.

Add Parametric Morphism : (WfSB) with signature 
  eq ==> same_relation ==> iff as WfSB_more.
Proof.
  intros; unfold WfSB; unnw; rewrite H; red in H; split; intuition; eauto.
  all: specialize (H8 a b SAME_TID INa INb PROPERa PROPERb NEQ); desf; eauto.
Qed.

Add Parametric Morphism : (WfRMW) with signature 
  same_relation ==> same_relation ==> iff as WfRMW_more.
Proof.
  intros; unfold WfRMW; unnw; red in H, H0; split; intuition; eauto.
Qed.

Add Parametric Morphism : (WfRF) with signature 
  eq ==> same_relation ==> iff as WfRF_more.
Proof.
  intros; unfold WfRF; unnw; red in H; split; intuition; eauto.
  all: by exploit H9; eauto; intro; desf; eauto.
Qed.

Add Parametric Morphism : (WfMO) with signature 
  eq ==> same_relation ==> iff as WfMO_more.
Proof.
  intros; unfold WfMO; unnw; try rewrite H in *; red in H; intuition; eauto.
  all: red; ins; eapply H9 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism : (WfSC) with signature 
  eq ==> same_relation ==> iff as WfSC_more.
Proof.
  intros; unfold WfSC; unnw; try rewrite H in *; red in H; intuition; eauto.
  all: red; ins; eapply H8 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism : (Wf) with signature 
  eq ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==> iff as Wf_more.
Proof.
  intros; unfold Wf; unnw. 
  rewrite H, H0, H1, H2, H3; reflexivity.
Qed.

Add Parametric Morphism : (CoherentRW) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentRW_more.
Proof.
  intros; unfold CoherentRW; unnw.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Add Parametric Morphism : (CoherentWW) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentWW_more.
Proof.
  intros; unfold CoherentWW; unnw.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Add Parametric Morphism : (CoherentWR) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentWR_more.
Proof.
  intros; unfold CoherentWR; unnw.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Add Parametric Morphism : (CoherentRR) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentRR_more.
Proof.
  intros; unfold CoherentRR; unnw.
  rewrite H, H0, H1, H2; reflexivity. 
Qed.

Add Parametric Morphism : (CoherentRR') with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentRR'_more.
Proof.
  intros; unfold CoherentRR'; unnw.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Add Parametric Morphism : (CoherentRFR) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff 
      as CoherentRFR_more.
Proof.
  intros; unfold CoherentRFR; unnw.
  rewrite H, H0, H1, H2; reflexivity.
Qed.

Add Parametric Morphism : (Atomicity) with signature 
  same_relation ==> same_relation ==> same_relation ==> iff as Atomicity_more.
Proof.
  intros; unfold Atomicity; unnw.
  rewrite H, H0, H1; reflexivity.
Qed.

Add Parametric Morphism : (CoherentSC) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentSC_more.
Proof.
  intros; unfold CoherentSC; unnw.
  rewrite H, H0, H1, H2, H3; reflexivity.
Qed.

Add Parametric Morphism : (NoPromises) with signature 
  same_relation ==> same_relation ==> same_relation ==> iff as NoPromises_more.
Proof.
  intros; unfold NoPromises; rewrite H, H0, H1; reflexivity.
Qed.

Add Parametric Morphism : (Coherent) with signature 
  eq ==> same_relation  ==> same_relation  ==> same_relation  
      ==> same_relation ==> same_relation ==> iff as Coherent_more.
Proof.
  intros; unfold Coherent; unnw.
  rewrite H, H0, H1, H2, H3; reflexivity.
Qed. 
