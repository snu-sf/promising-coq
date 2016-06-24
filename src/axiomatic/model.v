(******************************************************************************)
(** * Definitions of the axiomatic memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import sflib.
Require Import paco.

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
  Variable sb : event -> event -> Prop. 
  Variable rmw : event -> event -> Prop. 
  Variable rf : event -> event -> Prop. 
  Variable mo : event -> event -> Prop. 
  Variable sc : event -> event -> Prop. 

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

  Definition useq := clos_trans (rf ;; rmw).
   
  Definition rseq :=
    <| fun a => In a acts |> ;; 
    <| is_write |> ;;
    clos_refl (restr_eq_rel loc sb) ;;
    <| is_write |> ;;
    clos_refl useq.
   
  Definition rel :=
    <| is_ra |> ;; 
    (<| is_write |> +++ <| is_wfence |> ;; sb) ;; 
    rseq.
   
  Definition sw :=
    rel ;; rf ;; clos_refl (<| is_rlx |> ;; sb ;; <| is_rfence |>) ;; 
    <| is_ra |>.
   
  Definition hb :=
    clos_trans (sb +++ sw).

(******************************************************************************)
(** ** Additional derived relations for simulation *)
(******************************************************************************)

  Definition rfhbsc := clos_refl rf ;; clos_refl (hb ;; <| is_wfence |>) ;; sc.

  Definition urr := 
    <| fun a => In a acts |> ;; clos_refl (rfhbsc ;; <| is_wfence |>) ;; clos_refl hb.

  Definition rwr := 
    urr +++ <| fun a => In a acts |> ;; clos_refl rf ;; clos_refl hb.

  Definition scr := 
    rwr +++ 
    <| fun a => In a acts |> ;; clos_refl (rfhbsc ;; <| is_write |>) ;; clos_refl hb.

  Definition urr_rel := urr ;; rel.
  Definition rwr_rel := rwr ;; rel.
  Definition scr_rel := scr ;; rel.

  Definition m_rel l tm_relation := 
    <| fun x => is_write x /\ loc x = Some l |> ;; tm_relation.

  Definition c_rel i l' l tm_relation :=  
    m_rel l tm_relation ;;
    <| is_ra |> ;;
    <| fun x => is_write x /\ loc x = Some l' \/ is_wfence x |> ;;
    <| fun x => thread x = i |>.

  Definition c_cur i l tm_relation := 
    <| fun x => is_write x /\ loc x = Some l |> ;; 
    tm_relation ;; 
    <| fun x => thread x = i |>.

  Definition c_acq i l tm_relation :=  
    m_rel l tm_relation ;; rf ;; <| is_rlx |> ;; <| fun x => thread x = i |>.

  Definition S_tm_relation l := 
    <| fun x => is_write x /\ loc x = Some l |> ;; 
    <| fun x => In x acts |> ;; 
    clos_refl rf ;; clos_refl (hb ;; <| is_wfence |>) ;; <| is_sc |>.

  Definition S_tm l := dom_rel (S_tm_relation l).


(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

  Lemma sb_in_hb : inclusion sb hb.
  Proof. vauto. Qed.

  Lemma sw_in_hb : inclusion sw hb.
  Proof. vauto. Qed.
   
  Lemma hb_trans : 
    forall x y z, hb x y -> hb y z -> hb x z.
  Proof.
    vauto.
  Qed.
   
  Lemma ur_in_rw : inclusion urr rwr.
  Proof. vauto. Qed.
   
  Lemma rw_in_sc : inclusion rwr scr.
  Proof. vauto. Qed.
   
  Lemma ur_in_sc : inclusion urr scr.
  Proof. transitivity rwr; vauto. Qed.

  Lemma reflexive_ur a (IN: In a acts): urr a a.
  Proof. repeat (eexists; splits; eauto). Qed.

  Lemma reflexive_rw a (IN: In a acts): rwr a a.
  Proof. left; apply reflexive_ur; done. Qed.

  Lemma reflexive_sc a (IN: In a acts): scr a a.
  Proof. left; apply reflexive_rw; done. Qed.

  Lemma hb_hb : inclusion (hb ;; hb) hb.
  Proof. unfold seq, inclusion; ins; desf; vauto. Qed.

  Lemma cr_hb_hb : inclusion (clos_refl hb ;; hb) hb.
  Proof. rewrite crE, seq_union_l, hb_hb; rel_simpl. Qed.

  Lemma urr_hb : inclusion (urr ;; hb) urr.
  Proof.
    unfold urr; rewrite !seqA, cr_hb_hb; eauto with rel.
  Qed.  

  Lemma rwr_hb : inclusion (rwr ;; hb) rwr. 
  Proof.
    unfold rwr; rewrite seq_union_l, urr_hb, !seqA, cr_hb_hb.
    eauto 8 with rel.
  Qed.

  Lemma scr_hb : inclusion (scr ;; hb) scr.
  Proof.
    unfold scr; rewrite seq_union_l, rwr_hb, !seqA, cr_hb_hb.
    eauto 8 with rel.
  Qed.

  Lemma rseq_alt : 
    rseq <--> 
    <|fun a => In a acts|> ;; <|is_write|> +++
    <|fun a => In a acts|> ;; <|is_write|> ;; useq +++
    <|fun a => In a acts|> ;; <|is_write|> ;; restr_eq_rel loc sb ;; <|is_write|> +++
    <|fun a => In a acts|> ;; <|is_write|> ;; restr_eq_rel loc sb ;; 
    eqv_rel is_write ;; useq.
  Proof.
  unfold rseq; rewrite !crE; rel_simpl; rewrite !seq_eqvK, !(seq2 (seq_eqvK _)).
  unfold same_relation, inclusion, union; split; ins; desf; eauto. 
  Qed.

(******************************************************************************)
(** ** Well-formed relations *)
(******************************************************************************)

Definition WfSB := 
  << SB_ACTa: forall a b (SB: sb a b), In a acts >> /\
  << SB_ACTb: forall a b (SB: sb a b), In b acts >> /\
  << SB_TID: forall a b (SB: sb a b), (thread a = thread b) >> /\
  << CsbT: transitive sb >>.

Definition WfRMW := 
  << RMW_DOMa: forall a b (RMW: rmw a b), is_read a >> /\
  << RMW_DOMb: forall a b (RMW: rmw a b), is_write b >> /\
  << RMW_LOC: forall a b (RMW: rmw a b), exists l, (loc a = Some l) /\ (loc b = Some l) >> /\
  << RMW_SB: forall a b (RMW: rmw a b), sb a b >> /\
  << RMW_SBI: forall a b (RMW: rmw a b) c (SB: sb c b)(NEQ: c <> a), sb c a >> /\
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
  << SC_DOMa: forall a b (SC: sc a b), is_sc a >> /\
  << SC_DOMb: forall a b (SC: sc a b), is_sc b >> /\
  << SC_IRR: irreflexive sc >> /\
  << SC_T: transitive sc >> /\
  << SC_TOT: is_total (fun a => In a acts /\ is_sc a) sc >>.

Definition Wf :=
  << WF_SB : WfSB >> /\
  << WF_RMW : WfRMW >> /\
  << WF_RF : WfRF >> /\
  << WF_MO : WfMO >> /\
  << WF_SC : WfSC >>.


(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

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
Lemma sc_doma : doma sc is_sc.
Proof. cdes WF; cdes WF_SC; eauto. Qed.
Lemma sc_domb : domb sc is_sc.
Proof. cdes WF; cdes WF_SC; eauto. Qed.
Lemma useq_doma : doma useq is_write.
Proof. unfold useq; eauto using rf_doma with rel. Qed.
Lemma useq_domb : domb useq is_write.
Proof. unfold useq; eauto using rmw_domb with rel. Qed.
Lemma rseq_doma : doma rseq is_write.
Proof. unfold rseq; eauto with rel. Qed.
Lemma rseq_domb : domb rseq is_write.
Proof. unfold rseq; eauto using useq_domb with rel. Qed.
Lemma rel_doma : doma rel is_ra.
Proof. unfold rel; eauto with rel. Qed.
Lemma rel_domb : domb rel is_write.
Proof. unfold rel; eauto using rseq_domb with rel. Qed.
Lemma sw_doma : doma sw is_ra.
Proof. unfold sw; eauto using rel_doma with rel. Qed.
Lemma sw_domb : domb sw is_ra.
Proof. unfold sw; eauto with rel. Qed.

Lemma rfhbsc_domb : domb rfhbsc is_sc.
Proof. unfold rfhbsc; eauto using sc_domb with rel. Qed.

Lemma c_cur_doma i l tm_relation: doma (c_cur i l tm_relation) (fun a : event => is_write a /\ loc a = Some l).
Proof. unfold c_cur; eauto with rel. Qed.
Lemma c_cur_doma1 i l tm_relation: doma (c_cur i l tm_relation) is_write.
Proof. unfold doma; ins; exploit c_cur_doma; ins; desc; eauto. Qed.
Lemma c_cur_doma2 i l tm_relation: doma (c_cur i l tm_relation) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit c_cur_doma; ins; desc; eauto. Qed.
Lemma c_cur_domb i l tm_relation: domb (c_cur i l tm_relation) (fun a => thread a = i).
Proof. unfold c_cur; eauto with rel. Qed.

Lemma m_rel_doma l tm: doma (m_rel l tm) (fun a => is_write a /\ loc a = Some l).
Proof. unfold m_rel; eauto with rel. Qed.
Lemma m_rel_doma1 l tm: doma (m_rel l tm) is_write.
Proof. unfold doma; ins; exploit m_rel_doma; ins; desc; eauto. Qed.
Lemma m_rel_doma2 l tm: doma (m_rel l tm) (fun a => loc a = Some l).
Proof. unfold doma; ins; exploit m_rel_doma; ins; desc; eauto. Qed.
Lemma m_rel_domb l tm: domb tm is_write -> domb (m_rel l tm) is_write.
Proof. unfold m_rel; eauto using rel_domb with rel. Qed.

Lemma c_acq_doma i l tm : doma (c_acq i l tm) (fun a => is_write a /\ loc a = Some l).
Proof. unfold c_acq; eauto using m_rel_doma with rel. Qed.
Lemma c_acq_doma1 i l tm: doma (c_acq i l tm) is_write.
Proof. unfold doma; ins; exploit c_acq_doma; ins; desc; eauto. Qed.
Lemma c_acq_doma2 i l tm: doma (c_acq i l tm) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit c_acq_doma; ins; desc; eauto. Qed.
Lemma c_acq_domb1 i l tm: domb (c_acq i l tm) (fun a => thread a = i).
Proof. unfold c_acq; eauto with rel. Qed.
Lemma c_acq_domb2 i l tm: domb (c_acq i l tm) is_read.
Proof. unfold c_acq; rewrite <- !seqA; eauto 8 using rf_domb with rel. Qed.
Lemma c_acq_domb3 i l tm: domb (c_acq i l tm) is_rlx.
Proof. unfold c_acq; eauto with rel. Qed.

Lemma S_tm_relation_doma l: doma (S_tm_relation l) (fun a => is_write a /\ loc a = Some l).
Proof. unfold S_tm_relation; eauto with rel. Qed.
Lemma S_tm_relation_doma1 l: doma (S_tm_relation l) is_write.
Proof. unfold doma; ins; exploit S_tm_relation_doma; ins; desc; eauto. Qed.
Lemma S_tm_relation_doma2 l: doma (S_tm_relation l) (fun a => loc a = Some l).
Proof. unfold doma; ins; exploit S_tm_relation_doma; ins; desc; eauto. Qed.
Lemma S_tm_relation_domb l: domb (S_tm_relation l) is_sc.
Proof. unfold S_tm_relation; eauto 8 with rel. Qed.


Definition is_f (R : event -> Prop) f := forall (WF: Wf) a (H: R a), f a.

Lemma dom_dom_rel rel f (H: doma rel f) : is_f (dom_rel rel) f. 
Proof.
unfold is_f, doma, dom_rel in *; ins; desf; eauto.
Qed.

Hint Resolve
 dom_dom_rel : rel.


(*
Lemma c_cur_ur_dom1 i l : is_f (c_cur_ur i l) is_write.
Proof. unfold c_cur_ur; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_rw_dom1 i l : is_f (c_cur_rw i l) is_write.
Proof. unfold c_cur_rw; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_sc_dom1 i l : is_f (c_cur_sc i l) is_write.
Proof. unfold c_cur_sc; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_ur_dom2 i l : is_f (c_cur_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_ur; eauto using c_cur_doma2 with rel. Qed.
Lemma c_cur_rw_dom2 i l : is_f (c_cur_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_rw; eauto using c_cur_doma2 with rel. Qed.
Lemma c_cur_sc_dom2 i l : is_f (c_cur_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_sc; eauto using c_cur_doma2 with rel. Qed.

Lemma c_acq_ur_dom1 i l : is_f (c_acq_ur i l) is_write.
Proof. unfold c_acq_ur; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_rw_dom1 i l : is_f (c_acq_rw i l) is_write.
Proof. unfold c_acq_rw; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_sc_dom1 i l : is_f (c_acq_sc i l) is_write.
Proof. unfold c_acq_sc; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_ur_dom2 i l : is_f (c_acq_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_ur; eauto using c_acq_doma2 with rel. Qed.
Lemma c_acq_rw_dom2 i l : is_f (c_acq_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_rw; eauto using c_acq_doma2 with rel. Qed.
Lemma c_acq_sc_dom2 i l : is_f (c_acq_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_sc; eauto using c_acq_doma2 with rel. Qed.

Lemma S_tm_dom1 l : is_f (S_tm l) is_write.
Proof. unfold S_tm; eauto using S_tm_relation_doma1 with rel. Qed.
Lemma S_tm_dom2 l : is_f (S_tm l) (fun a : event => loc a = Some l).
Proof. unfold S_tm; eauto using S_tm_relation_doma2 with rel. Qed.
*)


(* Lemma conflicting_domains (WF: Wf) (R T: event -> event -> Prop) a b (A: R a b) (B: T a b) 
(f1 f2: event -> Prop) (CONFLICT: forall a, f1 a /\ f2 a -> False) 
(C: doma R f1) (D: doma T f2) : False.
Proof.
 eauto.
Qed.

Lemma conflicting_codomains (WF: Wf) (R T: event -> event -> Prop) a b (A: R a b) (B: T a b) 
(f1 f2: event -> Prop) (CONFLICT: forall a, f1 a /\ f2 a -> False) 
(C: domb R f1) (D: domb T f2) : False.
Proof.
 eauto.
Qed.
 *)

Lemma rf_to_non_read a b (RF: rf a b) (NON_READ: ~ is_read b) : False.
Proof.
  exploit rf_domb; eauto.
Qed.

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

Lemma rel_rf a b c (RA: is_ra c) (REL: rel a b) (RF: rf b c) : sw a c.
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
Lemma rfhbsc_acta : acta rfhbsc. Proof. eauto with rel. Qed.
Lemma rfhbsc_actb : actb rfhbsc. Proof. eauto with rel. Qed.
Hint Resolve rfhbsc_acta rfhbsc_actb : rel.
Lemma urr_acta : acta urr. Proof. eauto with rel. Qed.
Lemma urr_actb : actb urr. Proof. unfold urr; rewrite <- seqA; eauto with rel. Qed. 
Hint Resolve urr_acta urr_actb : rel.
Lemma rwr_acta : acta rwr. Proof. eauto with rel. Qed.
Lemma rwr_actb : actb rwr. Proof. unfold rwr; rewrite <- seqA; eauto with rel. Qed.
Hint Resolve rwr_acta rwr_actb : rel.
Lemma scr_acta : acta scr. Proof. eauto with rel. Qed.
Lemma scr_actb : actb scr. Proof. unfold scr; rewrite <- seqA; eauto with rel. Qed.
Hint Resolve scr_acta scr_actb : rel.
Lemma urr_rel_acta : acta urr_rel. Proof. eauto with rel. Qed.
Lemma urr_rel_actb : actb urr_rel. Proof. eauto with rel. Qed.
Hint Resolve urr_rel_acta urr_rel_actb : rel.
Lemma rwr_rel_acta : acta rwr_rel. Proof. eauto with rel. Qed.
Lemma rwr_rel_actb : actb rwr_rel. Proof. eauto with rel. Qed.
Hint Resolve rwr_rel_acta rwr_rel_actb : rel.
Lemma scr_rel_acta : acta scr_rel. Proof. eauto with rel. Qed.
Lemma scr_rel_actb : actb scr_rel. Proof. eauto with rel. Qed.
Hint Resolve scr_rel_acta scr_rel_actb : rel.

Lemma m_rel_acta l tm : acta tm -> acta (m_rel l tm).
Proof. eauto with rel. Qed.
Lemma m_rel_actb l tm : actb tm -> actb (m_rel l tm).
Proof. eauto with rel. Qed.

Lemma c_rel_acta i l l' tm : acta tm -> acta (c_rel i l l' tm).
Proof. unfold c_rel; eauto with rel. Qed.
Lemma c_rel_actb i l l' tm : actb tm -> actb (c_rel i l l' tm).
Proof. unfold c_rel; rewrite <- !seqA; eauto using m_rel_actb with rel. Qed.
Lemma c_cur_acta i l tm : acta tm -> acta (c_cur i l tm).
Proof. unfold c_cur; eauto with rel. Qed.
Lemma c_cur_actb i l tm : actb tm -> actb (c_cur i l tm).
Proof. unfold c_cur; rewrite <- !seqA; eauto using m_rel_actb with rel. Qed.
Lemma c_acq_acta i l tm : acta tm -> acta (c_acq i l tm).
Proof. unfold c_acq; eauto with rel. Qed.
Lemma c_acq_actb i l tm : actb tm -> actb (c_acq i l tm).
Proof. unfold c_acq; rewrite <- !seqA; eauto using m_rel_actb with rel. Qed.

Lemma S_tm_relation_acta l : acta (S_tm_relation l).
Proof. unfold S_tm_relation; eauto with rel. Qed.

Lemma S_tm_relation_actb l : actb (S_tm_relation l).
Proof. 
  unfold S_tm_relation; rewrite !inclusion_seq_eqv_r, inclusion_seq_eqv_l, !crE; 
  rel_simpl. 
Qed.


Definition in_acts (R : event -> Prop) := forall (WF: Wf) a (H: R a), In a acts.

Lemma dom_in_acts rel (H: acta rel) : in_acts (dom_rel rel). 
Proof.
unfold in_acts, doma, dom_rel in *; ins; desf; eauto.
Qed.

Hint Resolve dom_in_acts : rel.

(*
Lemma c_cur_ur_in_acts i l : in_acts (c_cur_ur i l).
Proof. unfold c_cur_ur, c_cur; eauto using ur_acta with actab. Qed.
Lemma c_cur_rw_in_acts i l : in_acts (c_cur_rw i l).
Proof. unfold c_cur_rw, c_cur; eauto using rw_acta with actab. Qed.
Lemma c_cur_sc_in_acts i l : in_acts (c_cur_sc i l).
Proof. unfold c_cur_sc, c_cur; eauto using scr_acta with actab. Qed.
Lemma c_acq_ur_in_acts i l : in_acts (c_acq_ur i l).
Proof. unfold c_acq_ur, c_acq, m_rel; eauto using ur_acta with actab. Qed.
Lemma c_acq_rw_in_acts i l : in_acts (c_acq_rw i l).
Proof. unfold c_acq_rw, c_acq, m_rel; eauto using rw_acta with actab. Qed.
Lemma c_acq_sc_in_acts i l : in_acts (c_acq_sc i l).
Proof. unfold c_acq_sc, c_acq, m_rel; eauto using scr_acta with actab. Qed.
*)

Lemma S_tm_acta l : in_acts (S_tm l).
Proof. unfold S_tm; eauto using S_tm_relation_acta with rel. Qed.

End WellFormedResults.

(******************************************************************************)
(** ** Coherence *)
(******************************************************************************)

Definition BasicRMW :=
  forall a b (MO: a=b \/ mo a b) c (RF: rf b c) (RMW: rmw c a), False.

(*Definition CoherentRW1 :=
  forall a b (RF: rf a b) (HB: hb b a), False.*)

Definition CoherentRW2 :=
  forall a b (MO: mo a b) c (RF: rf b c) (HB: hb c a), False.

Definition CoherentWW :=
  forall a b (MO: mo a b) (HB: hb b a), False.

Definition CoherentWR :=
  forall a b (MO: mo a b) c (HB: hb b c) (RF: rf a c), False.

Definition CoherentRR :=
  forall a b (MO: mo a b) c (RF: rf b c) d (HB: hb c d) (RLX: is_rlx d) (RF': rf a d),
    False.

Definition Atomicity :=
  forall a b (MO: mo a b) c (MO': mo b c) d (RMW: rmw d c) (RF: rf a d), False.

Definition CoherentSC :=
  forall a b c d e f (MO: mo a b) 
         (RF: (clos_refl rf) b c) (HBF: c=d \/ (hb c d) /\ is_wfence d /\ is_sc d)
         (SC: sc d e) (FHB: e=f \/ is_wfence e /\ is_sc e /\ (hb e f)) 
         (RF': (clos_refl rf) a f), False.

Definition NoPromises :=
  acyclic (sb +++ rf +++ sc).

Definition Coherent :=
  << WF : Wf >> /\
  << Crmw : BasicRMW >> /\
(*  << Crw1 : CoherentRW1 >> /\*)
  << Crw2 : CoherentRW2 >> /\
  << Cww : CoherentWW >> /\
  << Cwr : CoherentWR >> /\
  << Crr : CoherentRR >> /\
  << Cat : Atomicity >> /\
  << Csc : CoherentSC >> /\
  << Cnp : NoPromises >>.

Lemma coh_wf  (COH: Coherent) : Wf.
Proof. cdes COH; done. Qed.

Hint Resolve coh_wf.

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
  unfold useq; rewrite rmw_in_sb;
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
  ins.
  destruct (classic (a=b)) as [|N].
(* destruct (eqP a b) as [|N]. desf. *)
  by desf; exfalso; eapply irr_hb; eauto.
  cdes COH; cdes WF; desf; red in WF_MO; desf.
  eapply MO_TOT in N; eauto.
  desf; exfalso; eapply Cww; eauto.
  splits; eauto.
  eapply hb_acta; eauto.
  splits; eauto.
  eapply hb_actb; eauto.
Qed.

Lemma hb_in_sc x y (HB: hb x y) (A: is_sc x) (B : is_sc y) : sc x y.
Proof.
  destruct (classic (x=y)) as [|N]; desf.
    by apply irr_hb in HB; eauto.
  cdes COH; cdes WF; apply WF_SC in N; desf; intuition;
    try solve [eby eapply hb_acta | eby eapply hb_actb].
  eauto using hb_acta, hb_actb.
  exfalso; cdes COH; eapply Cnp, t_trans, hb_in_sb_rf_sc; vauto.
Qed.

Lemma hb_in_sc2 : inclusion (<| is_sc |> ;; hb ;; <| is_sc |>) sc.
Proof.
  rewrite seq_eqv_r, seq_eqv_l; red; ins; desf; eauto using hb_in_sc.
Qed.

Lemma sc_hb a b c (SC: sc a b) (HB: hb b c) (IS_SC: is_sc c) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma hb_sc a b c (SC: sc b c) (HB: hb a b) (IS_SC: is_sc a) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma mo_sc a b (MO: mo a b) (IS_SCa: is_sc a) (IS_SCb: is_sc b) : sc a b.
Proof.
  cdes COH; cdes WF; cdes WF_SC; cdes WF_MO.
  destruct (classic (a=b)) as [|N].
    by desf; exfalso; eauto.
  apply SC_TOT in N; desf; eauto.
  exfalso; eapply Csc; eauto.
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
desf.
destruct (classic (a=b)) as [|N].
- subst; exfalso; eapply Crmw with (a:=b) (b:=b); eauto.
- eapply MO_TOT in N; eauto.
  desf; try done.
  exfalso; eapply Crmw; eauto.
Qed.

Lemma useq_mo : inclusion useq mo.
Proof.
 eapply inclusion_t_ind, COH; eauto using rf_rmw_mo. 
Qed.

Lemma rseq_mo : inclusion rseq (clos_refl mo).
Proof.
  unfold rseq.
  rewrite useq_mo, inclusion_seq_eqv_l, crE; rel_simpl.
  apply inclusion_union_l; [by rewrite !inclusion_seq_eqv_l|]. 
  rewrite <- !seqA; apply inclusion_seq_trans; ins.
    by apply cr_trans, COH.
  rewrite seq_eqv_l, seq_eqv_r; unfold restr_eq_rel in *; red; ins; desf.
  cdes COH; cdes WF; cdes WF_MO.
  assert (X: exists l, loc x = Some l); desc; try rewrite X in *.
    by unfold is_write, loc in *; destruct (lab x); ins; eauto.
  destruct (classic (x = y)) as [|N]; desf; vauto.
  eapply MO_TOT in N; desf; intuition; eauto; try solve [eby eapply sb_acta | eby eapply sb_actb].
  edestruct Cww; eauto using sb_in_hb.
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
  (RF: (clos_refl rf) b c) d (HB: (clos_refl hb) c d) (INV_RF: (clos_refl rf) a d)
  (RLX: a=d \/ c=d \/ b=c \/ is_rlx d) : False.
Proof.
cdes COH; cdes WF; cdes WF_MO; cdes WF_RF.
unfold seq, clos_refl in *.
desf; eauto 2;
try solve [eapply rf_mo; eauto| eapply inv_rf_mo; eauto|eapply irr_hb; eauto |
 eapply MO_IRR; erewrite RF_FUN; edone].
Qed.

(*
Lemma ur_rel (COH: Coherent) a b c l (UR: ur_relation a b) (REL: rel b c) 
  (WRITE: is_write a) (LOC: loc a = Some l) : m_rel_ur l a c.
Proof.
red; red; unfold eqv_rel.
eexists; splits; try edone.
eexists; edone.
Qed.

Lemma rw_rel (COH: Coherent) a b c l (RW: rw_relation a b) (REL: rel b c) 
  (WRITE: is_write a) (LOC: loc a = Some l) : m_rel_rw l a c.
Proof.
red; red; unfold eqv_rel.
eexists; splits; try edone.
eexists; edone.
Qed.

Lemma scr_rel (COH: Coherent) a b c l (SC: sc_relation a b) (REL: rel b c) 
  (WRITE: is_write a) (LOC: loc a = Some l) : m_rel_sc l a c.
Proof.
red; red; unfold eqv_rel.
eexists; splits; try edone.
eexists; edone.
Qed.
*)

Lemma rf_in_rw (WF: Wf) : inclusion rf rwr.
Proof. right; repeat (eexists; splits; eauto); eapply rf_acta; eauto. Qed.


(* Lemma S_tm_sc (COH: Coherent) a b c l (S_TM: S_tm_relation l a b) (SC: sc b c) 
  (WRITE: is_write a) (LOC: loc a = Some l) : sc_relation a c.
Proof.
red; red; unfold eqv_rel.
eexists; splits; try edone.
eapply S_tm_relation_acta; cdes COH; try edone.
red in S_TM; unfold seq, eqv_rel, clos_refl in *; desf.
- exists b; splits; eauto.
  exists c; splits; eauto; right; repeat (eexists; splits; eauto).
- exists z2; splits; eauto.
  exists c; splits; eauto.
  right; exists b; splits; eauto; right; repeat (eexists; splits; eauto).
- exists z2; splits; eauto.
  exists c; splits; eauto.
  right; exists b; splits; eauto; right; repeat (eexists; splits; eauto).
Qed. *)

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma Coherent_ur a b c 
  (MO: mo a b) (UR: urr b c) (RF_INV: a=c \/ rf a c) : False.
Proof.
cdes COH.
red in WF; desc. 
unfold urr, rfhbsc, seq, clos_refl in *; desc.
cdes WF_MO; unfold WfSC in *; desc.
unfold eqv_rel in *.
destruct UR0; desc; subst.
  by eapply basic_coherence_lemma; eauto.
desf; eapply Csc; eauto.
Qed.

Lemma Coherent_rw a b c 
  (MO: mo a b) (RW: rwr b c) (RF_INV: a=c \/ (rf a c /\ is_rlx c)) : False.
Proof.
destruct RW.
eapply Coherent_ur; eauto. tauto.
unfold rfhbsc, seq, clos_refl in *.
cdes COH; cdes WF; cdes WF_MO; unfold WfSC in *; desc.
unfold eqv_rel in *.
desf; try (by desf; eapply basic_coherence_lemma; eauto).
Qed.

(*
Lemma Coherent_sc a b c  (SCc: is_sc c) 
  (MO: mo a b) (SC: scr b c) (RF_INV: a=c \/ rf a c) : False.
Proof.
  destruct SC.
    by eapply Coherent_rw; eauto; desf; eauto with acts.
  apply seq_eqv_l in H; unfold rfhbsc, seq, clos_refl, eqv_rel in *; desc.
  cdes COH; cdes WF; cdes WF_MO; unfold WfSC in *; desc.
  assert (is_sc z).
    desf; eauto.
    exfalso; eauto.
    exfalso; eauto.


  assert (sc z c). 


    destruct H0. by subst. eby eapply sc_hb.
desf; eapply Csc; try edone; eauto using hb_trans.
Qed.
*)


Lemma Coherent_urr_sb a b c d
  (MO: mo a b) (UR: urr b c) (SB: sb c d) (RF_INV: a=d \/ rf a d) : False.
Proof.
  eapply Coherent_ur with (c:=d); try eauto.
  eapply urr_hb; try edone; eexists; split; eauto using sb_in_hb. 
Qed.

Lemma Coherent_rwr_sb a b c d
  (MO: mo a b) (RW: rwr b c) (SB: sb c d) (RF_INV: a=d \/ (rf a d /\ is_rlx d)) : False.
Proof.
  eapply Coherent_rw with (c:=d); try eauto.
  eapply rwr_hb; try edone; eexists; split; eauto using sb_in_hb.
Qed.

(*
Lemma Coherent_scr_sb a b c d
  (SCc: is_sc d) (MO: mo a b) (SC: scr b c) (SB: sb c d) (RF_INV: a=d \/ rf a d) : False.
Proof.
  eapply Coherent_scr with (c:=d); try eauto.
  eapply scr_hb; try edone.
  eapply sb_in_hb; eauto.
Qed.


Lemma Coherent_m_rel_rw (COH: Coherent) a b x (LOC: loc b = Some x) 
  (RW: m_rel_rw x a b) (MO: mo b a) : False.
Proof.
cdes COH. cdes WF. unfold WfMO in *; desc.
unfold m_rel_rw, m_rel_rw, m_rel, seq, eqv_rel in *; desc; subst.
  apply rel_hb_mo in RW1; ins.
clear - COH MO RW0 RW1 RW2 RW3 MO_T LOC.
by unfold clos_refl, seq in *; desf; eauto using Coherent_rw, rw_hb.
Qed.
*)

End CoherenceProperties.

End Consistency.

Definition t_rel tm (acts : list event) (sb rmw rf sc : relation event) i l' l :=  
  dom_rel (c_rel i l' l (tm acts sb rmw rf sc)).

Definition t_cur tm (acts : list event) (sb rmw rf sc : relation event) i l :=  
  dom_rel (c_cur i l (tm acts sb rmw rf sc)).

Definition t_acq tm (acts : list event) (sb rmw rf sc : relation event) i l :=  
  dom_rel (c_acq rf i l (tm acts sb rmw rf sc ;; rel acts sb rmw rf)).

Definition msg_rel tm (acts : list event) (sb rmw rf sc : relation event) l :=  
  m_rel l (tm acts sb rmw rf sc ;; rel acts sb rmw rf).


(*
Lemma c_cur_ur_dom1 i l : is_f (c_cur_ur i l) is_write.
Proof. unfold c_cur_ur; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_rw_dom1 i l : is_f (c_cur_rw i l) is_write.
Proof. unfold c_cur_rw; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_sc_dom1 i l : is_f (c_cur_sc i l) is_write.
Proof. unfold c_cur_sc; eauto using c_cur_doma1 with rel. Qed.
Lemma c_cur_ur_dom2 i l : is_f (c_cur_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_ur; eauto using c_cur_doma2 with rel. Qed.
Lemma c_cur_rw_dom2 i l : is_f (c_cur_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_rw; eauto using c_cur_doma2 with rel. Qed.
Lemma c_cur_sc_dom2 i l : is_f (c_cur_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_sc; eauto using c_cur_doma2 with rel. Qed.

Lemma c_acq_ur_dom1 i l : is_f (c_acq_ur i l) is_write.
Proof. unfold c_acq_ur; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_rw_dom1 i l : is_f (c_acq_rw i l) is_write.
Proof. unfold c_acq_rw; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_sc_dom1 i l : is_f (c_acq_sc i l) is_write.
Proof. unfold c_acq_sc; eauto using c_acq_doma1 with rel. Qed.
Lemma c_acq_ur_dom2 i l : is_f (c_acq_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_ur; eauto using c_acq_doma2 with rel. Qed.
Lemma c_acq_rw_dom2 i l : is_f (c_acq_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_rw; eauto using c_acq_doma2 with rel. Qed.
Lemma c_acq_sc_dom2 i l : is_f (c_acq_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_sc; eauto using c_acq_doma2 with rel. Qed.

Lemma S_tm_dom1 l : is_f (S_tm l) is_write.
Proof. unfold S_tm; eauto using S_tm_relation_doma1 with rel. Qed.
Lemma S_tm_dom2 l : is_f (S_tm l) (fun a : event => loc a = Some l).
Proof. unfold S_tm; eauto using S_tm_relation_doma2 with rel. Qed.
*)

Section Exports.

  Variable acts : list event.
  Variables sb rmw rf mo sc : relation event.
  Hypothesis COH : Coherent acts sb rmw rf mo sc.
  Variables i : thread_id.
  Variables l' l : Loc.t.
  Variables x y : event.

  Hint Resolve coh_wf c_rel_acta c_cur_acta c_acq_acta.
  Hint Resolve urr_acta rwr_acta scr_acta rel_actb.

  Lemma acts_rel_urr : t_rel urr acts sb rmw rf sc i l' l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_rel_rwr : t_rel rwr acts sb rmw rf sc i l' l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_rel_scr : t_rel scr acts sb rmw rf sc i l' l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.

  Lemma acts_cur_urr : t_cur urr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_cur_rwr : t_cur rwr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.
  Lemma acts_cur_scr : t_cur scr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto. Qed.

  Lemma acts_acq_urr : t_acq urr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto with rel. Qed.
  Lemma acts_acq_rwr : t_acq rwr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto with rel. Qed.
  Lemma acts_acq_scr : t_acq scr acts sb rmw rf sc i l x -> In x acts.
  Proof. eapply dom_in_acts; eauto with rel. Qed.

  Lemma acta_msg_urr : msg_rel urr acts sb rmw rf sc l x y -> In x acts.
  Proof. apply m_rel_acta; eauto with rel. Qed.
  Lemma acta_msg_rwr : msg_rel rwr acts sb rmw rf sc l x y -> In x acts.
  Proof. apply m_rel_acta; eauto with rel. Qed.
  Lemma acta_msg_scr : msg_rel scr acts sb rmw rf sc l x y -> In x acts.
  Proof. apply m_rel_acta; eauto with rel. Qed.

  Lemma actb_msg_urr : msg_rel urr acts sb rmw rf sc l x y -> In y acts.
  Proof. apply m_rel_actb; eauto with rel. Qed.
  Lemma actb_msg_rwr : msg_rel rwr acts sb rmw rf sc l x y -> In y acts.
  Proof. apply m_rel_actb; eauto with rel. Qed.
  Lemma actb_msg_scr : msg_rel scr acts sb rmw rf sc l x y -> In y acts.
  Proof. apply m_rel_actb; eauto with rel. Qed.

End Exports.

Hint Resolve 
     acts_rel_urr acts_rel_rwr acts_rel_scr
     acts_cur_urr acts_cur_rwr acts_cur_scr
     acts_acq_urr acts_acq_rwr acts_acq_scr
     acta_msg_urr acta_msg_rwr acta_msg_scr
     actb_msg_urr actb_msg_rwr actb_msg_scr : acts.


Require Import Setoid Permutation.

Add Parametric Morphism : (restr_eq_rel loc) with signature 
  same_relation ==> same_relation as restr_eq_rel_loc_more.
Proof.
unfold restr_eq_rel, same_relation, inclusion; split; ins; desc; split; eauto.
Qed. 

Add Parametric Morphism : (useq) with signature 
  same_relation ==> same_relation ==> same_relation as useq_more.
Proof.
  unfold useq, same_relation; ins; repeat split; desc; unnw; eauto;
  eapply clos_trans_mori; eapply seq_mori; eauto.
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

Add Parametric Morphism : (WfSB) with signature 
  eq ==> same_relation ==> iff as WfSB_more.
Proof.
  intros; unfold WfSB; unnw; rewrite H; red in H; split; intuition; eauto.
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

Add Parametric Morphism : (BasicRMW) with signature 
  same_relation ==> same_relation ==> same_relation ==> iff as BasicRMW_more.
Proof.
  intros; unfold BasicRMW; unnw; red in H,H0,H1; intuition; eapply H1; eauto.
Qed.

Add Parametric Morphism : (CoherentRW2) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentRW2_more.
Proof.
intros; unfold CoherentRW2; split; ins; eapply H3; desc; try by red in H,H0,H1,H2; desc; eauto.
- eby eapply hb_more.
- eapply hb_more with (x:=y) (x0:=x) (x1:=x0) (x2:=x1); done.
Qed.

Add Parametric Morphism : (CoherentWW) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentWW_more.
Proof.
intros; unfold CoherentWW; red in H0,H1,H2; split; ins; eapply H3; desc; eauto.
- eby eapply hb_more.
- eapply hb_more with (x:=y) (x0:=x) (x1:=x0) (x2:=x1); done.
Qed.

Add Parametric Morphism : (CoherentWR) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentWR_more.
Proof.
intros; unfold CoherentWR; red in H0,H1,H2; split; ins; eapply H3; desc; eauto.
- eby eapply hb_more.
- eapply hb_more with (x:=y) (x0:=x) (x1:=x0) (x2:=x1); done.
Qed.

Add Parametric Morphism : (CoherentRR) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentRR_more.
Proof.
intros; unfold CoherentRR; red in H0,H1,H2; split; ins; eapply H3; desc; eauto.
- eby eapply hb_more.
- eapply hb_more with (x:=y) (x0:=x) (x1:=x0) (x2:=x1); done.
Qed.

Add Parametric Morphism : (Atomicity) with signature 
  same_relation ==> same_relation ==> same_relation ==> iff as Atomicity_more.
Proof.
  intros; unfold Atomicity; red in H,H0,H1; split; ins; eapply (H2 a b); desc; eauto.
Qed.

Add Parametric Morphism : (CoherentSC) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> same_relation ==> iff as CoherentSC_more.
Proof.
  intros; unfold CoherentSC, same_relation, clos_refl in *; split; ins; desc. 
  apply (H4 a b c d e f); eauto. 
    by clear HBF FHB RF'; desf; eauto.
    by clear RF FHB RF'; desf; eauto;
    right; splits; eauto; eapply hb_more; try eassumption; try edone.
    by clear RF HBF RF'; desf; eauto;
    right; splits; eauto; eapply hb_more; try eassumption; try edone.
    by clear RF HBF FHB; desf; eauto.
  apply (H4 a b c d e f); eauto. 
    by clear HBF FHB RF'; desf; eauto.
    by clear RF FHB RF'; desf; eauto;
    right; splits; eauto; eapply hb_more; try eassumption; try edone.
    by clear RF HBF RF'; desf; eauto;
    right; splits; eauto; eapply hb_more; try eassumption; try edone.
    by clear RF HBF FHB; desf; eauto.
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
