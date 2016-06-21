(******************************************************************************)
(** * Definitions of the axiomatic memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Vbase ExtraRelations.

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

Lemma seq_eqv_l A (dom : A -> Prop) (rel : relation A) (x y : A) 
  (H : dom x) (R: rel x y) : (eqv_rel dom ;; rel) x y.
Proof. unfold seq, eqv_rel; eauto. Qed.
Lemma seq_eqv_r A (dom : A -> Prop) (rel : relation A) (x y : A) 
  (H : dom y) (R: rel x y) : (rel ;; eqv_rel dom) x y.
Proof. unfold seq, eqv_rel; eauto. Qed.

Hint Resolve seq_eqv_l seq_eqv_r.

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
eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;;
(clos_refl (restr_eq_rel loc sb)) ;;
eqv_rel is_write ;;
(clos_refl useq).

Definition rel :=
eqv_rel is_ra ;; ((eqv_rel is_write) +++ (eqv_rel is_wfence ;; sb)) ;; rseq.

Definition sw :=
  rel ;; rf ;; (clos_refl (eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence)) ;; eqv_rel (is_ra).

Definition hb :=
  clos_trans (sb +++ sw).

(******************************************************************************)
(** ** Additional derived relations for simulation *)
(******************************************************************************)

  Definition hbsc := (clos_refl (hb ;; (eqv_rel is_wfence))) ;; sc.

  Definition ur_relation := 
    (eqv_rel (fun a => In a acts)) ;; 
    ((clos_refl (clos_refl rf ;; hbsc ;; (eqv_rel is_wfence))) ;; (clos_refl hb)).
  Definition rw_relation := 
    ur_relation +++ 
    (eqv_rel (fun a => In a acts)) ;; rf ;; (clos_refl hb).
  Definition sc_relation := 
    rw_relation +++ 
    (eqv_rel (fun a => In a acts)) ;; (clos_refl rf) ;; hbsc ;; (clos_refl hb).

  Definition m_rel l tm_relation := 
    eqv_rel (fun a => is_write a /\ loc a = Some l) ;; 
    tm_relation ;; rel.

  Definition m_rel_ur l a b:= m_rel l ur_relation a b.
  Definition m_rel_rw l a b:= m_rel l rw_relation a b.
  Definition m_rel_sc l a b:= m_rel l sc_relation a b.

  Definition c_cur i l tm_relation := 
    eqv_rel (fun a => is_write a /\ loc a = Some l) ;; 
    tm_relation ;; 
    eqv_rel (fun a => thread a = i).

  Definition c_cur_ur i l :=  dom_rel (c_cur i l ur_relation).
  Definition c_cur_rw i l :=  dom_rel (c_cur i l rw_relation).
  Definition c_cur_sc i l :=  dom_rel (c_cur i l sc_relation).

  Definition c_acq i l tm_relation :=  
    (m_rel l tm_relation) ;; rf ;; eqv_rel (fun a => is_rlx a) ;;
    eqv_rel (fun a => thread a = i).

  Definition c_acq_ur i l := dom_rel (c_acq i l ur_relation).
  Definition c_acq_rw i l := dom_rel (c_acq i l rw_relation).
  Definition c_acq_sc i l := dom_rel (c_acq i l sc_relation).

  Definition c_rel i l' l tm_relation :=  
    m_rel l tm_relation ;;
    eqv_rel (fun a => is_write a /\ loc a = Some l') ;;
    eqv_rel (fun a => thread a = i).

  Definition c_rel_ur i l' l := dom_rel (c_rel i l' l ur_relation).
  Definition c_rel_rw i l' l := dom_rel (c_rel i l' l rw_relation).
  Definition c_rel_sc i l' l := dom_rel (c_rel i l' l sc_relation).

  Definition S_tm_relation l := 
    eqv_rel (fun a => In a acts) ;; 
    eqv_rel (fun a => is_write a /\ loc a = Some l) ;; 
    clos_refl ((clos_refl rf) ;; hb ;; eqv_rel is_wfence) ;;
    eqv_rel (is_sc).

  Definition S_tm l := dom_rel (S_tm_relation l).

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_in_hb : 
  forall x y, sb x y -> hb x y.
Proof.
  vauto.
Qed.

Lemma sw_in_hb : 
  forall x y, sw x y -> hb x y.
Proof.
  vauto.
Qed.

Lemma hb_trans : 
  forall x y z, hb x y -> hb y z -> hb x z.
Proof.
  vauto.
Qed.

Hint Resolve hb_trans sb_in_hb sw_in_hb : hb. 

Lemma eqv_rel_seq_eqv_rel f1 f2 (a b: event): 
  ((eqv_rel f1) ;; (eqv_rel f2)) a b <-> (eqv_rel (f1 /1\ f2)) a b.
Proof.
unfold eqv_rel, seq; split; ins; desf; eauto.
Qed.

Lemma eqv_rel_seq_eqv_rel_id f (a b: event): 
  ((eqv_rel f) ;; (eqv_rel f)) a b <-> (eqv_rel (f /1\ f)) a b.
Proof.
unfold eqv_rel, seq; split; ins; desf; eauto.
Qed.

Hint Resolve eqv_rel_seq_eqv_rel eqv_rel_seq_eqv_rel_id : eqv_rel. 

Lemma rseq_alt a b: 
rseq a b <-> 
((eqv_rel (fun a => In a acts) ;; eqv_rel is_write) +++
(eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; useq) +++
(eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; eqv_rel is_write) +++
(eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; eqv_rel is_write ;; useq)) a b.
Proof.
unfold rseq, union, clos_refl, seq, eqv_rel; split.
- ins; desf.
all: try by (left;left;left; repeat (eexists; eauto)).
all: try by (left;left;right; repeat (eexists; eauto)).
all: try by (left;right; repeat (eexists; eauto)).
all: try by (right; repeat (eexists; eauto)).
- ins; desf.
all: try by (repeat (eexists; eauto)).
Qed.
(*
Lemma rel_alt a b : 
rel a b <->
((eqv_rel (is_ra /1\ is_write);; eqv_rel (fun a => In a acts)) +++ 
(eqv_rel (is_ra /1\ is_write);; eqv_rel (fun a => In a acts) ;; useq) +++
(eqv_rel (is_ra /1\ is_write);; eqv_rel (fun a => In a acts) ;; restr_eq_rel loc sb ;; eqv_rel is_write) +++
(eqv_rel (is_ra /1\ is_write);; eqv_rel (fun a => In a acts) ;; restr_eq_rel loc sb ;; eqv_rel is_write ;; useq) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel (fun a => In a acts) ;; eqv_rel is_write) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; useq) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; eqv_rel is_write) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel (fun a => In a acts) ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; eqv_rel is_write ;; useq)) a b.
Proof.
unfold rel, rseq, union, clos_refl, seq, eqv_rel ; split.
- ins; desf.
all: try by (left;left;left;left;left;left;left; repeat (eexists; eauto)).
all: try by (left;left;left;left;left;left;right; repeat (eexists; eauto)).
all: try by (left;left;left;left;left;right; repeat (eexists; eauto)).
all: try by (left;left;left;left;right; repeat (eexists; eauto)).
all: try by (left;left;left;right; repeat (eexists; eauto)).
all: try by (left;left;right; repeat (eexists; eauto)).
all: try by (left;right; repeat (eexists; eauto)).
all: try by (right; repeat (eexists; eauto)).
- ins; desf; try by (repeat (eexists; eauto)).
Qed.


Lemma sw_alt a b :
sw a b <->
(rel ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel (is_ra) +++
rel ;; rf ;; eqv_rel (is_ra)) a b.
Proof.
unfold sw, union, clos_refl, seq ; split.
- ins; desf.
all: try by (right; repeat (eexists; eauto)).
all: try by (left; repeat (eexists; eauto)).
- ins; desf.
all: try by (repeat (eexists; eauto)).
(eexists; eauto);  (eexists; eauto);  (eexists; eauto);  (eexists; eauto);  (eexists; eauto); split; try edone.
right; eexists; eauto.
Qed.

Lemma sw_alt1 a b :
sw a b <->
((eqv_rel is_ra;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++ 
(eqv_rel is_ra;; rf ;; eqv_rel is_ra) +++ 
(eqv_rel is_ra;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel is_ra;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_write);; restr_eq_rel loc sb ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_write);; restr_eq_rel loc sb ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_write);; restr_eq_rel loc sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_write);; restr_eq_rel loc sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; rf ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_rlx ;; sb ;; eqv_rel is_rfence ;; eqv_rel is_ra) +++
(eqv_rel (is_ra /1\ is_wfence) ;; sb ;; eqv_rel is_write ;; restr_eq_rel loc sb ;; clos_trans (rf ;; rmw) ;; rf ;; eqv_rel is_ra)) a b.
Proof.
unfold sw, rel, rseq, useq, union, clos_refl, seq ; split; ins; desf.
Admitted.

 *)
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
  << RMW_LOC: forall a b (RMW: rmw a b), exists l, (loc a = some l) /\ (loc b = Some l) >> /\
  << RMW_SB: forall a b (RMW: rmw a b), sb a b >> /\
  << RMW_SBI: forall a b (RMW: rmw a b) c (SB: sb c b)(NEQ: c <> a), sb c a >> /\
  << RMW_SBI': forall a b (RMW: rmw a b) c (SB: sb a c) (NEQ: c <> b), sb b c >>.

Definition WfRF := 
  << RF_ACTa: forall a b (RF: rf a b), In a acts >> /\
  << RF_ACTb: forall a b (RF: rf a b), In b acts >> /\
  << RF_DOMa: forall a b (RF: rf a b), is_write a >> /\
  << RF_DOMb: forall a b (RF: rf a b), is_read b >> /\
  << RF_LOC: forall a b (RF: rf a b), exists l, (loc a = some l) /\ (loc b = Some l) >> /\
  << RF_VAL: forall a b (RF: rf a b), (val a = val b) >> /\
  << RF_FUN: forall a b c (RF1: rf a c) (RF2: rf b c), a=b >> /\
  << RF_TOT: forall b (IN: In b acts) (READ: is_read b), exists a, rf a b >>.

Definition WfMO :=
  << MO_ACTa: forall a b (MO: mo a b), In a acts >> /\
  << MO_ACTb: forall a b (MO: mo a b), In b acts >> /\
  << MO_DOMa: forall a b (MO: mo a b), is_write a >> /\
  << MO_DOMb: forall a b (MO: mo a b), is_write b >> /\
  << MO_LOC: forall a b (MO: mo a b), exists l, (loc a = some l) /\ (loc b = Some l) >> /\
  << MO_IRR: irreflexive mo >> /\
  << MO_T: transitive mo >> /\
  << MO_TOT: forall l, is_total (fun a => In a acts /\ is_write a /\ (loc a = some l)) mo >>.

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
Definition doma (R : event -> event -> Prop) (Property: event -> Prop) := 
forall (WF: Wf) a b (H: R a b), Property a.

Definition domb (R : event -> event -> Prop) (Property: event -> Prop) := 
forall (WF: Wf) a b (H: R a b), Property b.

Lemma eqv_rel_doma f: doma (eqv_rel f) f.
Proof. unfold doma, eqv_rel; ins; desf. Qed.

Lemma eqv_rel_domb f: domb (eqv_rel f) f.
Proof. unfold domb, eqv_rel; ins; desf. Qed.

Lemma eqv_rel_seq_doma_doma f R f2 (A: doma R f2): doma (eqv_rel f ;; R) f2.
Proof. unfold doma, eqv_rel, seq; ins; desf; eauto. Qed.

Lemma domb_seq_eqv_rel_domb f R f2 (A: domb R f2): domb (R ;; eqv_rel f) f2.
Proof. unfold domb, eqv_rel, seq; ins; desf; eauto. Qed.

Lemma restr_eq_rel_doma T (f: _ -> T) R f2 (A: doma R f2): doma (restr_eq_rel f R) f2. 
Proof. unfold doma, restr_eq_rel; ins; desf; eauto. Qed.

Lemma restr_eq_rel_domb T (f: _ -> T) R f2 (A: domb R f2): domb (restr_eq_rel f R) f2. 
Proof. unfold domb, restr_eq_rel; ins; desf; eauto. Qed.

Lemma doma_seq_R_doma T R f2 (H: doma T f2) : doma (T;;R) f2. 
Proof. unfold doma, seq; ins; desf; eauto. Qed.

Lemma R_seq_domb_domb T R f2 (H: domb R f2) : domb (T;;R) f2. 
Proof. unfold domb, seq; ins; desf; eauto. Qed.

Lemma doma_union_doma_doma T R f2 (H_T: doma T f2) (H_R: doma R f2): doma (T +++ R) f2. 
Proof. unfold doma, union; ins; desf; eauto. Qed.

Lemma doma_union_domb_domb T R f2 (H_T: domb T f2) (H_R: domb R f2): domb (T +++ R) f2. 
Proof. unfold domb, union; ins; desf; eauto. Qed.

Lemma tc_doma_doma R f2 (H: doma R f2) : doma (tc R) f2. 
Proof.
unfold doma; ins; apply clos_trans_t1n_iff in H0.
destruct H0; eauto.
Qed.

Lemma tc_domb_domb R f2 (H: domb R f2) : domb (tc R) f2. 
Proof.
unfold domb; ins; apply clos_trans_tn1_iff in H0.
destruct H0; eauto.
Qed.

Lemma clos_refl_doma_seq_doma_doma T R f2 (H: doma T f2) (H1: doma R f2): doma ((clos_refl T);;R) f2. 
Proof. unfold doma, clos_refl, seq; ins; desf; eauto. Qed.

Lemma domb_seq_clos_refl_domb_domb T R f2 (H: domb T f2) (H1: domb R f2): domb (T ;; (clos_refl R)) f2. 
Proof. unfold domb, clos_refl, seq; ins; desf; eauto. Qed.

Lemma restr_eq_rel_doma_doma T (f: _ -> T) R f2 (A: doma R f2): doma (restr_eq_rel f R) f2. 
Proof. unfold doma, restr_eq_rel; ins; desf; eauto. Qed.

Lemma restr_eq_rel_doma_domb T (f: _ -> T) R f2 (A: domb R f2): domb (restr_eq_rel f R) f2. 
Proof. unfold domb, restr_eq_rel; ins; desf; eauto. Qed.

Hint Resolve
 eqv_rel_doma eqv_rel_domb eqv_rel_seq_doma_doma domb_seq_eqv_rel_domb 
 restr_eq_rel_doma restr_eq_rel_domb doma_seq_R_doma R_seq_domb_domb
 doma_union_doma_doma doma_union_domb_domb tc_doma_doma tc_domb_domb
 clos_refl_doma_seq_doma_doma domb_seq_clos_refl_domb_domb
 restr_eq_rel_doma_doma restr_eq_rel_doma_domb : domab.

Lemma rmw_doma : doma rmw is_read.
Proof. red; ins; red in WF; desc; red in WF_RMW; desf; eauto. Qed.
Lemma rmw_domb : domb rmw is_write.
Proof. red; ins; red in WF; desc; red in WF_RMW; desf; eauto. Qed.
Lemma rf_doma : doma rf is_write.
Proof. red; ins; red in WF; desc; red in WF_RF; desf; eauto. Qed.
Lemma rf_domb : domb rf is_read.
Proof. red; ins; red in WF; desc; red in WF_RF; desf; eauto. Qed.
Lemma mo_doma : doma mo is_write.
Proof. red; ins; red in WF; desc; red in WF_MO; desf; eauto. Qed.
Lemma mo_domb : domb mo is_write.
Proof. red; ins; red in WF; desc; red in WF_MO; desf; eauto. Qed.
Lemma sc_doma : doma sc is_sc.
Proof. red; ins; red in WF; desc; red in WF_SC; desf; eauto. Qed.
Lemma sc_domb : domb sc is_sc.
Proof. red; ins; red in WF; desc; red in WF_SC; desf; eauto. Qed.
Lemma useq_doma : doma useq is_write.
Proof. unfold useq; eauto using rf_doma with domab. Qed.
Lemma useq_domb : domb useq is_write.
Proof. unfold useq; eauto using rmw_domb with domab. Qed.
Lemma rseq_doma : doma rseq is_write.
Proof. unfold rseq; eauto with domab. Qed.
Lemma rseq_domb : domb rseq is_write.
Proof. unfold rseq; eauto using useq_domb with domab. Qed.
Lemma rel_doma : doma rel is_ra.
Proof. unfold rel; eauto with domab. Qed.
Lemma rel_domb : domb rel is_write.
Proof. unfold rel; eauto using rseq_domb with domab. Qed.
Lemma sw_doma : doma sw is_ra.
Proof. unfold sw; eauto using rel_doma with domab. Qed.
Lemma sw_domb : domb sw is_ra.
Proof. unfold sw; eauto with domab. Qed.

Lemma hbsc_domb : domb hbsc is_sc.
Proof. unfold hbsc; eauto using sc_domb with domab. Qed.

Lemma c_cur_doma i l tm_relation: doma (c_cur i l tm_relation) (fun a : event => is_write a /\ loc a = Some l).
Proof. unfold c_cur; eauto with domab. Qed.
Lemma c_cur_doma1 i l tm_relation: doma (c_cur i l tm_relation) is_write.
Proof. unfold doma; ins; exploit c_cur_doma; ins; desc; eauto. Qed.
Lemma c_cur_doma2 i l tm_relation: doma (c_cur i l tm_relation) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit c_cur_doma; ins; desc; eauto. Qed.
Lemma c_cur_domb i l tm_relation: domb (c_cur i l tm_relation) (fun a => thread a = i).
Proof. unfold c_cur; eauto with domab. Qed.

Lemma m_rel_doma l tm_relation: doma (m_rel l tm_relation) (fun a : event => is_write a /\ loc a = Some l).
Proof. unfold m_rel; eauto with domab. Qed.
Lemma m_rel_doma1 l tm_relation: doma (m_rel l tm_relation) is_write.
Proof. unfold doma; ins; exploit m_rel_doma; ins; desc; eauto. Qed.
Lemma m_rel_doma2 l tm_relation: doma (m_rel l tm_relation) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit m_rel_doma; ins; desc; eauto. Qed.
Lemma m_rel_domb l tm_relation: domb (m_rel l tm_relation) is_write.
Proof. unfold m_rel; eauto using rel_domb with domab. Qed.

Lemma c_acq_doma i l tm_relation: doma (c_acq i l tm_relation) (fun a : event => is_write a /\ loc a = Some l).
Proof. unfold c_acq; eauto using m_rel_doma with domab. Qed.
Lemma c_acq_doma1 i l tm_relation: doma (c_acq i l tm_relation) is_write.
Proof. unfold doma; ins; exploit c_acq_doma; ins; desc; eauto. Qed.
Lemma c_acq_doma2 i l tm_relation: doma (c_acq i l tm_relation) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit c_acq_doma; ins; desc; eauto. Qed.
Lemma c_acq_domb1 i l tm_relation: domb (c_acq i l tm_relation) (fun a => thread a = i).
Proof. unfold c_acq; eauto with domab. Qed.
Lemma c_acq_domb2 i l tm_relation: domb (c_acq i l tm_relation) is_read.
Proof. Admitted.
Lemma c_acq_domb3 i l tm_relation: domb (c_acq i l tm_relation) is_rlx.
Proof. unfold c_acq; eauto with domab. Qed.

Lemma S_tm_relation_doma l: doma (S_tm_relation l) (fun a : event => is_write a /\ loc a = Some l).
Proof. unfold S_tm_relation; eauto with domab. Qed.
Lemma S_tm_relation_doma1 l: doma (S_tm_relation l) is_write.
Proof. unfold doma; ins; exploit S_tm_relation_doma; ins; desc; eauto. Qed.
Lemma S_tm_relation_doma2 l: doma (S_tm_relation l) (fun a : event => loc a = Some l).
Proof. unfold doma; ins; exploit S_tm_relation_doma; ins; desc; eauto. Qed.
Lemma S_tm_relation_domb l: domb (S_tm_relation l) is_sc.
Proof. unfold S_tm_relation; eauto with domab. Qed.


Definition is_f (R : event -> Prop) f := forall (WF: Wf) a (H: R a), f a.

Lemma dom_dom_rel rel f (H: doma rel f) : is_f (dom_rel rel) f. 
Proof.
unfold is_f, doma, dom_rel in *; ins; desf; eauto.
Qed.

Hint Resolve
 dom_dom_rel : domab.

Lemma c_cur_ur_dom1 i l : is_f (c_cur_ur i l) is_write.
Proof. unfold c_cur_ur; eauto using c_cur_doma1 with domab. Qed.
Lemma c_cur_rw_dom1 i l : is_f (c_cur_rw i l) is_write.
Proof. unfold c_cur_rw; eauto using c_cur_doma1 with domab. Qed.
Lemma c_cur_sc_dom1 i l : is_f (c_cur_sc i l) is_write.
Proof. unfold c_cur_sc; eauto using c_cur_doma1 with domab. Qed.
Lemma c_cur_ur_dom2 i l : is_f (c_cur_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_ur; eauto using c_cur_doma2 with domab. Qed.
Lemma c_cur_rw_dom2 i l : is_f (c_cur_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_rw; eauto using c_cur_doma2 with domab. Qed.
Lemma c_cur_sc_dom2 i l : is_f (c_cur_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_cur_sc; eauto using c_cur_doma2 with domab. Qed.

Lemma c_acq_ur_dom1 i l : is_f (c_acq_ur i l) is_write.
Proof. unfold c_acq_ur; eauto using c_acq_doma1 with domab. Qed.
Lemma c_acq_rw_dom1 i l : is_f (c_acq_rw i l) is_write.
Proof. unfold c_acq_rw; eauto using c_acq_doma1 with domab. Qed.
Lemma c_acq_sc_dom1 i l : is_f (c_acq_sc i l) is_write.
Proof. unfold c_acq_sc; eauto using c_acq_doma1 with domab. Qed.
Lemma c_acq_ur_dom2 i l : is_f (c_acq_ur i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_ur; eauto using c_acq_doma2 with domab. Qed.
Lemma c_acq_rw_dom2 i l : is_f (c_acq_rw i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_rw; eauto using c_acq_doma2 with domab. Qed.
Lemma c_acq_sc_dom2 i l : is_f (c_acq_sc i l) (fun a : event => loc a = Some l).
Proof. unfold c_acq_sc; eauto using c_acq_doma2 with domab. Qed.

Lemma S_tm_dom1 l : is_f (S_tm l) is_write.
Proof. unfold S_tm; eauto using S_tm_relation_doma1 with domab. Qed.
Lemma S_tm_dom2 l : is_f (S_tm l) (fun a : event => loc a = Some l).
Proof. unfold S_tm; eauto using S_tm_relation_doma2 with domab. Qed.



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

Lemma rf_to_non_read (C: Wf) a b (RF: rf a b) (NON_READ: ~ is_read b) : False.
Proof.
  exploit rf_domb; eauto.
Qed.

Lemma rf_mo (C: Wf) a b c (RF: rf a b) (MO: mo c b) : False.
Proof.
  exploit rf_domb; eauto.
  exploit mo_domb; eauto; ins.
  unfold is_read, is_write in *; destruct (lab b); ins; desf.
Qed.

Lemma inv_rf_mo (C: Wf) a b c (RF: rf b a) (MO: mo a c) : False.
Proof.
  exploit rf_domb; eauto.
  exploit mo_doma; eauto; ins.
  unfold is_read, is_write in *; destruct (lab a); ins; desf.
Qed.

Lemma rel_rf a b c (C: WfRF) (RA: is_ra c) (REL: rel a b) (RF: rf b c) : sw a c.
Proof.
unfold WfRF,WfMO in *; desf.
eexists; splits; try edone.
unfold eqv_rel.
exists c; splits; try edone.
exists c; splits; try edone.
left; eauto.
Qed.

Lemma rf_rf a b c (C: Wf) (RF: rf a b) (RF1: rf b c) : False.
Proof.
  exploit rf_doma; eauto.
  generalize (rf_domb C RF); ins.
  unfold is_read, is_write in *; destruct (lab b); ins; desf.
Qed.

Lemma irr_rf a (C: Wf) (RF: rf a a) : False.
Proof.
eapply rf_rf; edone.
Qed.

Lemma reflexive_ur a (IN: In a acts): ur_relation a a.
Proof.
red; unfold seq, eqv_rel.
repeat (eexists; splits; eauto).
Qed.

Lemma reflexive_rw a (IN: In a acts): rw_relation a a.
Proof.
red; left; apply reflexive_ur; done.
Qed.

Lemma reflexive_sc a (IN: In a acts): sc_relation a a.
Proof.
red; left; apply reflexive_rw; done.
Qed.

(******************************************************************************)
(** ** Actions in graph *)
(******************************************************************************)
Definition acta (R : event -> event -> Prop) := doma R (fun a => In a acts).
Definition actb (R : event -> event -> Prop) := domb R (fun a => In a acts).

Lemma eqv_rel_acta : acta (eqv_rel (fun a => In a acts)).
Proof. unfold acta, doma, eqv_rel; ins; desf. Qed.

Lemma eqv_rel_actb : actb (eqv_rel (fun a => In a acts)).
Proof. unfold actb, domb, eqv_rel; ins; desf. Qed.

Lemma eqv_rel_seq_acta_acta f R (A: acta R): acta (eqv_rel f ;; R).
Proof. unfold acta, doma, eqv_rel, seq; ins; desf; eauto. Qed.

Lemma actb_seq_eqv_rel_actb f R (A: actb R): actb (R ;; eqv_rel f).
Proof. unfold actb, domb, eqv_rel, seq; ins; desf; eauto. Qed.

Lemma restr_eq_rel_acta T (f: _ -> T) R (A: acta R): acta (restr_eq_rel f R). 
Proof. unfold acta, doma, restr_eq_rel; ins; desf; eauto. Qed.

Lemma restr_eq_rel_actb T (f: _ -> T) R (A: actb R): actb (restr_eq_rel f R). 
Proof. unfold actb, domb, restr_eq_rel; ins; desf; eauto. Qed.

Lemma acta_seq_R_acta T R (H: acta T) : acta (T;;R).
Proof. unfold acta, doma, seq; ins; desf; eauto. Qed.

Lemma R_seq_actb_actb T R (H: actb R) : actb (T;;R).
Proof. unfold actb, domb, seq; ins; desf; eauto. Qed.

Lemma acta_union_acta_acta T R (H_T: acta T) (H_R: acta R): acta (T +++ R).
Proof. unfold acta, doma, union; ins; desf; eauto. Qed.

Lemma acta_union_actb_actb T R (H_T: actb T) (H_R: actb R): actb (T +++ R).
Proof. unfold actb, domb, union; ins; desf; eauto. Qed.

Lemma tc_acta_acta R (H: acta R) : acta (tc R).
Proof.
unfold acta, doma; ins; apply clos_trans_t1n_iff in H0.
destruct H0; eauto.
Qed.

Lemma tc_actb_actb R (H: actb R) : actb (tc R).
Proof.
unfold actb, domb; ins; apply clos_trans_tn1_iff in H0.
destruct H0; eauto.
Qed.

Lemma clos_refl_acta_seq_acta_acta T R (H: acta T) (H1: acta R): acta ((clos_refl T);;R).
Proof. unfold acta, doma, clos_refl, seq; ins; desf; eauto. Qed.

Lemma actb_seq_clos_refl_actb_actb T R (H: actb T) (H1: actb R): actb (T ;; (clos_refl R)).
Proof. unfold actb, domb, clos_refl, seq; ins; desf; eauto. Qed.

Lemma restr_eq_rel_acta_acta T (f: _ -> T) R (A: acta R): acta (restr_eq_rel f R). 
Proof. unfold acta, doma, restr_eq_rel; ins; desf; eauto. Qed.

Lemma restr_eq_rel_acta_actb T (f: _ -> T) R (A: actb R): actb (restr_eq_rel f R). 
Proof. unfold actb, domb, restr_eq_rel; ins; desf; eauto. Qed.

Hint Resolve
 eqv_rel_acta eqv_rel_actb eqv_rel_seq_acta_acta actb_seq_eqv_rel_actb 
 restr_eq_rel_acta restr_eq_rel_actb acta_seq_R_acta R_seq_actb_actb
 acta_union_acta_acta acta_union_actb_actb tc_acta_acta tc_actb_actb
 clos_refl_acta_seq_acta_acta actb_seq_clos_refl_actb_actb
 restr_eq_rel_acta_acta restr_eq_rel_acta_actb : actab. 

Lemma in_acts_acta : acta (eqv_rel (fun a => In a acts)).
Proof. unfold acta; eauto with domab. Qed.
Lemma in_acts_actb : actb (eqv_rel (fun a => In a acts)).
Proof. unfold actb; eauto with domab. Qed.
Lemma sb_acta : acta sb.
Proof. red; red; ins; red in WF; desc. red in WF_SB; desc; eauto. Qed.
Lemma sb_actb : actb sb.
Proof. red; red; ins; red in WF; desc. red in WF_SB; desc; eauto. Qed.
Lemma rmw_acta : acta rmw.
Proof. red; red; ins; red in WF; desc; red in WF_SB; red in WF_RMW; desc.
apply (SB_ACTa a b); apply (RMW_SB a b); done. Qed.
Lemma rmw_actb : actb rmw.
Proof. red; red; ins; red in WF; desc; red in WF_SB; red in WF_RMW; desc.
by apply (SB_ACTb a b); apply (RMW_SB a b). Qed.
Lemma rf_acta : acta rf.
Proof. red; red; ins; red in WF; desc. red in WF_RF; desc; eauto. Qed.
Lemma rf_actb : actb rf.
Proof. red; red; ins; red in WF; desc. red in WF_RF; desc; eauto. Qed.
Lemma mo_acta : acta mo.
Proof. red; red; ins; red in WF; desc. red in WF_MO; desc; eauto. Qed.
Lemma mo_actb : actb mo.
Proof. red; red; ins; red in WF; desc. red in WF_MO; desc; eauto. Qed.
Lemma sc_acta : acta sc.
Proof. red; red; ins; red in WF; desc. red in WF_SC; desc; eauto. Qed.
Lemma sc_actb : actb sc.
Proof. red; red; ins; red in WF; desc. red in WF_SC; desc; eauto. Qed.

Lemma useq_acta : acta useq.
Proof. unfold useq; eauto using rf_acta with actab. Qed.
Lemma useq_actb : actb useq.
Proof. unfold useq; eauto using rmw_actb with actab. Qed.
Lemma rseq_acta : acta rseq.
Proof. unfold rseq; eauto with actab. Qed.
Lemma rseq_actb : actb rseq.
Proof. Admitted.
Lemma rel_acta : acta rel.
Proof. unfold rel; eauto using sb_acta, rseq_acta with actab.
apply eqv_rel_seq_acta_acta. Admitted.
Lemma rel_actb : actb rel.
Proof. unfold rel; eauto using rseq_actb with actab. Qed.
Lemma sw_acta : acta sw.
Proof. unfold sw; eauto using rel_acta with actab. Qed.
Lemma sw_actb : actb sw.
Proof. unfold sw; eauto using sb_actb,rf_actb with actab.
Admitted.
Lemma hb_acta : acta hb.
Proof. unfold hb; eauto using sb_acta,sw_acta with actab. Qed.
Lemma hb_actb : actb hb.
Proof. unfold hb; eauto using sb_actb,sw_actb with actab. Qed.
Lemma hbsc_acta : acta hbsc.
Proof. unfold hbsc; eauto using hb_acta,sc_acta with actab. Qed.
Lemma hbsc_actb : actb hbsc.
Proof. unfold hbsc; eauto using sc_actb with actab. Qed.
Lemma ur_acta : acta ur_relation.
Proof. unfold ur_relation; eauto using hb_acta,sc_acta with actab. Qed.
Lemma ur_actb : actb ur_relation.
Proof. Admitted.
Lemma rw_acta : acta rw_relation.
Proof. unfold rw_relation; eauto using hb_acta,sc_acta,ur_acta with actab. Qed.
Lemma rw_actb : actb rw_relation.
Proof. Admitted.
Lemma scr_acta : acta sc_relation.
Proof. unfold sc_relation; eauto using hb_acta,sc_acta,rw_acta with actab. Qed.
Lemma scr_actb : actb sc_relation.
Proof. Admitted.
Lemma m_rel_ur_acta l : acta (m_rel_ur l).
Proof. unfold m_rel_ur, m_rel. eauto using ur_acta with actab. Qed.
Lemma m_rel_rw_acta l : acta (m_rel_rw l).
Proof. unfold m_rel_rw, m_rel. eauto using rw_acta with actab. Qed.
Lemma m_rel_sc_acta l : acta (m_rel_sc l).
Proof. unfold m_rel_sc, m_rel. eauto using scr_acta with actab. Qed.
Lemma m_rel_ur_actb l : actb (m_rel_ur l).
Proof. unfold m_rel_ur, m_rel. eauto using rel_actb with actab. Qed.
Lemma m_rel_rw_actb l : actb (m_rel_rw l).
Proof. unfold m_rel_rw, m_rel. eauto using rel_actb with actab. Qed.
Lemma m_rel_sc_actb l : actb (m_rel_sc l).
Proof. unfold m_rel_sc, m_rel. eauto using rel_actb with actab. Qed.
Lemma S_tm_relation_acta l : acta (S_tm_relation l).
Proof. unfold S_tm_relation. eauto using rf_acta, hb_acta with actab. Qed.


Definition in_acts (R : event -> Prop) := forall (WF: Wf) a (H: R a), In a acts.

Lemma dom_in_acts rel (H: acta rel) : in_acts (dom_rel rel). 
Proof.
unfold in_acts, acta, doma, dom_rel in *; ins; desf; eauto.
Qed.

Hint Resolve
 dom_in_acts : actab.

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

Lemma S_tm_acta l : in_acts (S_tm l).
Proof. unfold S_tm; eauto using S_tm_relation_acta with actab. Qed.

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
Lemma useq_in_sb_rf (COH: Coherent) a b (USEQ: useq a b): (clos_trans (sb +++ rf)) a b.
Proof.
red in USEQ; desf.
eapply clos_trans_of_clos_trans.
eapply clos_trans_monotonic; try exact USEQ.
red; ins.
red in H; desf.
eapply t_trans.
apply t_step; right; edone.
apply t_step; left.
red in COH; desc. 
red in WF; desc.
red in WF_RMW; desf; eauto.
Qed.

Lemma rseq_in_sb_rf (COH: Coherent) a b (RSEQ: rseq a b): (clos_refl_trans (sb +++ rf)) a b.
Proof.
red in RSEQ.
unfold seq, eqv_rel,restr_eq_rel, clos_refl in *; desc; subst.
desf; subst.
apply rt_refl.
apply clos_trans_in_rt; eapply useq_in_sb_rf; edone.
apply rt_step; left; done.
apply rt_trans with (y:=z2); apply clos_trans_in_rt.
apply t_step; left; done. 
by apply useq_in_sb_rf.
Qed.

Lemma rel_in_sb_rf (COH: Coherent) a b (REL: rel a b): (clos_refl_trans (sb +++ rf)) a b.
Proof.
red in REL.
unfold seq, eqv_rel, clos_refl in *; desc; subst.
destruct REL0; desf; subst.
eapply rseq_in_sb_rf; done.
eapply rt_trans with (y:=z0).
apply rt_step; left; done. 
by apply rseq_in_sb_rf.
Qed.

Lemma sw_in_sb_rf (COH: Coherent) a b (SW: sw a b): (clos_trans (sb +++ rf)) a b.
Proof.
red in SW.
unfold seq, eqv_rel, clos_refl in *; desc; subst.
apply rel_in_sb_rf in SW; try done.
apply clos_refl_transE in SW.
destruct SW1; desf.
all: try eby eapply t_step; right.
all: try eby eapply t_trans; try edone; apply t_step; econstructor.
all: try eby eapply t_trans; try edone; eapply t_trans; try edone; apply t_step; econstructor.
Qed.

Lemma hb_in_sb_rf (COH: Coherent) a b (HB: hb a b): (clos_trans (sb +++ rf)) a b.
Proof.
red in HB; desf.
eapply clos_trans_of_clos_trans.
eapply clos_trans_monotonic.
Focus 2. edone.
eapply inclusion_union_l; unfold inclusion; ins; eauto using sw_in_sb_rf.
eapply t_step; left; done.
Qed.

Lemma hb_in_sb_rf_sc (COH: Coherent) a b (HB: hb a b): (clos_trans (sb +++ rf +++ sc)) a b.
Proof.
assert (COH' := COH).
red in COH; desf.
eapply clos_trans_monotonic with (r := (sb +++ rf)).
apply inclusion_union_r with (r := (sb +++ rf)); left; unfold inclusion; desf.
eapply hb_in_sb_rf; eauto.
Qed.

Lemma irr_hb (COH: Coherent) a (HB: hb a a): False.
Proof.
assert (COH' := COH).
red in COH; desf.
apply (Cnp a).
eapply clos_trans_monotonic.
apply inclusion_union_r with (r := (sb +++ rf)); left; unfold inclusion; desf.
eapply hb_in_sb_rf; eauto.
Qed.

Lemma hb_mo (COH: Coherent) a b (HB : hb a b) l
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

Lemma hb_in_sc (COH: Coherent) a b (HB: hb a b) 
  (IS_SCa: is_sc a)
  (IS_SCb: is_sc b) : sc a b.
Proof.
  cdes COH. cdes WF. unfold WfSC in *; desc.
  destruct (classic (a=b)) as [|N]; desf.
    by eapply irr_hb in HB.
  eapply SC_TOT in N; splits; desf; eauto using hb_acta, hb_actb.
  edestruct Cnp; eapply t_trans; eauto using hb_in_sb_rf_sc; vauto. 
Qed.

Lemma sc_hb (COH: Coherent) a b c (SC: sc a b) (HB: hb b c) (IS_SC: is_sc c) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma hb_sc (COH: Coherent) a b c (SC: sc b c) (HB: hb a b) (IS_SC: is_sc a) : sc a c.
Proof.
  cdes COH; cdes WF; unfold WfSC in *; desc.
  apply hb_in_sc in HB; eauto.
Qed.

Lemma mo_sc (COH: Coherent) a b (MO: mo a b) (IS_SCa: is_sc a) (IS_SCb: is_sc b) : sc a b.
Proof.
assert (COH' := COH).
red in COH; desf.
red in WF; desf. 
red in WF_SC, WF_MO; desf. 
destruct (classic (a=b)) as [|N].
by desf; exfalso; eauto.
apply SC_TOT in N; desf; eauto.
exfalso; eapply Csc; eauto.
Qed.

Lemma rf_rmw_mo (COH: Coherent) a b (A: (rf ;; rmw) a b) : mo a b.
Proof.
cdes COH.
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

Lemma useq_mo (COH: Coherent) a b (USEQ: (tc (rf ;; rmw)) a b) : mo a b.
Proof.
cdes COH.
red in WF; desf. 
red in WF_MO; desf. 
apply clos_trans_tn1_iff in USEQ.
induction USEQ; eauto using rf_rmw_mo.
Qed.

Lemma rseq_mo (COH: Coherent) a b (RSEQ: rseq a b) (NEQ: ~a=b) : mo a b.
Proof.
cdes COH; cdes WF; desf; red in  WF_MO; desf; cdes RSEQ.
unfold rseq, seq, eqv_rel, restr_eq_rel, clos_refl in RSEQ0; desc.
subst.
assert (WRITEa' := RSEQ6).
  apply write_has_location in RSEQ6; desc.
assert (LOCb: loc z0 = loc b).
  eapply loceq_rseq; eauto.
subst; desf.
- exfalso; auto.
- eapply useq_mo; eauto.
- eapply hb_mo; eauto with hb.
  by rewrite <- RSEQ0.
- eapply MO_T with (y:=z2). eapply hb_mo; eauto with hb.
  by rewrite <- RSEQ0.
  eby eapply useq_mo.
Qed.

Lemma rel_mo (COH: Coherent) a b (WRITE: is_write a) 
  (REL: rel a b) (NEQ: ~a=b) : mo a b.
Proof.
red in REL; unfold seq,eqv_rel, union in *; desf.
eapply rseq_mo; eauto.
exfalso; unfold is_write, is_wfence in *; destruct (lab z1); ins.
Qed.

Lemma rel_hb_mo (COH: Coherent) a b (REL: rel a b) : 
  exists c, (c=a \/ hb a c) /\ (c=b \/ mo c b).
Proof.
cdes REL.
red in REL0; desc.
red in REL1; desc.
unfold eqv_rel in *; desc; subst.
exists z0.
split.
destruct REL1; desc; auto.
destruct H; desc; subst; auto with hb.
destruct (classic (z0=b)) as [|N]; subst; auto.
right; apply rseq_mo; edone.
Qed.

Lemma basic_coherence_lemma (COH: Coherent) a b (MO: mo a b) c 
  (RF: (clos_refl rf) b c) d (HB: (clos_refl hb) c d) (INV_RF: (clos_refl rf) a d)
  (RLX: a=d \/ c=d \/ b=c \/ is_rlx d) : False.
Proof.
cdes COH; cdes WF; cdes WF_MO; cdes WF_RF.
unfold seq, clos_refl in *.
desf; eauto 2;
try solve [eapply rf_mo; eauto| eapply inv_rf_mo; eauto|eapply irr_hb; eauto |
 eapply MO_IRR; erewrite RF_FUN; edone].
Qed.

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

Lemma rf_in_rw a b (WF: Wf) (RF: rf a b): rw_relation a b.
Proof. right; repeat (eexists; splits; eauto); eapply rf_acta; eauto. Qed.

Lemma ur_in_rw a b (H: ur_relation a b): rw_relation a b.
Proof. left; done. Qed.

Lemma rw_in_sc a b (H: rw_relation a b): sc_relation a b.
Proof. left; done. Qed.

Lemma ur_in_sc a b (H: ur_relation a b): sc_relation a b.
Proof.
eauto using rw_in_sc, ur_in_rw.
Qed.

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

Lemma Coherent_ur (COH: Coherent) a b c 
  (MO: mo a b) (UR: ur_relation b c) (RF_INV: a=c \/ rf a c) : False.
Proof.
cdes COH.
red in WF; desc. 
unfold ur_relation,hbsc, seq, clos_refl in *; desc.
cdes WF_MO; unfold WfSC in *; desc.
unfold eqv_rel in *.
destruct UR0; desc; subst.
  by eapply basic_coherence_lemma; eauto.
desf; eapply Csc; eauto.
Qed.

Lemma Coherent_rw (COH: Coherent) a b c 
  (MO: mo a b) (RW: rw_relation b c) (RF_INV: a=c \/ (rf a c /\ is_rlx c)) : False.
Proof.
destruct RW.
eapply Coherent_ur; eauto. tauto.
unfold hbsc, seq, clos_refl in *.
cdes COH; cdes WF; cdes WF_MO; unfold WfSC in *; desc.
unfold eqv_rel in *.
desf; try (by desf; eapply basic_coherence_lemma; eauto).
Qed.

Lemma Coherent_sc (COH: Coherent) a b c  (SCc: is_sc c) 
  (MO: mo a b) (SC: sc_relation b c) (RF_INV: a=c \/ rf a c) : False.
Proof.
destruct SC.
eapply Coherent_rw; eauto.
desf; eauto with acts.
unfold hbsc, seq, clos_refl in *.
cdes COH; cdes WF; cdes WF_MO; unfold WfSC in *; desc.
unfold eqv_rel in *.
assert (sc z2 c). 
    destruct H2. by subst. eby eapply sc_hb.
desf; eapply Csc; try edone; eauto using hb_trans.
Qed.

Lemma ur_hb a b c (A: ur_relation a b) (HB: hb b c) : ur_relation a c. 
Proof.
red in A; unfold seq, eqv_rel in *; desf. 
red. eexists.
split. try done.
exists z0; split; eauto.
unfold clos_refl in *; desf; eauto using hb_trans.
Qed.

Lemma rw_hb a b c (A: rw_relation a b) (HB: hb b c) : rw_relation a c. 
Proof.
destruct A as [A|A]; eauto using ur_in_rw, ur_hb.
red in A; unfold seq, eqv_rel in *; desf. 
right. eexists.
split. try done.
exists z0; split; eauto.
unfold clos_refl in *; desf; eauto using hb_trans.
Qed.

Lemma scr_hb a b c (A: sc_relation a b) (HB: hb b c) : sc_relation a c. 
Proof.
destruct A as [A|A]; eauto using rw_in_sc, rw_hb.
red in A; unfold seq, eqv_rel in *; desf. 
right. eexists.
split. try done.
exists z0; split; eauto.
exists z1; split; eauto.
unfold clos_refl in *; desf; eauto using hb_trans.
Qed.

Lemma Coherent_ur_sb (COH: Coherent) a b c d
  (MO: mo a b) (UR: ur_relation b c) (SB: sb c d) (RF_INV: a=d \/ rf a d) : False.
Proof.
  eapply Coherent_ur with (c:=d); try eauto.
  eapply ur_hb; try edone.
  eapply sb_in_hb; eauto.
Qed.

Lemma Coherent_rw_sb (COH: Coherent) a b c d
  (MO: mo a b) (RW: rw_relation b c) (SB: sb c d) (RF_INV: a=d \/ (rf a d /\ is_rlx d)) : False.
Proof.
  eapply Coherent_rw with (c:=d); try eauto.
  eapply rw_hb; try edone.
  eapply sb_in_hb; eauto.
Qed.

Lemma Coherent_sc_sb (COH: Coherent) a b c d
  (SCc: is_sc d) (MO: mo a b) (SC: sc_relation b c) (SB: sb c d) (RF_INV: a=d \/ rf a d) : False.
Proof.
  eapply Coherent_sc with (c:=d); try eauto.
  eapply scr_hb; try edone.
  eapply sb_in_hb; eauto.
Qed.

Lemma Coherent_m_rel_rw (COH: Coherent) a b x (LOC: loc b = Some x) 
  (RW: m_rel_rw x a b) (MO: mo b a) : False.
Proof.
cdes COH. cdes WF. unfold WfMO in *; desc.
unfold m_rel_rw, m_rel_rw, m_rel, seq, eqv_rel in *; desc; subst.
assert (X: exists d, (d = z0 \/ hb z0 d) /\ (d = b \/ mo d b)).
  apply rel_hb_mo; eauto.
clear - COH X MO RW0 RW2 RW3 MO_T LOC.
desf; eauto using Coherent_rw, rw_hb.
Qed.

End Consistency.

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
  unfold rseq. ins.
rewrite H, H0, H1.
reflexivity.
Qed. 
 
Add Parametric Morphism : (rel) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as rel_more.
Proof.
  unfold rel. ins.
  rewrite H, H0, H1.
  reflexivity.
Qed. 

Add Parametric Morphism : (sw) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as sw_more.
Proof.
  unfold sw. ins.
  rewrite H, H0, H1.
  reflexivity.
Qed. 

Add Parametric Morphism : (hb) with signature 
  eq ==> same_relation ==> same_relation ==> same_relation ==> same_relation as hb_more.
Proof.
  unfold hb. ins.
  rewrite H, H0, H1.
  reflexivity.
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
  intros; unfold CoherentSC; cdes H; cdes H0; cdes H1; cdes H2; cdes H3.
  split; ins; eapply (H14 a b c d e f);
  desc; eauto; try (by  eapply clos_refl_mori; edone);
  desf; eauto; right; splits; try done.
  all: try by eapply hb_more; eauto using Permutation_in, Permutation_sym.
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

 