(******************************************************************************)
(** * Definitions of Graph Steps   *)
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
Require Import Memory.
Require Import Thread.
Require Import Commit.

Require Import Gevents.
Require Import model.

Set Implicit Arguments.
Remove Hints plus_n_O.


Lemma seq_eq_contra A (dom: A -> Prop) x (GOAL: ~ dom x) :
  <| eq x |> ;; <| dom |> <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
Qed.

Lemma seq_eq_contra2 A (dom: A -> Prop) x (GOAL: ~ dom x) r :
  <| eq x |> ;; <| dom |> ;; r <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
Qed.

Lemma restr_eq_seq_eqv_l :
  forall (X : Type) (rel : relation X) (B : Type) (f : X -> B)
         (dom : X -> Prop),
    restr_eq_rel f (<| dom |>;; rel) <--> <| dom |> ;; restr_eq_rel f rel.
Proof.
  ins; rewrite !seq_eqv_l; unfold restr_eq_rel; split; red; ins; desf.
Qed.

Lemma seq_eqvC A (dom dom' : A -> Prop) :
  <| dom |>;; <| dom' |> <-->
  <| dom' |>;; <| dom |>.
Proof.
  rewrite !seq_eqv_l; unfold eqv_rel, same_relation, inclusion; intuition.
Qed.



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
red; ins; eapply clos_trans_mon; eauto.
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



(*
Hint Resolve
 act_mon sb_mon rmw_mon rf_mon mo_mon sc_mon
 useq_mon rseq_mon rel_mon sw_mon hb_mon hbsc_mon
 ur_mon rw_mon scr_mon
 c_cur_ur_mon c_cur_rw_mon c_cur_sc_mon 
 c_acq_ur_mon c_acq_rw_mon c_acq_sc_mon : gstep_mon.
*)

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

Section GstepLemmas.

  Hypothesis (COH: Coherent acts sb rmw rf mo sc).
  Variable (a : event).
  Hypothesis (GSTEP: gstep a).

  Hint Resolve 
    inclusion_refl2 clos_refl_mori clos_trans_mori clos_refl_trans_mori 
    restr_rel_mori restr_eq_rel_mori seq_mori union_mori : mon.

  Lemma act_mon : inclusion <| fun a => In a acts |> <|fun a => In a acts'|>.
  Proof. unfold eqv_rel; cdes GSTEP; cdes INC; red; ins; desf; eauto. Qed.
  Lemma sb_mon : inclusion sb sb'.
  Proof. cdes GSTEP; cdes INC; auto. Qed.
  Lemma rmw_mon : inclusion rmw rmw'.
  Proof. cdes GSTEP; cdes INC; auto. Qed.
  Lemma rf_mon : inclusion rf rf'.
  Proof. cdes GSTEP; cdes INC; auto. Qed.
  Lemma mo_mon : inclusion mo mo'.
  Proof. cdes GSTEP; cdes INC; auto. Qed.
  Lemma sc_mon : inclusion sc sc'.
  Proof. cdes GSTEP; cdes INC; auto. Qed.
  Hint Resolve act_mon sb_mon rmw_mon rf_mon mo_mon sc_mon: mon.

  Lemma useq_mon : inclusion (useq rmw rf) (useq rmw' rf').
  Proof. unfold useq; eauto with mon. Qed.
  Hint Resolve useq_mon: mon.
  Lemma rseq_mon : inclusion (rseq acts sb rmw rf) (rseq acts' sb' rmw' rf').
  Proof. unfold rseq; eauto 20 with mon. Qed.
  Hint Resolve rseq_mon: mon.
  Lemma rel_mon : inclusion (rel acts sb rmw rf) (rel acts' sb' rmw' rf').
  Proof. unfold rel; eauto 20 with mon. Qed.
  Hint Resolve rel_mon: mon.
  Lemma sw_mon : inclusion (sw acts sb rmw rf) (sw acts' sb' rmw' rf').
  Proof. unfold sw; eauto 20 with mon. Qed.
  Hint Resolve sw_mon: mon.
  Lemma hb_mon : inclusion (hb acts sb rmw rf) (hb acts' sb' rmw' rf').
  Proof. unfold hb; eauto 20 with mon. Qed.
  Hint Resolve hb_mon: mon.
  Lemma rfhbsc_mon : inclusion (rfhbsc acts sb rmw rf sc) (rfhbsc acts' sb' rmw' rf' sc').
  Proof. unfold rfhbsc; eauto 20 with mon. Qed.
  Hint Resolve rfhbsc_mon: mon.
  Lemma urr_mon : inclusion (urr acts sb rmw rf sc) (urr acts' sb' rmw' rf' sc').
  Proof. unfold urr; eauto 20 with mon. Qed.
  Hint Resolve urr_mon: mon.
  Lemma rwr_mon : inclusion (rwr acts sb rmw rf sc) (rwr acts' sb' rmw' rf' sc').
  Proof. unfold rwr; eauto 20 with mon. Qed.
  Hint Resolve rwr_mon: mon.
  Lemma scr_mon : inclusion (scr acts sb rmw rf sc) (scr acts' sb' rmw' rf' sc').
  Proof. unfold scr; eauto 20 with mon. Qed.
  Hint Resolve scr_mon: mon.
  Lemma urr_rel_mon : inclusion (urr_rel acts sb rmw rf sc) (urr_rel acts' sb' rmw' rf' sc').
  Proof. unfold urr_rel; eauto 20 with mon. Qed.
  Hint Resolve urr_rel_mon: mon.
  Lemma rwr_rel_mon : inclusion (rwr_rel acts sb rmw rf sc) (rwr_rel acts' sb' rmw' rf' sc').
  Proof. unfold rwr_rel; eauto 20 with mon. Qed.
  Hint Resolve rwr_rel_mon: mon.
  Lemma scr_rel_mon : inclusion (scr_rel acts sb rmw rf sc) (scr_rel acts' sb' rmw' rf' sc').
  Proof. unfold scr_rel; eauto 20 with mon. Qed.
  Hint Resolve scr_rel_mon: mon.
  
  Lemma max_elt_sb : max_elt sb' a.
  Proof.
    red; ins; cdes GSTEP; cdes INC.
    apply SB_STEP in REL; desf; try edone.
    cdes COH; cdes WF; cdes WF_SB; apply SB_ACTa in REL; edone.
  Qed.
  
  Lemma max_elt_rmw : max_elt rmw' a.
  Proof.
    red; ins; cdes COH; cdes GSTEP; cdes INC.
    apply RMW_STEP in REL.
    eapply FRESH, rmw_acta; edone.
  Qed.

  Lemma max_elt_rf : max_elt rf' a.
  Proof.
    red; ins; assert (X:=REL); eapply rf_actb with (acts:=acts') in X; eauto. 
    cdes GSTEP; cdes INC; subst acts'; clear ACT_STEP; ins; desf.
      by eapply irr_rf with (rf:=rf'); eauto.
    assert(N: exists z, rf z b); desc.
      by eapply COH; eauto; eapply rf_domb; eauto.
    assert(M:=N); apply INC_RF in N. 
    cdes COH0; cdes WF; cdes WF_RF; specialize (RF_FUN _ _ _ N REL); subst. 
    eapply FRESH, rf_acta with (acts:=acts); eauto.
  Qed. 

  Lemma max_elt_sc : max_elt sc' a.
  Proof.
    red; ins; cdes GSTEP; cdes INC; cdes COH0; cdes WF; cdes WF_SC.
    by eapply SC_IRR; apply SC_AT_END; eauto.
  Qed.

  Hint Resolve wmax_elt_eqv : rel.
  Hint Resolve max_elt_sb max_elt_rmw max_elt_rf max_elt_sc : rel_max.

  Lemma max_elt_useq : max_elt (useq rmw' rf') a. 
  Proof. eauto with rel_max rel. Qed. 
  Hint Resolve max_elt_useq : rel_max.
  Lemma wmax_elt_rseq : wmax_elt (rseq acts' sb' rmw' rf') a. 
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rseq : rel_max.
  Lemma wmax_elt_rel : wmax_elt (rel acts' sb' rmw' rf') a. 
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rel : rel_max.
  Lemma max_elt_sw : max_elt (sw acts' sb' rmw' rf') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve max_elt_sw : rel_max.
  Lemma max_elt_hb : max_elt (hb acts' sb' rmw' rf') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve max_elt_hb : rel_max.
  Lemma max_elt_rfhbsc : max_elt (rfhbsc acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve max_elt_rfhbsc : rel_max.

  Lemma wmax_elt_urr : wmax_elt (urr acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_urr : rel_max.
  Lemma wmax_elt_rwr : wmax_elt (rwr acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rwr : rel_max.
  Lemma wmax_elt_scr : wmax_elt (scr acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_scr : rel_max.

  Lemma wmax_elt_urr_rel : wmax_elt (urr_rel acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_urr_rel : rel_max.
  Lemma wmax_elt_rwr_rel : wmax_elt (rwr_rel acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rwr_rel : rel_max.
  Lemma wmax_elt_scr_rel : wmax_elt (scr_rel acts' sb' rmw' rf' sc') a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_scr_rel : rel_max.

(******************************************************************************)
(** * New edges only to the added event    *)
(******************************************************************************)

  Definition gstep_a (R R': relation event) :=
    forall x y (NEQ: y <> a) (H: R' x y), R x y.

  Lemma gstep_r_a r r' (H: gstep_a r r') : gstep_a (clos_refl r) (clos_refl r').
  Proof.
    unfold clos_refl; red; ins; desf; eauto.
  Qed.

  Lemma gstep_union_a R R' T T' (H2: gstep_a T T') (H3: gstep_a R R'): 
    gstep_a (R +++ T) (R' +++ T').
  Proof.
    unfold union; red; ins; desf; eauto.
  Qed.

  Lemma gstep_seq_wde_a R R' T T' 
        (H1: wmax_elt T' a) (H2: gstep_a T T') (H3: gstep_a R R'): 
    gstep_a (R;;T) (R';;T').
  Proof.
    unfold seq; red; ins; desf; eauto.
    destruct (classic (z = a)); desf; eauto.
    exploit H1; ins; eauto; subst y; eauto.
  Qed.

  Lemma gstep_tc_wde_a R R' (H1: wmax_elt R' a) (H2: gstep_a R R'): 
    gstep_a (tc R) (tc R').
  Proof.
    red; ins; rewrite clos_trans_tn1_iff in H; rename H into J;
    induction J; eauto using t_step.   
    destruct (classic (y = a)); desf; eauto using clos_trans. 
    exploit H1; ins; eauto; subst z; eauto. 
  Qed.

  Lemma gstep_eqv_rel_a :
    gstep_a <| fun x => In x acts |>
            <| fun x => In x acts' |>.
  Proof.
    cdes GSTEP; unfold eqv_rel, gstep_a; subst acts'; clear ACT_STEP;
    ins; desf; ins; desf; exfalso; eauto.
  Qed.

  Lemma gstep_id_a P : gstep_a P P.
  Proof.
    done.
  Qed.

  Lemma gstep_restr_eq_rel_loc_a R R' (H: gstep_a R R') : 
    gstep_a (restr_eq_rel loc R) (restr_eq_rel loc R').
  Proof.
    unfold restr_eq_rel, gstep_a in *.
    ins; desf; eauto.
  Qed.

  Hint Resolve 
     gstep_r_a gstep_seq_wde_a gstep_eqv_rel_a gstep_union_a
     gstep_id_a gstep_tc_wde_a gstep_restr_eq_rel_loc_a: rel_max.

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
    red; ins; cdes GSTEP; cdes INC; cdes COH; cdes WF; cdes WF_RF.
    cdes COH0; cdes WF0; cdes WF_RF0.
    rewrite ACT_STEP in *.
    assert(exists z, rf z y); desc.
      eapply RF_TOT.
      specialize (RF_ACTb0 x y H); destruct RF_ACTb0; try done.
        by exfalso; eauto.
      specialize (RF_DOMb0 x y H); done.
    assert (H1: z=x); try eapply RF_FUN0; eauto.
    rewrite H1 in *; done.
  Qed.

  Lemma gstep_sc_a : gstep_a sc sc'.
  Proof.
    red; ins; cdes GSTEP; cdes INC; unnw.
    cdes COH0; cdes WF; cdes WF_SC.
    assert (x<>a).
      intro H1. rewrite H1 in *. eby eapply max_elt_sc.
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

  Hint Resolve gstep_sb_a gstep_rmw_a gstep_rf_a gstep_sc_a : rel_max.

  Lemma gstep_useq_a : gstep_a (useq rmw rf) (useq rmw' rf').
  Proof. unfold useq; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_useq_a : rel_max.
  Lemma gstep_rseq_a : gstep_a (rseq acts sb rmw rf) (rseq acts' sb' rmw' rf').
  Proof. unfold rseq; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rseq_a : rel_max.
  Lemma gstep_rel_a : gstep_a (rel acts sb rmw rf) (rel acts' sb' rmw' rf').
  Proof. unfold rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rel_a : rel_max.
  Lemma gstep_sw_a : gstep_a (sw acts sb rmw rf) (sw acts' sb' rmw' rf').
  Proof. unfold sw; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_sw_a : rel_max.
  Lemma gstep_hb_a : gstep_a (hb acts sb rmw rf) (hb acts' sb' rmw' rf').
  Proof. unfold hb; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_hb_a : rel_max.
  Lemma gstep_rfhbsc_a : gstep_a (rfhbsc acts sb rmw rf sc) (rfhbsc acts' sb' rmw' rf' sc').
  Proof. unfold rfhbsc; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rfhbsc_a : rel_max.
  Lemma gstep_urr_a : gstep_a (urr acts sb rmw rf sc) (urr acts' sb' rmw' rf' sc').
  Proof. unfold urr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_urr_a : rel_max.
  Lemma gstep_rwr_a : gstep_a (rwr acts sb rmw rf sc) (rwr acts' sb' rmw' rf' sc').
  Proof. unfold rwr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rwr_a : rel_max.
  Lemma gstep_scr_a : gstep_a (scr acts sb rmw rf sc) (scr acts' sb' rmw' rf' sc').
  Proof. unfold scr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_scr_a : rel_max.

  Lemma gstep_urr_rel_a : 
    gstep_a (urr_rel acts sb rmw rf sc) (urr_rel acts' sb' rmw' rf' sc').
  Proof. unfold urr_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_urr_rel_a : rel_max.
  Lemma gstep_rwr_rel_a : 
    gstep_a (rwr_rel acts sb rmw rf sc) (rwr_rel acts' sb' rmw' rf' sc').
  Proof. unfold rwr_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rwr_rel_a : rel_max.
  Lemma gstep_scr_rel_a : 
    gstep_a (scr_rel acts sb rmw rf sc) (scr_rel acts' sb' rmw' rf' sc').
  Proof. unfold scr_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_scr_rel_a : rel_max.
   
  Lemma gstep_m_rel_a l tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (m_rel l tm) (m_rel l tm').
  Proof. unfold m_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_m_rel_a : rel_max.
   
  Lemma gstep_c_rel_a i l l' tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_rel i l l' tm) (c_rel i l l' tm').
  Proof. unfold c_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_rel_a : rel_max.
   
  Lemma gstep_c_cur_a i l tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_cur i l tm) (c_cur i l tm').
  Proof. unfold c_cur; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_cur_a : rel_max.
   
  Lemma gstep_c_acq_a i l tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_acq rf i l tm) (c_acq rf' i l tm').
  Proof. ins; unfold c_acq; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_acq_a : rel_max.
   
  Lemma gstep_S_tmr_a l : 
    gstep_a (S_tm_relation acts sb rmw rf l) 
            (S_tm_relation acts sb rmw rf l).
  Proof. unfold S_tm_relation; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_S_tmr_a : rel_max.
   
  Lemma gstep_dom_rel_a R R' (H: gstep_a R R') : 
    forall x (IN: dom_rel R' x), dom_rel R x \/ R' x a.
  Proof.
    unfold dom_rel; ins; desf.
    destruct (classic (y=a)); subst; eauto.
  Qed.

(*
Lemma gstep_c_cur_ur_a i l : 
forall x (IN: c_cur_ur acts' sb' rmw' rf' sc' i l x), 
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
*)

(******************************************************************************)
(** * Various lemmas about gstep   *)
(******************************************************************************)

Lemma gstep_read_rf l v o_a (READ: lab a = Aload l v o_a) : 
  (exists b, << RFb: rf' b a >> /\ << INb: In b acts >> /\ 
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

Lemma gstep_non_write_mo (N: ~ is_write a) : mo <--> mo'.
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

Lemma gstep_sc_nonsc (N: ~ is_sc a) : sc <--> sc'.
Proof.
cdes GSTEP; cdes INC; split; ins.
intros x y H.
cdes COH0; cdes WF; cdes WF_SC.
specialize (SC_DOMa _ _ H); red in SC_DOMa.
specialize (SC_DOMb _ _ H); red in SC_DOMb.
unfold is_sc in *.
eapply gstep_sc_a; try edone;
by intro A; rewrite A in *; edestruct (lab a); ins.
Qed.

Definition sc_ext x y := 
  In x acts /\ is_sc x /\ is_sc y /\ y = a.

Definition sb_ext :=
  <| fun x => In x acts |> ;; (fun x y => thread x = thread y) ;; <| eq a |>.

Lemma max_elt_sc_ext : max_elt sc_ext a.
Proof. cdes GSTEP; unfold sc_ext; red; ins; desf. Qed.
Hint Resolve max_elt_sc_ext : rel_max.
Lemma max_elt_sb_ext : max_elt sb_ext a.
Proof. cdes GSTEP; unfold sb_ext, seq, eqv_rel; red; ins; desf. Qed.
Hint Resolve max_elt_sb_ext : rel_max.

Lemma seq_sc_ext_max r (MAX: max_elt r a) : sc_ext ;; r <--> (fun _ _ => False).
Proof. unfold sc_ext; eapply seq_max; eauto; ins; desf. Qed.
Lemma seq_sb_ext_max r (MAX: max_elt r a) : sb_ext ;; r <--> (fun _ _ => False).
Proof. eapply seq_max; eauto; unfold sb_ext, seq, eqv_rel; ins; desf. Qed.

Lemma seq_sc_ext_max_r r (MAX: max_elt r a) : sc_ext ;; clos_refl r <--> sc_ext.
Proof. rewrite crE; rel_simpl; rewrite seq_sc_ext_max; rel_simpl. Qed.
Lemma seq_sb_ext_max_r r (MAX: max_elt r a) : sb_ext ;; clos_refl r <--> sb_ext.
Proof. rewrite crE; rel_simpl; rewrite seq_sb_ext_max; rel_simpl. Qed.


Lemma gstep_sc :
  sc' <--> sc +++ sc_ext.
Proof.
  cdes GSTEP; cdes INC; unfold union, sc_ext.
  split; try apply inclusion_union_l; eauto with rel; 
    red; ins; desc; try subst y; eauto.
  cdes COH0; cdes WF; cdes WF_SC.
  specialize (SC_ACTa _ _ H); subst acts'; ins; des; try subst x. 
    by apply max_elt_sc in H.
  specialize (SC_ACTb _ _ H); ins; des; try subst y; eauto 8.
  left; eapply gstep_sc_a; try edone; intro; subst y; eauto.
Qed.

Lemma inclusion_sb1 : 
  inclusion sb 
            (<| fun x => In x acts |> ;; (fun x y => thread x = thread y) ;; 
             <| fun x => In x acts |>).
Proof.
  clear a GSTEP.
  rewrite seq_eqv_r, seq_eqv_l; red; ins.
  cdes COH; cdes WF; cdes WF_SB; eauto 6.
Qed.

Lemma sb_sb_ext : inclusion (sb;; sb_ext) sb_ext.
Proof.
  rewrite inclusion_sb1, inclusion_seq_eqv_r.
  unfold sb_ext, seq, eqv_rel; red; ins; desf. 
  rewrite H1 in *; eauto 8.
Qed.


(******************************************************************************)
(** * More lemmas about gstep   *)
(******************************************************************************)

Lemma gstep_a_acts : 
  <| eq a |> ;; <| fun x => In x acts |> <--> (fun _ _ => False).
Proof.
  clear - GSTEP; unfold seq, eqv_rel; split; red; ins; desf.
  cdes GSTEP; eauto.
Qed.

Ltac relsimp := 
  repeat first 
         [rewrite seq_id_l | rewrite seq_id_r 
          | rewrite unionFr | rewrite unionrF 
          | rewrite seqFr | rewrite seqrF 
          | rewrite gstep_a_acts
          | rewrite (seq2 gstep_a_acts)
          | rewrite restr_eq_seq_eqv_l 
          | rewrite restr_eq_seq_eqv_rel 
          | rewrite restr_eq_union 
          | rewrite clos_refl_union1 
          | rewrite seq_union_l
          | rewrite seq_union_r 
          | rewrite seqA ]; try done.



Lemma gstep_in_acts :
  eqv_rel (fun x => In x acts') <--> 
  eqv_rel (fun x => In x acts) +++ eqv_rel (eq a).
Proof.
  cdes GSTEP; subst; clear.
  unfold union, eqv_rel, same_relation, inclusion; ins.
  intuition.
Qed.  

Lemma gstep_sb : sb' <--> sb +++ sb_ext.
Proof.
  unfold sb_ext; cdes GSTEP; cdes INC.
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

Lemma gstep_rmw :
  rmw' <--> rmw.
Proof.
  apply GSTEP.
Qed.

Lemma gstep_rf :
  rf' <--> rf +++ <| fun x => In x acts |> ;; rf' ;; <| eq a |>.
Proof.
  rewrite seq_eqv_r, seq_eqv_l.
  split; unfold union, singl_rel; red; ins; desf; eauto using rf_mon.
  destruct (classic (y = a)); subst.
  2: by eapply gstep_rf_a in H; vauto.
  cdes GSTEP; cdes INC; cdes COH0; cdes WF; cdes WF_RF; eauto.
  desf; exploit RF_ACTa; eauto; ins; desf; try subst a; eauto.
  edestruct (Cnp x); eapply t_step; vauto. 
Qed.

Lemma gstep_rf_rmw :
  rf' ;; rmw' <--> rf ;; rmw.
Proof.
  rewrite gstep_rmw, gstep_rf; rel_simpl.
  split; repeat apply inclusion_union_l; eauto with rel.
  unfold seq, eqv_rel; red; ins; desf. 
  exfalso; apply GSTEP.
  cdes COH; cdes WF; cdes WF_RMW; cdes WF_SB; eauto.
Qed.

Lemma gstep_useq :
  useq rmw' rf' <--> useq rmw rf.
Proof.
  by unfold useq; rewrite gstep_rf_rmw.
Qed.


Lemma gstep_rf_read b (RFb: rf' b a) :
  rf' <--> rf +++ singl_rel b a.
Proof.
  split; unfold union, singl_rel; red; ins; desf; eauto using rf_mon.
  destruct (classic (y = a)); subst.
    by cdes GSTEP; cdes INC; cdes COH0; cdes WF; cdes WF_RF; eauto.
  by eapply gstep_rf_a in H; vauto.
Qed.

Lemma gstep_rf_nonread (N: ~ is_read a) :
  rf' <--> rf.
Proof.
  split; unfold union, singl_rel; red; ins; desf; eauto using rf_mon.
  destruct (classic (y = a)); subst.
    by destruct N; eapply rf_domb in H; eauto.
  by eapply gstep_rf_a in H; vauto.
Qed.


Lemma gstep_a_write b (RFb: rf' b a) :
  eqv_rel (eq a);; eqv_rel is_write <--> (fun _ _ => False).
Proof.
  unfold seq, eqv_rel; split; red; ins; desf.
  eapply rf_to_non_read with (acts:=acts'); eauto.
  intro; unfold is_read,is_write in *; destruct (lab y); ins.
Qed.

Lemma gstep_rseq1 :
  rseq acts' sb' rmw' rf' <--> 
  rseq acts sb rmw rf +++ 
  <| fun x => In x acts' |> ;;
  <| is_write |> ;;
  restr_eq_rel loc (fun x y => thread x = thread y) ;;
  <| is_write |> ;; <| eq a |>.
Proof.
  assert (X: <| eq a |>;; <| is_write |>;; clos_refl (useq rmw rf)
           <--> <| is_write |>;; <| eq a |>).
    rewrite (seq2 (seq_eqvC _ _)), seqA; apply seq_more; ins. 
    rewrite crE; rel_simpl; split; repeat apply inclusion_union_l; eauto with rel.
    rewrite seq_eqv_l; red; ins; desc; subst x.
    by apply gstep_useq, max_elt_useq in H0.
  assert (Y: forall r, <| eq a |>;; <| is_write |>;; 
                       clos_refl (restr_eq_rel loc sb);; r
                       <--> <| eq a |>;; <| is_write |> ;; r).
    ins; rewrite !(seq2 (seq_eqvC _ _)), !seqA; apply seq_more; ins. 
    rewrite <- seqA; apply seq_more; ins.
    rewrite crE; rel_simpl; split; repeat apply inclusion_union_l; eauto with rel.
    rewrite seq_eqv_l; unfold restr_eq_rel; red; ins; desc; subst x.
    by exfalso; apply GSTEP; cdes COH; cdes WF; cdes WF_SB; eauto.
  unfold rseq; rewrite gstep_useq, gstep_sb, gstep_in_acts; unfold sb_ext;
  relsimp. 
  rewrite unionA; apply union_more; ins.
  rewrite Y, (seq2 (seq_eqvK _)), X.
  rewrite (seq2 (seq_eqvC (eq a) is_write)); relsimp. 
  rewrite (seq2 (seq_eqvC is_write (fun x => In x acts))); relsimp. 
  rewrite (seq2 (seq_eqvK _)).
  split; repeat apply inclusion_union_l; eauto with rel;
  rewrite !seq_eqv_l; unfold eqv_rel, restr_eq_rel, seq; right; ins; desf; eauto 12.
Qed.


Lemma gstep_rseq :
  rseq acts' sb' rmw' rf' <--> 
  rseq acts sb rmw rf +++ 
  <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> +++
  <| is_write |> ;; <| eq a |>.
Proof.
  unfold rseq; rewrite gstep_in_acts; relsimp.
  apply union_more; cycle 1.
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    by rewrite (seq2 (seq_eqvK _)).
  rewrite gstep_sb at 1; relsimp. 
  apply union_more.
    by rewrite gstep_useq.
  unfold sb_ext; relsimp.
  rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
  rewrite (seq_eq_max_r), (seq_eqvC (eq a) _); eauto with rel rel_max.
  rewrite (seq2 (seq_eqvC is_write _)), seqA.
  by rewrite (seq2 (seq_eqvK _)).
Qed.

Lemma gstep_eq_acts' : 
  <| eq a |>;; <| fun a0 => In a0 acts' |> <--> <| eq a |>.
Admitted.

Lemma gstep_rel :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  <| is_ra |> ;; <| is_write |> ;; <| eq a |> +++
  <| is_ra |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> +++
  <| is_ra |> ;; <| is_wfence |> ;; sb_ext ;; <| is_write |>.
Proof.
  unfold rel at 1; rewrite gstep_sb at 1; relsimp.
  assert (X: sb_ext;; rseq acts' sb' rmw' rf' <--> sb_ext;; <| is_write |>).
    unfold sb_ext, rseq; rewrite !seqA.
    rewrite (seq2 gstep_eq_acts').
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    rewrite (seq2 (seq_eqvK _)).
    by rewrite (seq_eqvC _).  
  rewrite X; clear X.
  unfold rel; relsimp.
  rewrite gstep_rseq; relsimp.
  rewrite !(seq2 (seq_eqvK _)).
  split; repeat apply inclusion_union_l; eauto 20 with rel.
    apply inclusion_union_r; right; do 2 (apply seq_mori; ins).
    by rewrite inclusion_restr_eq, inclusion_seq_eqv_l, <- seqA, sb_sb_ext. 
  red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
  apply GSTEP; eapply sb_actb in H1; eauto.
Qed.

Lemma gstep_rseq_nonwrite (N: ~ is_write a) :
  rseq acts' sb' rmw' rf' <--> rseq acts sb rmw rf.
Proof.
  unfold rseq; rewrite <- gstep_useq, gstep_in_acts, gstep_sb.
  unfold sb_ext; relsimp.
  rewrite !(seq_eq_contra2 _ _ N); relsimp.
Qed.

Lemma gstep_rel_nonwrite (N: ~ is_write a) :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf.
Proof.
  unfold rel; rewrite gstep_rseq_nonwrite, gstep_sb;
  unfold sb_ext; eauto; relsimp.
  unfold rseq at 3; relsimp.
Qed.

Lemma gstep_sw_read b (RFb: rf' b a) :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ 
  rel acts sb rmw rf ;; singl_rel b a ;; eqv_rel is_ra.
Proof.
  assert (R: is_read a) by (cdes GSTEP; eapply COH0; eauto).
  assert (N: ~ is_write a /\ ~ is_rfence a); desc.
    by unfold is_read, is_write, is_rfence in *; destruct (lab a); ins.
  unfold sw; rewrite gstep_rel_nonwrite, gstep_rf_read; try edone. 
  relsimp. 
  apply union_more; ins.
  2: by rewrite (fun x => seq2 (seq_singl_max_r _ x)); eauto with rel rel_max. 
   do 2 (apply seq_more; ins). 
  rewrite gstep_sb; unfold sb_ext; relsimp.
  rewrite seq_eq_contra2; relsimp.
Qed.

Lemma gstep_sw_rfence (F: is_rfence a) :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ 
  rel acts sb rmw rf;; rf;; <| is_rlx |>;; sb_ext ;; <| is_ra |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_rfence in *; destruct (lab a); ins.
  unfold sw; rewrite gstep_rel_nonwrite, gstep_rf_nonread; try edone. 
  relsimp; rewrite !crE; relsimp.
  rewrite unionA; apply union_more; ins.
  rewrite gstep_sb; unfold sb_ext; relsimp.
  apply union_more; ins.
  do 5 (apply seq_more; ins); unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
Qed.

Lemma union_eq_helper X (rel rel' : relation X) (IN: inclusion rel' rel) :
   rel +++ rel' <--> rel.
Proof.
  split; eauto with rel.
Qed.

Lemma union_eq_helper2 X (rel rel' : relation X) (IN: inclusion rel' (fun _ _ => False)) :
   rel +++ rel' <--> rel.
Proof.
  apply union_eq_helper; red; ins; exfalso; eauto. 
Qed.


Lemma gstep_sw_other (NR: ~ is_read a) (NF: ~ is_rfence a) :
  sw acts' sb' rmw' rf' <--> sw acts sb rmw rf.
Proof.
  unfold sw. 
  rewrite gstep_rel; relsimp.
  rewrite (fun x => seq2 (seq_eq_max x)); auto with rel rel_max; relsimp.
  rewrite union_eq_helper2; cycle 1.
    by rewrite !inclusion_seq_eqv_l, seq_sb_ext_max; auto with rel rel_max. 
  rewrite union_eq_helper2; cycle 1.
    rewrite !inclusion_seq_eqv_l; unfold sb_ext; relsimp.
    rewrite (fun x => seq2 (seq_eq_max x)); auto with rel rel_max; relsimp.
  rewrite gstep_rf_nonread, gstep_sb; ins; relsimp. 
  apply union_eq_helper2; ins.
  unfold sb_ext; rewrite !seqA, (seq_eq_contra2 _ _ NF); relsimp.
Qed.


Lemma sbsw_de: 
  <| eq a |>;; (sb +++ sw acts sb rmw rf) <--> (fun _ _ => False).
Proof.
  unfold seq, union, eqv_rel, singl_rel; split; red; ins; desf.
    by apply GSTEP; cdes COH; cdes WF; cdes WF_SB; eauto.
    by apply GSTEP; eapply sw_acta; eauto.
Qed.

Lemma hb_de: 
  <| eq a |>;; hb acts sb rmw rf <--> (fun _ _ => False).
Proof.
  unfold hb; rewrite ct_begin, <- seqA, sbsw_de; relsimp.
Qed.

Lemma gstep_hb_read b (RFb: rf' b a) :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++ 
  clos_refl (hb acts sb rmw rf) ;; 
  (sb_ext +++ rel acts sb rmw rf ;; singl_rel b a ;; eqv_rel is_ra).
Proof.
  unfold hb; rewrite gstep_sw_read, gstep_sb; unfold sb_ext; try edone.
  rewrite unionAC, unionA, unionAC, <- unionA.
  rewrite path_decomp_u_3, cr_of_t; ins.
  {
    unfold seq, union, eqv_rel, singl_rel; red; ins; desc.
    assert (z = a); [by clear H0; desf|clear H; desf]. 
      by apply GSTEP; cdes COH; cdes WF; cdes WF_SB; eauto.
    by apply GSTEP; eapply sw_acta; eauto.
  }
  {
    rewrite !seq_eqv_r, !seq_eqv_l; unfold seq, union, eqv_rel, singl_rel; red; ins; desc.
    assert (y = a); [by clear H0; desf|clear H; desf]. 
      by exfalso; apply GSTEP. 
      by exfalso; apply GSTEP; eapply rel_acta in H0; eauto.
  }
Qed.

Lemma gstep_hb_rfence (F: is_rfence a) :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++ 
  clos_refl (hb acts sb rmw rf) ;; 
  (sb_ext +++ rel acts sb rmw rf;; rf ;; <| is_rlx |>;; sb_ext ;; <| is_ra |>).
Proof.
  unfold hb; rewrite gstep_sw_rfence, gstep_sb; try edone.
  rewrite unionAC, unionA, unionAC, <- unionA.
  rewrite path_decomp_u_3, cr_of_t; ins. 
    rewrite inclusion_seq_eqv_r.
    etransitivity. 
      eapply seq_mori, inclusion_refl. 
      instantiate (1 := (fun _ _ => True) ;; <| eq a |>). 
      unfold sb_ext; apply inclusion_union_l; rewrite <- !seqA; apply seq_mori; ins. 
    rewrite seqA, sbsw_de; relsimp.
  apply transitiveI.
    rewrite inclusion_seq_eqv_r at 1.
    etransitivity. 
      eapply seq_mori, inclusion_refl. 
      instantiate (1 := (fun _ _ => True) ;; <| eq a |>). 
      unfold sb_ext; apply inclusion_union_l; rewrite <- !seqA; apply seq_mori; ins. 
  relsimp.
  assert (X: <| eq a |>;; rel acts sb rmw rf <--> (fun _ _ => False)).
    unfold rel, rseq, seq, union, eqv_rel, singl_rel; split; red; ins; desf.
    2: by apply GSTEP; cdes COH; cdes WF; cdes WF_SB; eauto.
    by apply GSTEP; eauto.
  rewrite (seq2 X); unfold sb_ext; relsimp.
Qed.

Lemma gstep_hb_other (NR: ~ is_read a) (NF: ~ is_rfence a) :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++
  clos_refl (hb acts sb rmw rf) ;; sb_ext.
Proof.
  unfold hb; rewrite gstep_sw_other; ins.
  rewrite gstep_sb; relsimp.
  rewrite unionA, unionAC, unionC.
  rewrite path_decomp_u_3, cr_of_t; ins; unfold sb_ext.
  2: by apply transitiveI; relsimp.
  rewrite !seqA, sbsw_de; relsimp.
Qed.

Lemma no_a_sc :
  <| eq a |>;; sc' <--> (fun _ _ => False).
Proof.
  rewrite seq_eqv_l; split; red; ins; desc; subst x; eauto using max_elt_sc.
Qed.

Lemma no_a_sc2 b :
  singl_rel b a ;; sc' <--> (fun _ _ => False).
Proof.
  unfold singl_rel, seq; split; red; ins; desc; subst z; eauto using max_elt_sc.
Qed.

Lemma no_ext_sthr r (X: <| eq a |>;; r <--> (fun _ _ => False)) :
  sb_ext ;; r <--> (fun _ _ => False).
Proof.
  unfold sb_ext; rewrite !seqA, X; relsimp.
Qed.

Lemma gstep_rfhbsc :
  rfhbsc acts' sb' rmw' rf' sc' <--> 
  rfhbsc acts sb rmw rf sc +++
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);; sc_ext.
Proof.
  unfold rfhbsc.
  rewrite gstep_rf at 1; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)), seq_eq_max; auto with rel rel_max; relsimp. 
  rewrite <- seq_union_r; apply seq_more; ins.
  transitivity (clos_refl (hb acts sb rmw rf;; <| is_wfence |>);; sc').
  { destruct (classic (is_read a)).
      assert (exists b, rf' b a). 
        by cdes GSTEP; apply COH0; ins; subst acts'; vauto.
      desc; rewrite gstep_hb_read; eauto; relsimp.
      rewrite seq_sb_ext_max; auto with rel rel_max.
      rewrite seq_singl_max; auto with rel rel_max; relsimp. 
    destruct (classic (is_rfence a)).
      desc; rewrite gstep_hb_rfence; eauto; relsimp.
      rewrite !seq_sb_ext_max; auto with rel rel_max; relsimp.
    rewrite gstep_hb_other; ins; relsimp. 
    rewrite !seq_sb_ext_max; auto with rel rel_max; relsimp.
  }
  rewrite gstep_sc; relsimp.
Qed.


Lemma gstep_a_simpl r r' (MON: inclusion r r') (GA: gstep_a r r') :
  r' ;; <| fun x => In x acts |> <--> r ;; <| fun x => In x acts |>.
Proof.
  split; auto with rel.
  rewrite !seq_eqv_r; split; ins; desf.
  cdes GSTEP; apply GA; eauto; congruence.
Qed.


Lemma gstep_urr_read b (RF: rf' b a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  urr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_ra |> +++
  <| eq a |>.
Proof.
  unfold urr.
  rewrite gstep_in_acts; relsimp.
  eapply union_more; cycle 1.
    rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
    by erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite union_eq_helper2; cycle 1. 
    unfold sc_ext, seq, eqv_rel; red; ins; desf.
    eapply rf_domb in RF; eauto.
    by destruct a as [??[]].
  rewrite gstep_hb_read; try edone; relsimp.
  split; repeat apply inclusion_union_l; eauto with rel.
Qed.

Lemma gstep_act_singl_read b (RF: rf' b a) : 
  <| fun x => In x acts |>;; singl_rel b a <--> singl_rel b a.
Proof.
  rewrite seq_eqv_l; unfold singl_rel; split; red; ins; desf; intuition.
  cdes GSTEP. 
  exploit rf_acta; eauto; rewrite ACT_STEP; clear ACT_STEP; ins; desf. 
  by exfalso; eapply irr_rf in RF; eauto.
Qed. 

Lemma gstep_rwr_read b (RF: rf' b a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  rwr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_ra |> +++
  singl_rel b a +++
  <| eq a |>.
Proof.
  unfold rwr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); trivial with rel rel_max.
  rewrite (seq_eq_max_r); trivial with rel rel_max.
  rewrite gstep_rf_read at 2; try edone; relsimp.
  rewrite seq_singl_max_r; trivial with rel rel_max.
  rewrite gstep_act_singl_read; try edone.
  rewrite gstep_urr_read, gstep_hb_read; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 20 with rel. 
Qed.

Lemma gstep_scr_read b (RF: rf' b a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  scr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_ra |> +++
  <| fun x => In x acts |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);;
  sc_ext ;; <| is_write |> +++
  singl_rel b a +++
  <| eq a |>.
Proof.
  unfold scr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
  rewrite (seq_eq_max_r); auto with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite (crE (hb _ _ _ _)) at 2; relsimp. 
  rewrite gstep_hb_read at 1; try edone; relsimp.
  rewrite gstep_rwr_read; try edone.
  split; repeat apply inclusion_union_l; eauto 20 with rel. 
  rewrite seq_sc_ext_max; auto with rel rel_max; relsimp.
Qed.


Lemma gstep_urr_rfence (RF: is_rfence a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  urr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; <| is_rlx |> ;; sb_ext ;; <| is_ra |> +++
  <| eq a |>.
Proof.
  unfold urr.
  rewrite gstep_in_acts; relsimp.
  eapply union_more; cycle 1.
    rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
    by erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite union_eq_helper2; cycle 1. 
    unfold sc_ext, seq, eqv_rel; red; ins; desf.
    by destruct a as [??[]].
  rewrite gstep_hb_rfence; try edone; relsimp.
  split; repeat apply inclusion_union_l; eauto with rel.
Qed.

Lemma seq_sc_ext_max_r2 r (MAX: max_elt r a) d : 
  sc_ext ;; <| d |> ;; clos_refl r <--> sc_ext ;; <| d |>.
Proof. 
  rewrite crE; rel_simpl; apply union_eq_helper2.
  rewrite seq_sc_ext_max; auto with rel. 
Qed.

Lemma gstep_urr_other (NR: ~ is_read a) (NF: ~ is_rfence a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  <| fun x => In x acts |> ;; 
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);;
  sc_ext ;; <| is_wfence |> +++
  <| eq a |>.
Proof.
  unfold urr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
  eapply union_more; cycle 1.
    by erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite seq_sc_ext_max_r2; auto with rel rel_max.
  rewrite gstep_hb_other; eauto; relsimp.
Qed.


Lemma gstep_rwr_rfence (RF: is_rfence a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  rwr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; 
  <| is_rlx |> ;; sb_ext ;; <| is_ra |> +++
  <| eq a |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_rfence in *; destruct (lab a); ins.
  unfold rwr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); trivial with rel rel_max.
  rewrite (seq_eq_max_r); trivial with rel rel_max.
  rewrite gstep_rf_nonread at 2; try edone; relsimp.
  rewrite gstep_urr_rfence, gstep_hb_rfence; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_scr_rfence (RF: is_rfence a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  scr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; 
  <| is_rlx |> ;; sb_ext ;; <| is_ra |> +++
  <| eq a |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_rfence in *; destruct (lab a); ins.
  unfold scr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
  rewrite (seq_eq_max_r); trivial with rel rel_max.
  rewrite gstep_rfhbsc; try edone; relsimp.
  assert (X: sc_ext;; <| is_write |> <--> (fun _ _ => False)).
    by unfold sc_ext, seq, eqv_rel; split; red; ins; desf.
  rewrite (seq2 X); clear X; relsimp.
  rewrite gstep_rwr_rfence, gstep_hb_rfence; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.


Lemma gstep_rwr_other (NR: ~ is_read a) (NF: ~ is_rfence a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  <| fun x => In x acts |> ;; 
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);;
  sc_ext ;; <| is_wfence |> +++
  <| eq a |>.
Proof.
  unfold rwr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
  rewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rf_nonread at 2; ins. 
  rewrite gstep_urr_other, gstep_hb_other; eauto; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_scr_other (NR: ~ is_read a) (NF: ~ is_rfence a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  <| fun x => In x acts |> ;; 
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);;
  sc_ext ;; <| is_wfence |> +++
  <| fun x : event => In x acts |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf;; <| is_wfence |>);;
  sc_ext;; <| is_write |> +++
  <| eq a |>.
Proof.
  unfold scr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
  rewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; try edone; relsimp.
  rewrite seq_sc_ext_max_r2; eauto with rel rel_max.
  rewrite gstep_rwr_other, gstep_hb_other; eauto; relsimp.
  split; repeat apply inclusion_union_l; eauto 12 with rel. 
Qed.


Lemma gstep_eqa_rel :
  <| eq a |> ;; rel acts' sb' rmw' rf' <--> 
  <| eq a |> ;; <| is_ra |> ;; <| is_write |>. 
Proof.
  rewrite gstep_rel; relsimp.
  rewrite seq_eqvC, (seq2 (seq_eqvC _ (eq a))), seqA, (seq2 (seq_eqvK _)).
  split; repeat apply inclusion_union_l; eauto with rel. 
  by cdes GSTEP; rewrite seq_eq_max; ins; red; ins; eapply rel_acta in REL; eauto.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
Qed.

Lemma gstep_singl_rel b :
  singl_rel b a ;; <| is_ra |> ;; rel acts' sb' rmw' rf' <--> 
  singl_rel b a ;; <| is_ra |> ;; <| is_write |>. 
Proof.
  assert (X: singl_rel b a <--> singl_rel b a ;; <| eq a |>).
    by rewrite seq_eqv_r; unfold singl_rel; split; red; ins; desf.
  rewrite X, !seqA, (seq2 (seq_eqvC _ _)), seqA, gstep_eqa_rel. 
  by rewrite (seq2 (seq_eqvC _ _)), seqA, (seq2 (seq_eqvK _)). 
Qed.

Lemma gstep_sb_ext_rel :
  sb_ext ;; rel acts' sb' rmw' rf' <--> 
  sb_ext ;; <| is_ra |> ;; <| is_write |>. 
Proof.
  unfold sb_ext; rewrite !seqA; auto using gstep_eqa_rel, seq_more.
Qed.


Lemma max_elt_eqv2 A (dom: A -> Prop) x : 
  ~ dom x -> max_elt <| dom |> x.
Proof.
  unfold eqv_rel; red; ins; desf.
Qed.
Hint Immediate max_elt_eqv2 : rel.

Lemma gstep_rel_write (W: is_write a) :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  rel acts sb rmw rf ;; restr_eq_rel loc sb_ext +++
  <| is_ra |> ;; <| eq a |> +++
  <| is_ra |> ;; sb_ext ;; <| is_write |>.
Proof.

  unfold rel at 1; rewrite gstep_sb at 1; relsimp.
  assert (X: sb_ext;; rseq acts' sb' rmw' rf' <--> sb_ext;; <| is_write |>).
    unfold sb_ext, rseq; rewrite !seqA.
    rewrite (seq2 gstep_eq_acts').
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite (seq2 (seq_eqvC (eq a) _)), seqA.
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    rewrite (seq2 (seq_eqvK _)).
    by rewrite (seq_eqvC _).  
  rewrite X; clear X.
  unfold rel; relsimp.
  rewrite gstep_rseq; relsimp.
  rewrite !(seq2 (seq_eqvK _)).
  split; repeat apply inclusion_union_l; eauto 20 with rel.
    apply inclusion_union_r; right; do 2 (apply seq_mori; ins).
    by rewrite inclusion_restr_eq, inclusion_seq_eqv_l, <- seqA, sb_sb_ext. 
  red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
  apply GSTEP; eapply sb_actb in H1; eauto.
Qed.


Lemma gstep_urr_rel_write (F: is_write a) :
  urr_rel acts' sb' rmw' rf' sc' <--> 
  urr_rel acts sb rmw rf sc +++
  <| is_ra |> ;; <| is_write |> ;; <| eq a |> +++
  urr_rel acts sb rmw rf sc ;; <| is_ra |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> +++
  urr_rel acts sb rmw rf sc ;; <| is_ra |> ;; <| is_wfence |> ;; sb_ext ;; <| is_write |>.
Proof.
  assert (N: ~ is_rfence a /\ ~ is_wfence a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_wfence, is_rfence in *; destruct (lab a); ins.
  unfold urr_rel.
  rewrite gstep_urr_other; ins.
  rewrite seq_sc_ext_max; auto with rel; relsimp.
  rewrite gstep_eqa_rel, gstep_sb_ext_rel.
  rewrite gstep_rel; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 


 relsimp.
  

try edone; relsimp.
  rewrite !seq_sb_ext_max, seq_eq_max; auto with rel; relsimp.
  rewrite gstep_rel_nonwrite; relsimp.


  assert (N: ~ is_write a). 
    by destruct a as [??[]].
  assert (MAX: max_elt (rel acts' sb' rmw' rf') a).
    red; ins; exploit wmax_elt_rel; eauto; intro; subst b.
    by eapply rel_domb in REL; eauto. 
  unfold urr_rel.
  rewrite gstep_urr_rfence; try edone; relsimp.
  rewrite !seq_sb_ext_max, seq_eq_max; auto with rel; relsimp.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.


Lemma gstep_urr_rel_read b (RF: rf' b a) :
  urr_rel acts' sb' rmw' rf' sc' <--> urr_rel acts sb rmw rf sc.
Proof.
  assert (N: ~ is_write a). 
    by eapply rf_domb in RF; eauto; destruct a as [??[]].
  assert (MAX: max_elt (rel acts' sb' rmw' rf') a).
    red; ins; exploit wmax_elt_rel; eauto; intro; subst b0.
    by eapply rel_domb in REL; eauto. 
  unfold urr_rel.
  rewrite gstep_urr_read; try edone; relsimp.
  rewrite seq_sb_ext_max, seq_singl_max, seq_eq_max; auto with rel; relsimp.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.

Lemma gstep_urr_rel_rfence (F: is_rfence a) :
  urr_rel acts' sb' rmw' rf' sc' <--> urr_rel acts sb rmw rf sc.
Proof.
  assert (N: ~ is_write a). 
    by destruct a as [??[]].
  assert (MAX: max_elt (rel acts' sb' rmw' rf') a).
    red; ins; exploit wmax_elt_rel; eauto; intro; subst b.
    by eapply rel_domb in REL; eauto. 
  unfold urr_rel.
  rewrite gstep_urr_rfence; try edone; relsimp.
  rewrite !seq_sb_ext_max, seq_eq_max; auto with rel; relsimp.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.

Lemma gstep_urr_rel_wfence (F: is_wfence a) :
  urr_rel acts' sb' rmw' rf' sc' <--> urr_rel acts sb rmw rf sc.
Proof.
  assert (N: ~ is_write a). 
    by destruct a as [??[]].
  assert (MAX: max_elt (rel acts' sb' rmw' rf') a).
    red; ins; exploit wmax_elt_rel; eauto; intro; subst b.
    by eapply rel_domb in REL; eauto. 
  unfold urr_rel.
  rewrite gstep_urr_rfence; try edone; relsimp.
  rewrite !seq_sb_ext_max, seq_eq_max; auto with rel; relsimp.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.



Lemma gstep_rwr_rel_read b (RF: rf' b a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  rwr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_ra |> +++
  singl_rel b a +++
  <| eq a |>.
Proof.
  unfold rwr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); trivial with rel rel_max.
  rewrite (seq_eq_max_r); trivial with rel rel_max.
  rewrite gstep_rf_read at 2; try edone; relsimp.
  rewrite seq_singl_max_r; trivial with rel rel_max.
  rewrite gstep_act_singl_read; try edone.
  rewrite gstep_urr_read, gstep_hb_read; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 20 with rel. 
Qed.



Lemma gstep_urr :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc ;;
  (<| fun x => In x acts |> ;; restr_rel is_sc (fun _ _ => True) ;; <| eq a |> +++
   ext_sthr) +++ 
  <| eq a |>.
Proof.
  assert (X: clos_refl (hb acts' sb' rmw' rf') ;; <| fun x => In x acts |> <-->
             clos_refl (hb acts sb rmw rf) ;; <| fun x => In x acts |>).
    by eapply gstep_a_simpl; eauto with mon rel rel_max.

  unfold urr.
  rewrite gstep_in_acts; relsimp.
  erewrite (seq2 (seq_eq_max_r _)). 
  erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite (seq2 (seq_eqvC _ _)), seqA, seq_eq_max_r; trivial with rel rel_max.
  apply union_more; ins.
  rewrite (seq2 X).
  apply union_more; ins.
 
hb acts' sb' rmw' rf'


  apply union_more; ins.
  rewrite hb_eq_max_r.

$eauto with rel rel_max$)).
admit.
all: eauto with rel rel_max.
  rewrite 
  
  
  rewrite !crE; relsimp.
  

  <| fun x => In x acts |> ;; 
/\ thread c = thread a \/ rel acts sb rmw rf c b /\ is_ra a)

Proof.

  unfold urr.

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


(*
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




