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
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Thread.
Require Import Commit.

Require Import Gevents.
Require Import model.

Set Implicit Arguments.
Remove Hints plus_n_O.

Lemma and_or_l P Q R : P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof. tauto. Qed.

Lemma or_more P Q P' Q' : (P <-> Q) -> (P' <-> Q') -> (P \/ P' <-> Q \/ Q').
Proof. tauto. Qed.


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


Lemma max_elt_eqv2 A (dom: A -> Prop) x : 
  ~ dom x -> max_elt <| dom |> x.
Proof.
  unfold eqv_rel; red; ins; desf.
Qed.
Hint Immediate max_elt_eqv2 : rel.

Lemma eqv_join A (d d' : A -> Prop) : 
  <| d |> ;; <| d' |> <--> <| d /1\ d' |>. 
Proof.
  rewrite seq_eqv_l; unfold eqv_rel; split; red; ins; desf.
Qed.

Lemma eqv_joinA A (d d' : A -> Prop) r : 
  <| d |> ;; <| d' |> ;; r <--> <| d /1\ d' |> ;; r. 
Proof.
  by rewrite <- seqA, eqv_join. 
Qed.

Lemma seq_eqvC A (dom dom' : A -> Prop) :
  <| dom |>;; <| dom' |> <-->
  <| dom' |>;; <| dom |>.
Proof.
  rewrite !eqv_join; unfold eqv_rel, same_relation, inclusion; intuition.
Qed.

Lemma seq_eqvAC A (dom dom' : A -> Prop) r :
  <| dom |> ;; <| dom' |> ;; r <-->
  <| dom' |> ;; <| dom |> ;; r.
Proof.
  rewrite !eqv_joinA, !seq_eqv_l; unfold same_relation, inclusion; intuition.
Qed.

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
(** ** Graph inclusion   *)
(******************************************************************************)

Definition graph_inclusion : Prop :=
      << INC_ACT: forall x (IN: In x acts), In x acts' >> /\
      << INC_SB: inclusion sb sb' >> /\
      << INC_RMW: inclusion rmw rmw' >> /\
      << INC_RF: inclusion rf rf' >> /\
      << INC_MO: inclusion mo mo' >> /\
      << INC_SC: inclusion sc sc' >>.

(******************************************************************************)
(** ** Graph step   *)
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
(** ** Basic Lemmas    *)
(******************************************************************************)

Section GstepLemmas.

  Hypothesis (COH: Coherent acts sb rmw rf mo sc).
  Variable (a : event).
  Hypothesis (GSTEP: gstep a).

  Lemma gstep_coh : Coherent acts'  sb' rmw' rf' mo' sc'.
  Proof. cdes GSTEP; done. Qed.

  Lemma gstep_inc : graph_inclusion.
  Proof. cdes GSTEP; done. Qed.

  Hint Resolve gstep_coh gstep_inc coh_wf.

(******************************************************************************)
(** ** Lemmas about graph inclusion   *)
(******************************************************************************)

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
  Lemma S_tmr_mon l : inclusion (S_tmr acts sb rmw rf l) (S_tmr acts' sb' rmw' rf' l).
  Proof. unfold S_tmr; eauto 20 with mon. Qed.
  Hint Resolve S_tmr_mon: mon.


(******************************************************************************)
(** ** Added node is a dead end   *)
(******************************************************************************)
  
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

  Lemma max_elt_rel_nonwrite (N: ~ is_write a) : max_elt (rel acts' sb' rmw' rf') a. 
  Proof. eauto 14 with rel_max rel. Qed.

(******************************************************************************)
(** ** New edges only to the added event    *)
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
    wmax_elt tm' a -> gstep_a tm tm' ->
    gstep_a (m_rel acts sb rmw rf l tm) (m_rel acts' sb' rmw' rf' l tm').
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
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_acq acts sb rmw rf i l tm) (c_acq acts' sb' rmw' rf' i l tm').
  Proof. ins; unfold c_acq; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_acq_a : rel_max.
   
  Lemma gstep_S_tmr_a l : 
    gstep_a (S_tmr acts sb rmw rf l) 
            (S_tmr acts sb rmw rf l).
  Proof. unfold S_tmr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_S_tmr_a : rel_max.

  Lemma gstep_seq_max r r' (MON: inclusion r r') (GA: gstep_a r r') r''
      (R : max_elt r'' a) :
    r' ;; r'' <--> r ;; r''.
  Proof.
    split; auto with rel.
    unfold seq; red; ins; desf; eexists; split; eauto.
    apply GA; ins; intro; clarify; eauto.
  Qed.

   
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
exploit (RF_TOT a). by left; eauto. eauto with acts.
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
  <| fun x => In x acts' |> <--> <| fun x => In x acts |> +++ <| eq a |>.
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

Lemma gstep_rseq :
  rseq acts' sb' rmw' rf' <--> 
  rseq acts sb rmw rf +++ 
  <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> +++
  <| is_write |> ;; <| eq a |>.
Proof.
  unfold rseq; rewrite gstep_in_acts; relsimp.
  apply union_more; cycle 1.
    rewrite (seq_eqvAC (eq a)).
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite (seq_eqvAC (eq a)).
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    by rewrite (seq2 (seq_eqvK _)).
  rewrite gstep_sb at 1; relsimp. 
  apply union_more.
    by rewrite gstep_useq.
  unfold sb_ext; relsimp.
  rewrite (seq_eqvAC (eq a)).
  rewrite (seq_eq_max_r), (seq_eqvC (eq a)); eauto with rel rel_max.
  by rewrite (seq_eqvAC is_write), (seq2 (seq_eqvK _)).
Qed.

Lemma gstep_eq_acts' : 
  <| eq a |>;; <| fun a0 => In a0 acts' |> <--> <| eq a |>.
Proof.
  rewrite gstep_in_acts; relsimp; apply seq_eqvK.
Qed.

Lemma gstep_rel :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  <| is_rel |> ;; <| is_write |> ;; <| eq a |> +++
  <| is_rel |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> +++
  <| is_rel |> ;; <| is_fence |> ;; sb_ext ;; <| is_write |>.
Proof.
  unfold rel at 1; rewrite gstep_sb at 1; relsimp.
  assert (X: sb_ext;; rseq acts' sb' rmw' rf' <--> sb_ext;; <| is_write |>).
    unfold sb_ext, rseq; rewrite !seqA.
    rewrite (seq2 gstep_eq_acts').
    rewrite (seq_eqvAC (eq a)).
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite (seq_eqvAC (eq a)).
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
  rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>.
Proof.
  assert (R: is_read a) by (cdes GSTEP; eapply COH0; eauto).
  assert (N: ~ is_write a /\ ~ is_fence a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold sw; rewrite gstep_rel_nonwrite, gstep_rf_read; try edone. 
  relsimp. 
  apply union_more; ins.
  2: by rewrite (fun x => seq2 (seq_singl_max_r _ x)); eauto with rel rel_max. 
   do 2 (apply seq_more; ins). 
  rewrite gstep_sb; unfold sb_ext; relsimp.
  rewrite seq_eq_contra2; relsimp.
Qed.

Lemma gstep_sw_fence (F: is_fence a) :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ 
  rel acts sb rmw rf;; rf;; <| is_rlx_rw |>;; sb_ext ;; <| is_acq |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold sw; rewrite gstep_rel_nonwrite, gstep_rf_nonread; try edone. 
  relsimp; rewrite !crE; relsimp.
  rewrite unionA; apply union_more; ins.
  rewrite gstep_sb; unfold sb_ext; relsimp.
  apply union_more; ins.
  do 5 (apply seq_more; ins); unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
Qed.

Lemma gstep_sw_write (W: is_write a) :
  sw acts' sb' rmw' rf' <--> sw acts sb rmw rf.
Proof.
  assert (~ is_fence a) by (destruct a as [??[]]; done).
  unfold sw. 
  rewrite gstep_rel; relsimp.
  rewrite (fun x => seq2 (seq_eq_max x)); auto with rel rel_max; relsimp.
  rewrite union_eq_helper2; cycle 1.
    by rewrite !inclusion_seq_eqv_l, seq_sb_ext_max; auto with rel rel_max. 
  rewrite union_eq_helper2; cycle 1.
    rewrite !inclusion_seq_eqv_l; unfold sb_ext; relsimp.
    rewrite (fun x => seq2 (seq_eq_max x)); auto with rel rel_max; relsimp.
  rewrite gstep_rf_nonread, gstep_sb; ins; relsimp; auto 2 with acts.
  apply union_eq_helper2; ins.
  rewrite seq_sb_ext_max; relsimp; eauto with rel.
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
  (sb_ext +++ rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>).
Proof.
  unfold hb; rewrite gstep_sw_read, gstep_sb; try edone.
  rewrite unionAC, unionA, unionAC, <- unionA.
  rewrite path_decomp_u_3, cr_of_t; ins; unfold sb_ext.
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

Lemma gstep_hb_fence (F: is_fence a) :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++ 
  clos_refl (hb acts sb rmw rf) ;; 
  (sb_ext +++ rel acts sb rmw rf;; rf ;; <| is_rlx_rw |>;; sb_ext ;; <| is_acq |>).
Proof.
  unfold hb; rewrite gstep_sw_fence, gstep_sb; try edone.
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

Lemma gstep_hb_write (W: is_write a) :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++
  clos_refl (hb acts sb rmw rf) ;; sb_ext.
Proof.
  unfold hb; rewrite gstep_sw_write; ins.
  rewrite gstep_sb; relsimp.
  rewrite unionA, unionAC, unionC.
  rewrite path_decomp_u_3, cr_of_t; ins; unfold sb_ext.
  2: by apply transitiveI; relsimp.
  rewrite !seqA, sbsw_de; relsimp.
Qed.

Lemma gstep_rfhbsc :
  rfhbsc acts' sb' rmw' rf' sc' <--> 
  rfhbsc acts sb rmw rf sc +++
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);; sc_ext.
Proof.
  unfold rfhbsc.
  rewrite gstep_rf at 1; relsimp.
  rewrite seq_eq_max; relsimp; auto with rel rel_max; relsimp. 
  rewrite !(crE (_ ;; _)); relsimp.
  rewrite (gstep_seq_max hb_mon); relsimp; auto with rel rel_max; relsimp. 
  rewrite gstep_sc; relsimp.
  split; repeat apply inclusion_union_l; eauto with rel.
Qed.


Lemma gstep_urr_read b (RF: rf' b a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  urr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_acq |> +++
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
  rwr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_acq |> +++
  singl_rel b a +++
  <| eq a |>.
Proof.
  unfold rwr.
  rewrite seq2; trivial with rel rel_max.
  rewrite gstep_rf_read at 2; try edone; relsimp.
  rewrite seq_singl_max_r; trivial with rel rel_max.
  rewrite gstep_urr_read, gstep_hb_read; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 20 with rel. 
Qed.

Lemma gstep_scr_read b (RF: rf' b a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  scr acts sb rmw rf sc ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_acq |> +++
  singl_rel b a +++
  <| eq a |>.
Proof.
  assert (N: ~ is_write a); desc.
    by eapply rf_domb in RF; eauto; destruct a as [??[]].
  unfold scr.
  rewrite seq2; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite seq_sc_ext_max; auto with rel rel_max; relsimp.
  rewrite gstep_hb_read at 1; try edone; relsimp.
  rewrite gstep_rwr_read; try edone.
  split; repeat apply inclusion_union_l; eauto 20 with rel. 
Qed.


Lemma gstep_urr_fence (RF: is_fence a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  urr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; <| is_rlx_rw |> ;; sb_ext ;; <| is_acq |> +++
  <| fun x => In x acts |> ;; 
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);;
  sc_ext +++
  <| eq a |>.
Proof.
  assert (X : sc_ext;; <| is_fence |> <--> sc_ext).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  unfold urr.
  rewrite gstep_in_acts; relsimp.
  eapply union_more; cycle 1.
    rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
    by erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite (seq2 X), seq_sc_ext_max_r; auto with rel_max.
  rewrite gstep_hb_fence; relsimp.
  split; repeat apply inclusion_union_l; eauto with rel.
Qed.

Lemma seq_sc_ext_max_r2 r (MAX: max_elt r a) d : 
  sc_ext ;; <| d |> ;; clos_refl r <--> sc_ext ;; <| d |>.
Proof. 
  rewrite crE; rel_simpl; apply union_eq_helper2.
  rewrite seq_sc_ext_max; auto with rel. 
Qed.

Lemma gstep_rwr_fence (RF: is_fence a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  rwr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; 
  <| is_rlx_rw |> ;; sb_ext ;; <| is_acq |> +++
  <| fun x => In x acts |> ;; 
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);;
  sc_ext +++
  <| eq a |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold rwr.
  rewrite seq2; trivial with rel rel_max.
  rewrite gstep_rf_nonread at 2; try edone; relsimp.
  rewrite gstep_urr_fence, gstep_hb_fence; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_scr_fence (RF: is_fence a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  scr acts sb rmw rf sc ;; rel acts sb rmw rf ;; rf;; 
  <| is_rlx_rw |> ;; sb_ext ;; <| is_acq |> +++
  <| fun x => In x acts |> ;; 
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);;
  sc_ext +++
  <| eq a |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold scr.
  rewrite seq2; trivial with rel rel_max.
  rewrite gstep_rfhbsc; try edone; relsimp.
  rewrite seq_sc_ext_max; auto with rel rel_max; relsimp.
  rewrite gstep_rwr_fence, gstep_hb_fence; try edone.
  relsimp.
  split;
    repeat (match goal with |- inclusion (_ +++ _) _ => apply inclusion_union_l end);
    eauto 10 with rel. 
Qed.

Lemma gstep_urr_write (W: is_write a) :
  urr acts' sb' rmw' rf' sc' <-->
  urr acts sb rmw rf sc +++
  urr acts sb rmw rf sc ;; sb_ext +++
  <| eq a |>.
Proof.
  assert (~ is_fence a) by (destruct a as [??[]]; done).
  unfold urr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)); eauto with rel rel_max.
  eapply union_more; cycle 1.
    by erewrite seq_eq_max_r; trivial with rel rel_max.
  rewrite gstep_rfhbsc; relsimp.
  rewrite seq_sc_ext_max; auto with rel rel_max; relsimp.
  rewrite gstep_hb_write; eauto; relsimp.
Qed.

Lemma gstep_rwr_write (W: is_write a) :
  rwr acts' sb' rmw' rf' sc' <-->
  rwr acts sb rmw rf sc +++
  rwr acts sb rmw rf sc ;; sb_ext +++
  <| eq a |>.
Proof.
  unfold rwr.
  rewrite gstep_rf_nonread at 2; ins; auto with acts. 
  rewrite gstep_urr_write, gstep_hb_write; eauto; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_scr_write (W: is_write a) :
  scr acts' sb' rmw' rf' sc' <-->
  scr acts sb rmw rf sc +++
  scr acts sb rmw rf sc ;; sb_ext +++
  <| fun x => In x acts |> ;; 
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);; sc_ext +++
  <| eq a |>.
Proof.
  assert (X : sc_ext;; <| is_write |> <--> sc_ext).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  assert (Y: <| fun x : event => In x acts |>;;
      clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);; sc_ext <-->
      clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);; sc_ext).
    rewrite seq_eqv_l; split; red; ins; splits; desf.
    eapply seq_r_doma with (d:=fun x => In x acts) in H; eauto.
    2: by unfold sc_ext; red; ins; desf.
    by apply seq_r_doma; eauto using rf_acta, seq_doma, hb_acta.
  rewrite Y.
  unfold scr.
  rewrite gstep_rfhbsc; try edone; relsimp.
  rewrite (seq2 X), seq_sc_ext_max_r; eauto with rel rel_max.
  rewrite gstep_rwr_write, gstep_hb_write; eauto; relsimp.
  split;
    repeat (match goal with |- inclusion (_ +++ _) _ => apply inclusion_union_l end);
    eauto 10 with rel. 
Qed.


Lemma gstep_rel_write (W: is_write a) :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  <| is_rel |> ;; <| eq a |> +++
  <| is_rel |> ;; <| is_write |>;; restr_eq_rel loc sb_ext +++
  <| is_rel |> ;; <| is_fence |> ;; sb_ext.
Proof.
  rewrite gstep_rel.
  assert (X : <| is_write |>;; <| eq a |> <--> <| eq a |>); [|rewrite X].
    by rewrite seq_eqv_l; unfold eqv_rel; split; red; ins; desf.
  rewrite seq_eqvC in X. 
  unfold sb_ext; rewrite !seqA, X; relsimp; rewrite X.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
Qed.

Lemma gstep_eqa_rel_write (W : is_write a) :
  <| eq a |> ;; rel acts' sb' rmw' rf' <--> 
  <| eq a |> ;; <| is_rel |>. 
Proof.
  rewrite gstep_rel_write; relsimp.
  rewrite seq_eqvC, (seq2 (seq_eqvC _ (eq a))), seqA, (seq2 (seq_eqvK _)).
  split; repeat apply inclusion_union_l; eauto with rel. 
  by cdes GSTEP; rewrite seq_eq_max; ins; red; ins; eapply rel_acta in REL; eauto.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
Qed.

(*
Lemma gstep_singl_rel b :
  singl_rel b a ;; <| is_ra |> ;; rel acts' sb' rmw' rf' <--> 
  singl_rel b a ;; <| is_write |> ;; <| is_ra |>.
Proof.
  assert (X: singl_rel b a <--> singl_rel b a ;; <| eq a |>).
    by rewrite seq_eqv_r; unfold singl_rel; split; red; ins; desf.
  rewrite X, !seqA, (seq2 (seq_eqvC _ _)), seqA, gstep_eqa_rel. 
  by rewrite (seq2 (seq_eqvC _ _)), seqA, (seq2 (seq_eqvK _)). 
Qed.
*)

Lemma gstep_sb_ext_rel_write (W : is_write a) :
  sb_ext ;; rel acts' sb' rmw' rf' <--> 
  sb_ext ;; <| is_rel |>. 
Proof.
  unfold sb_ext; rewrite !seqA; auto using gstep_eqa_rel_write, seq_more.
Qed.

Lemma gstep_sc_ext_rel_write (W : is_write a) :
  sc_ext ;; rel acts' sb' rmw' rf' <--> 
  sc_ext ;; <| is_rel |>. 
Proof.
  assert (X: sc_ext <--> sc_ext ;; <| eq a |>).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  by rewrite X, !seqA, gstep_eqa_rel_write.
Qed.

Lemma gstep_urr_rel_write (F: is_write a) :
  urr_rel acts' sb' rmw' rf' sc' <--> 
  urr_rel acts sb rmw rf sc +++
  <| eq a |> ;; <| is_rel |> +++
  urr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext +++
  urr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext +++
  urr acts sb rmw rf sc ;; sb_ext ;; <| is_rel |>.
Proof.
  assert (N: ~ is_fence a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold urr_rel.
  rewrite gstep_urr_write; ins; relsimp.
  rewrite gstep_eqa_rel_write, gstep_sb_ext_rel_write; ins.

  rewrite gstep_rel_write; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  red; ins; exfalso; unfold seq, eqv_rel in *; desf.
  apply GSTEP; eapply urr_actb in H; eauto.
Qed.

Lemma gstep_rwr_rel_write (F: is_write a) :
  rwr_rel acts' sb' rmw' rf' sc' <--> 
  rwr_rel acts sb rmw rf sc +++
  <| eq a |> ;; <| is_rel |> +++
  rwr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext +++
  rwr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext +++
  rwr acts sb rmw rf sc ;; sb_ext ;; <| is_rel |>.
Proof.
  assert (N: ~ is_fence a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold rwr_rel.
  rewrite gstep_rwr_write; ins; relsimp.
  rewrite gstep_eqa_rel_write, gstep_sb_ext_rel_write; ins.

  rewrite gstep_rel_write; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  red; ins; exfalso; unfold seq, eqv_rel in *; desf.
  apply GSTEP; eapply rwr_actb in H; eauto.
Qed.

Lemma gstep_scr_rel_write (F: is_write a) :
  scr_rel acts' sb' rmw' rf' sc' <--> 
  scr_rel acts sb rmw rf sc +++
  <| eq a |> ;; <| is_rel |> +++
  scr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext +++
  scr acts sb rmw rf sc ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext +++
  scr acts sb rmw rf sc ;; sb_ext ;; <| is_rel |> +++
  <| fun x => In x acts |>;;  
  clos_refl (clos_refl rf;; hb acts sb rmw rf;; <| is_fence |>);; sc_ext;; <| is_rel |>.
Proof.
  assert (N: ~ is_fence a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  assert (M: sc_ext;; <| is_write |> <--> sc_ext).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  unfold scr_rel.
  rewrite gstep_scr_write; ins; relsimp.
  rewrite gstep_eqa_rel_write, gstep_sb_ext_rel_write, 
          gstep_sc_ext_rel_write; ins.
  rewrite gstep_rel_write; relsimp.
  split; repeat apply inclusion_union_l; eauto 14 with rel. 
  red; ins; exfalso; unfold seq, eqv_rel in *; desf.
  apply GSTEP; eapply scr_actb in H; eauto.
Qed.

Lemma gstep_urr_rel_nonwrite (N: ~ is_write a) :
  urr_rel acts' sb' rmw' rf' sc' <--> urr_rel acts sb rmw rf sc.
Proof.
  unfold urr_rel; rewrite (gstep_seq_max urr_mon); eauto with rel rel_max.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.

Lemma gstep_rwr_rel_nonwrite (N: ~ is_write a) :
  rwr_rel acts' sb' rmw' rf' sc' <--> rwr_rel acts sb rmw rf sc.
Proof.
  unfold rwr_rel; rewrite (gstep_seq_max rwr_mon); eauto with rel rel_max.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.

Lemma gstep_scr_rel_nonwrite (N: ~ is_write a) :
  scr_rel acts' sb' rmw' rf' sc' <--> scr_rel acts sb rmw rf sc.
Proof.
  unfold scr_rel; rewrite (gstep_seq_max scr_mon); eauto with rel rel_max.
  rewrite gstep_rel_nonwrite; relsimp.
Qed.

(** Easy cases when the thread views do not change *)

Lemma gstep_c_rel_other tm tm' 
      (GA: gstep_a tm tm') (MON: inclusion tm tm') 
      i l l' (NT: thread a <> i
                  \/ ~ is_rel a
                  \/ ~ is_fence a /\ ~ is_write a 
                  \/ is_write a /\ loc a <> Some l) :
  c_rel i l l' tm' <--> c_rel i l l' tm.
Proof.
  unfold c_rel; split; eauto with mon.
  rewrite !eqv_join; rewrite !seq_eqv_r, !seq_eqv_l; red; ins; desc; subst. 
  splits; try done; apply GA; eauto; intro; desf; eauto.
  by destruct a as [??[]].
Qed.

Lemma gstep_c_cur_other tm tm' 
      (GA: gstep_a tm tm') (MON: inclusion tm tm') 
      i l (NT: thread a <> i) :
  c_cur i l tm' <--> c_cur i l tm.
Proof.
  unfold c_cur; split; eauto with mon.
  rewrite !seq_eqv_r, !seq_eqv_l; red; ins; desc; subst. 
  splits; try done; apply GA; eauto; intro; desf; eauto.
Qed.

Lemma gstep_c_acq_other tm tm' 
      (GA: gstep_a tm tm') (MON: inclusion tm tm') 
      i l (NT: thread a <> i) :
  c_acq acts' sb' rmw' rf' i l tm' <--> c_acq acts sb rmw rf i l tm.
Proof.
  unfold c_acq; split; eauto 8 with mon.
  rewrite (gstep_seq_max MON); auto with rel rel_max.
  do 2 (apply seq_mori; ins).
  rewrite (gstep_seq_max rel_mon); auto with rel rel_max.
  rewrite !crE; relsimp.
  rewrite (gstep_seq_max rf_mon); auto with rel rel_max.
Qed.

Lemma gstep_t_rel_other tm 
   (GA: gstep_a (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   (MON: inclusion (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   i l l' (NT: thread a <> i
               \/ ~ is_rel a
               \/ ~ is_fence a /\ ~ is_write a 
               \/ is_write a /\ loc a <> Some l) x :
  t_rel tm acts' sb' rmw' rf' sc' i l l' x <->
  t_rel tm acts sb rmw rf sc i l l' x.
Proof.
  unfold t_rel, dom_rel; split; ins; desc; exists y;
  by eapply (gstep_c_rel_other GA MON).
Qed.

Lemma gstep_t_cur_other tm 
   (GA: gstep_a (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   (MON: inclusion (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   i (NT: thread a <> i) l x :
  t_cur tm acts' sb' rmw' rf' sc' i l  x <->
  t_cur tm acts sb rmw rf sc i l  x.
Proof.
  unfold t_cur, dom_rel; split; ins; desc; exists y;
  by eapply (gstep_c_cur_other GA MON).
Qed.

Lemma gstep_t_acq_other tm 
   (GA: gstep_a (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   (MON: inclusion (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc')) 
   i l (NT: thread a <> i) x :
  t_acq tm acts' sb' rmw' rf' sc' i l x <->
  t_acq tm acts sb rmw rf sc i l x.
Proof.
  unfold t_acq, dom_rel; split; ins; desc; exists y;
  eapply (fun x => gstep_c_acq_other x MON); 
    eauto with rel rel_max.
Qed.

(** Release view for wfences *)

Lemma thr_sb_ext :
  sb_ext ;; <| fun x => thread x = thread a |> <--> sb_ext.
Proof.
  unfold sb_ext; rewrite seq_eqv_l, seq_eqv_r; 
  unfold seq, eqv_rel; split; red; ins; desf; eauto 10.
Qed.

Lemma thr_sb_ext2 :
  <| fun x => thread x = thread a |> ;; sb_ext <--> sb_ext.
Proof.
  unfold sb_ext; rewrite seq_eqv_l, seq_eqv_r; 
  unfold seq, eqv_rel; split; red; ins; desf; eauto 10.
Qed.

(*
Lemma thr_sb_ext i :
  sb_ext ;; <| fun x => thread x = i |> <-->
  <| fun x => thread x = i |> ;; sb_ext.
Proof.
  unfold sb_ext; rewrite seq_eqv_l, seq_eqv_r; 
  unfold seq, eqv_rel; split; red; ins; desf; eauto 10.
Qed.
*)

Lemma gstep_sb_ext_helper_w l (F: is_write a /\ loc a = Some l \/ is_fence a) dom :
  sb_ext;;
        <| dom |>;;
        <| fun x => is_write x /\ loc x = Some l \/ is_fence x |>;;
        <| fun x => thread x = thread a |> <-->
        <| fun x => thread x = thread a |> ;; sb_ext ;; <| dom |>.
Proof.
  unfold sb_ext; rewrite !seqA, !eqv_join, <- !seqA, !eqv_join, !seq_eqv_l, !seq_eqv_r.
  by split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_sc_ext_helper_fence l (F: is_fence a) :
  sc_ext ;; <| is_rel |> ;;
    <| fun x => is_write x /\ loc x = Some l \/ is_fence x |>;;
    <| fun x => thread x = thread a |> <-->
  <| is_sc |> ;; sc_ext.
Proof.
  rewrite !eqv_join, !seq_eqv_l, !seq_eqv_r; unfold sc_ext.
  split; red; ins; desf; splits; eauto 10.
  by destruct a as [??[]]; ins; destruct ow; ins.
Qed.

Lemma gstep_c_rel_urr_fence (RF: is_fence a) l l' :
  c_rel (thread a) l l' (urr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (urr acts sb rmw rf sc) +++
  c_cur (thread a) l' (urr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  c_acq acts sb rmw rf (thread a) l' (urr acts sb rmw rf sc) ;; sb_ext ;;
  <| is_acq /1\ is_rel |> +++
  S_tmr acts sb rmw rf l' ;; sc_ext.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.

  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_urr_fence; try edone.
  relsimp.
  rewrite (seq2 (eqv_join is_acq is_rel)).
  rewrite !gstep_sb_ext_helper_w, gstep_sc_ext_helper_fence; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by rewrite crE; relsimp; eauto 10 with rel.
    by red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
  rewrite crE; relsimp; apply inclusion_union_l; eauto 10 with rel.
  rewrite <- (eqv_join is_acq is_rel).
  rewrite inclusion_seq_eqv_l with (dom := is_acq) at 1; eauto 10 with rel.
Qed.

Lemma gstep_c_rel_rwr_fence (F: is_fence a) l l' :
  c_rel (thread a) l l' (rwr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (rwr acts sb rmw rf sc) +++
  c_cur (thread a) l' (rwr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  c_acq acts sb rmw rf (thread a) l' (rwr acts sb rmw rf sc) ;; sb_ext ;;
  <| is_acq /1\ is_rel |> +++
  S_tmr acts sb rmw rf l' ;; sc_ext.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.

  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_rwr_fence; try edone.
  relsimp.
  rewrite (seq2 (eqv_join is_acq is_rel)).
  rewrite !gstep_sb_ext_helper_w, gstep_sc_ext_helper_fence; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by rewrite crE; relsimp; eauto 10 with rel.
    by red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
  rewrite crE; relsimp; apply inclusion_union_l; eauto 10 with rel.
  rewrite <- (eqv_join is_acq is_rel).
  rewrite inclusion_seq_eqv_l with (dom := is_acq) at 1; eauto 10 with rel.
Qed.

Lemma gstep_c_rel_scr_fence (RF: is_fence a) l l' :
  c_rel (thread a) l l' (scr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (scr acts sb rmw rf sc) +++
  c_cur (thread a) l' (scr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  c_acq acts sb rmw rf (thread a) l' (scr acts sb rmw rf sc) ;; sb_ext ;;
  <| is_acq /1\ is_rel |> +++
  S_tmr acts sb rmw rf l' ;; sc_ext.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_scr_fence; try edone.
  relsimp.
  rewrite (seq2 (eqv_join is_acq is_rel)).
  rewrite !gstep_sb_ext_helper_w, gstep_sc_ext_helper_fence; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by rewrite crE; relsimp; eauto 10 with rel.
    by red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
  rewrite crE; relsimp; apply inclusion_union_l; eauto 10 with rel.
  rewrite <- (eqv_join is_acq is_rel).
  rewrite inclusion_seq_eqv_l with (dom := is_acq) at 1; eauto 10 with rel.
Qed.

Lemma gstep_t_rel_urr_fence (F: is_fence a) l l' x :
  t_rel urr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel urr acts sb rmw rf sc (thread a) l l' x \/
  t_cur urr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  t_acq urr acts sb rmw rf sc (thread a) l' x /\ is_rel a /\ is_acq a \/
  S_tm acts sb rmw rf l' x /\ is_sc a.
Proof.
  unfold t_rel, t_cur, t_acq, S_tm; rewrite gstep_c_rel_urr_fence; try edone;
  autorewrite with rel_dom.
  rewrite !or_assoc; repeat apply or_more; ins;
  unfold sb_ext, sc_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    by unfold c_cur, seq, eqv_rel in *; desf; eapply urr_actb in H1; eauto.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    exploit c_acq_actb; ins; eauto using urr_actb.
    exploit c_acq_doma; ins; desc; eauto using urr_actb.
    exploit c_acq_domb; ins; desc; eauto using urr_actb.

  assert (In y acts /\ is_sc y); desc; eauto 16.
  exploit S_tmr_domb; eauto; exploit S_tmr_actb; eauto.
Qed.


Lemma gstep_t_rel_rwr_fence (F: is_fence a) l l' x :
  t_rel rwr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel rwr acts sb rmw rf sc (thread a) l l' x \/
  t_cur rwr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  t_acq rwr acts sb rmw rf sc (thread a) l' x /\ is_rel a /\ is_acq a \/
  S_tm acts sb rmw rf l' x /\ is_sc a.
Proof.
  unfold t_rel, t_cur, t_acq, S_tm; rewrite gstep_c_rel_rwr_fence; try edone;
  autorewrite with rel_dom. 
  rewrite !or_assoc; repeat apply or_more; ins;
  unfold sb_ext, sc_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    by unfold c_cur, seq, eqv_rel in *; desf; eapply rwr_actb in H1; eauto.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    exploit c_acq_actb; ins; eauto using rwr_actb.
    exploit c_acq_doma; ins; desc; eauto.
    exploit c_acq_domb; ins; desc; eauto.

  assert (In y acts /\ is_sc y); desc; eauto 16.
  exploit S_tmr_domb; eauto; exploit S_tmr_actb; eauto.
Qed.

Lemma gstep_t_rel_scr_fence (F: is_fence a) l l' x :
  t_rel scr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel scr acts sb rmw rf sc (thread a) l l' x \/
  t_cur scr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  t_acq scr acts sb rmw rf sc (thread a) l' x /\ is_rel a /\ is_acq a \/
  S_tm acts sb rmw rf l' x /\ is_sc a.
Proof.
  unfold t_rel, t_cur, t_acq, S_tm; rewrite gstep_c_rel_scr_fence; try edone;
  autorewrite with rel_dom. 
  rewrite !or_assoc; repeat apply or_more; ins;
  unfold sb_ext, sc_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    by unfold c_cur, seq, eqv_rel in *; desf; eapply scr_actb in H1; eauto.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ thread y = thread a);
    desc; eauto 16.
    exploit c_acq_actb; ins; eauto using scr_actb.
    exploit c_acq_doma; ins; desc; eauto.
    exploit c_acq_domb; ins; desc; eauto.

  assert (In y acts /\ is_sc y); desc; eauto 16.
  exploit S_tmr_domb; eauto; exploit S_tmr_actb; eauto.
Qed.


(** Release view for writes *)

Lemma gstep_c_rel_urr_write (W: is_write a) l (LOC: loc a = Some l) l' :
  c_rel (thread a) l l' (urr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (urr acts sb rmw rf sc) +++
  c_cur (thread a) l' (urr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  <| fun x => x = a /\ l = l' /\ is_rel a |>.
Proof.
  unfold c_rel, c_cur.
  rewrite gstep_urr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by unfold seq, eqv_rel; right; desf.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf; 
  subst y; tauto.
Qed.

Lemma gstep_c_rel_rwr_write (W: is_write a) l (LOC: loc a = Some l) l' :
  c_rel (thread a) l l' (rwr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (rwr acts sb rmw rf sc) +++
  c_cur (thread a) l' (rwr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  <| fun x => x = a /\ l = l' /\ is_rel a |>.
Proof.
  unfold c_rel, c_cur.
  rewrite gstep_rwr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by unfold seq, eqv_rel; right; desf.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf; 
  subst y; tauto.
Qed.

Lemma gstep_c_rel_scr_write (W: is_write a) l (LOC: loc a = Some l) l' :
  c_rel (thread a) l l' (scr acts' sb' rmw' rf' sc') <-->
  c_rel (thread a) l l' (scr acts sb rmw rf sc) +++
  c_cur (thread a) l' (scr acts sb rmw rf sc) ;; sb_ext ;; <| is_rel |> +++
  S_tmr acts sb rmw rf l' ;; sc_ext +++
  <| fun x => x = a /\ l = l' /\ is_rel a |>.
Proof.
  assert (N: ~ is_fence a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
clear N N0.
  assert (Y: sc_ext;;
             <| is_rel |>;;
             <| fun x : event => is_write x /\ loc x = Some l \/ is_fence x |>;;
             <| fun x : event => thread x = thread a |> <-->
             <| is_sc |> ;; sc_ext).
    rewrite !eqv_join, !seq_eqv_l, !seq_eqv_r; unfold sc_ext.
    split; red; ins; desf; splits; eauto 10.
    by destruct a as [??[]]; ins; destruct o; ins.

  unfold c_rel, c_cur, S_tmr.
  rewrite gstep_scr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w, Y; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by unfold seq, eqv_rel; right; desf.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf; 
  subst y; tauto.
Qed.

Lemma gstep_t_rel_urr_write (RF: is_write a) l (LOC: loc a = Some l) l' x :
  t_rel urr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel urr acts sb rmw rf sc (thread a) l l' x \/
  t_cur urr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  x = a /\ l = l' /\ is_rel a.
Proof.
  unfold t_cur, t_rel; rewrite gstep_c_rel_urr_write; try edone;
  autorewrite with rel_dom. 
  unfold sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.
  assert (is_write x /\ loc x = Some l' /\ In y acts /\ thread y = thread a); 
    desc; eauto 15.
  by unfold c_cur, seq, eqv_rel in *; desf; eapply urr_actb in H1; eauto. 
Qed.

Lemma gstep_t_rel_rwr_write (RF: is_write a) l (LOC: loc a = Some l) l' x :
  t_rel rwr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel rwr acts sb rmw rf sc (thread a) l l' x \/
  t_cur rwr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  x = a /\ l = l' /\ is_rel a.
Proof.
  unfold t_cur, t_rel; rewrite gstep_c_rel_rwr_write; try edone;
  autorewrite with rel_dom. 
  unfold sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.
  assert (is_write x /\ loc x = Some l' /\ In y acts /\ thread y = thread a); 
    desc; eauto 15.
  by unfold c_cur, seq, eqv_rel in *; desf; eapply rwr_actb in H1; eauto. 
Qed.

Lemma gstep_t_rel_scr_write (RF: is_write a) l (LOC: loc a = Some l) l' x :
  t_rel scr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel scr acts sb rmw rf sc (thread a) l l' x \/
  t_cur scr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  S_tm acts sb rmw rf l' x /\ is_sc a \/
  x = a /\ l = l' /\ is_rel a.
Proof.
  unfold t_cur, t_rel, S_tm; rewrite gstep_c_rel_scr_write; try edone;
  autorewrite with rel_dom. 
  unfold sc_ext, sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.
    assert (is_write x /\ loc x = Some l' /\ In y acts /\ thread y = thread a); 
      desc; eauto 18.
    by unfold c_cur, seq, eqv_rel in *; desf; eapply scr_actb in H1; eauto.
  assert (In y acts /\ is_sc y); desc; eauto 16.
  exploit S_tmr_domb; eauto; exploit S_tmr_actb; eauto.
Qed.

(** Current view for reads *)

Lemma gstep_c_cur_urr_read b (RF: rf' b a) l :
  c_cur (thread a) l (urr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (urr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  <| fun x => is_write x /\ loc x = Some l |> ;; urr_rel acts sb rmw rf sc ;; 
    singl_rel b a ;; <| is_acq |> ;; <| fun x => thread x = thread a |>.
Proof.
  assert (N: ~ is_write a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]]. 
  rewrite crE; unfold c_cur, urr_rel.
  rewrite gstep_urr_read; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  by rewrite !eqv_join; unfold eqv_rel; red; ins; desf.
Qed. 

Lemma gstep_c_cur_rwr_read b (RF: rf' b a) l :
  c_cur (thread a) l (rwr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (rwr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  <| fun x => is_write x /\ loc x = Some l |> ;;
    singl_rel b a ;; <| fun x : event => thread x = thread a |> +++
  <| fun x => is_write x /\ loc x = Some l |> ;; rwr_rel acts sb rmw rf sc ;; 
    singl_rel b a ;; <| is_acq |> ;; <| fun x : event => thread x = thread a |>.
Proof.
  assert (N: ~ is_write a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]]. 
  rewrite crE; unfold c_cur, rwr_rel.
  rewrite gstep_rwr_read; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  by rewrite !eqv_join; unfold eqv_rel; red; ins; desf.
Qed. 

Lemma gstep_c_cur_scr_read b (RF: rf' b a) l :
  c_cur (thread a) l (scr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (scr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  <| fun x : event => is_write x /\ loc x = Some l |> ;;
      singl_rel b a ;; <| fun x => thread x = thread a |> +++
  <| fun x => is_write x /\ loc x = Some l |> ;; scr_rel acts sb rmw rf sc ;; 
      singl_rel b a ;; <| is_acq |> ;; <| fun x => thread x = thread a |>.
Proof.
  assert (N: ~ is_write a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]].
  rewrite crE; unfold c_cur, scr_rel.
  rewrite gstep_scr_read; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  by rewrite !eqv_join; unfold eqv_rel; red; ins; desf.
Qed. 

Lemma gstep_t_cur_urr_read b (RF: rf' b a) l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  msg_rel urr acts sb rmw rf sc l x b /\ is_acq a.
Proof.
  unfold t_cur, msg_rel, m_rel; rewrite gstep_c_cur_urr_read; try edone.
  autorewrite with rel_dom; fold (urr_rel acts sb rmw rf sc).
  unfold seq, eqv_rel, dom_rel, singl_rel; split; ins; desf; eauto 15. 
Qed.

Lemma gstep_t_cur_rwr_read b (RF: rf' b a) l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  msg_rel rwr acts sb rmw rf sc l x b /\ is_acq a \/
  x = b /\ loc x = Some l.
Proof.
  unfold t_cur, msg_rel, m_rel; rewrite gstep_c_cur_rwr_read; try edone;
  autorewrite with rel_dom; fold (rwr_rel acts sb rmw rf sc).
  unfold seq, eqv_rel, dom_rel, singl_rel; split; ins; desf; eauto 15.
  eapply rf_doma in RF; eauto 10.
Qed.

Lemma gstep_t_cur_scr_read b (RF: rf' b a) l x :
  t_cur scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur scr acts sb rmw rf sc (thread a) l x \/
  msg_rel scr acts sb rmw rf sc l x b /\ is_acq a \/
  x = b /\ loc x = Some l.
Proof.
  unfold t_cur, msg_rel, m_rel; rewrite gstep_c_cur_scr_read; try edone;
  autorewrite with rel_dom; fold (scr_rel acts sb rmw rf sc).
  unfold seq, eqv_rel, dom_rel, singl_rel; split; ins; desf; eauto 15.
  eapply rf_doma in RF; eauto 10.
Qed.


(** Current view for rfences *)

Lemma thr_sc_ext :
  sc_ext ;; <| fun x => thread x = thread a |> <--> sc_ext.
Proof.
  unfold sc_ext; rewrite seq_eqv_r; split; red; ins; desf; eauto 10.
Qed.

Lemma thr_sc_ext2 :
  <| is_sc |>;; sc_ext <--> sc_ext.
Proof.
  unfold sc_ext; rewrite seq_eqv_l; split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_c_cur_urr_fence (F: is_fence a) l :
  c_cur (thread a) l (urr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (urr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  c_acq acts sb rmw rf (thread a) l (urr acts sb rmw rf sc) ;;
  sb_ext;; <| is_acq |>;; <| fun x : event => thread x = thread a |> +++
  S_tmr acts sb rmw rf l ;; sc_ext.
Proof.
  rewrite crE; unfold c_cur, c_acq, urr_rel, S_tmr.
  rewrite !seqA, (seq2 thr_sb_ext2).
  rewrite gstep_urr_fence; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2, !thr_sc_ext, !thr_sc_ext2.
  rewrite (crE (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
    rewrite !eqv_join; unfold eqv_rel; red; ins; exfalso; desf.
    by destruct y as [??[]].
  rewrite inclusion_seq_eqv_l with (dom:=is_acq) at 1; rewrite thr_sb_ext; 
  eauto 8 with rel.
Qed.

Lemma gstep_c_cur_rwr_fence (F: is_fence a) l :
  c_cur (thread a) l (rwr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (rwr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  c_acq acts sb rmw rf (thread a) l (rwr acts sb rmw rf sc) ;;
  sb_ext;; <| is_acq |>;; <| fun x => thread x = thread a |> +++
  S_tmr acts sb rmw rf l ;; sc_ext.
Proof.
  rewrite crE; unfold c_cur, c_acq, rwr_rel, S_tmr.
  rewrite !seqA, (seq2 thr_sb_ext2).
  rewrite gstep_rwr_fence; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2, !thr_sc_ext, thr_sc_ext2.
  rewrite (crE (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
    rewrite !eqv_join; unfold eqv_rel; red; ins; exfalso; desf.
    by destruct y as [??[]].
  rewrite inclusion_seq_eqv_l with (dom:=is_acq) at 1; rewrite thr_sb_ext; 
  eauto 8 with rel.
Qed.

Lemma gstep_c_cur_scr_fence (F: is_fence a) l :
  c_cur (thread a) l (scr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (scr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  c_acq acts sb rmw rf (thread a) l (scr acts sb rmw rf sc) ;;
  sb_ext;; <| is_acq |>;; <| fun x : event => thread x = thread a |> +++
  S_tmr acts sb rmw rf l ;; sc_ext.
Proof.
  rewrite crE; unfold c_cur, c_acq, scr_rel, S_tmr.
  rewrite !seqA, (seq2 thr_sb_ext2).
  rewrite gstep_scr_fence; try edone; relsimp.
  rewrite !thr_sb_ext, !thr_sb_ext2, !thr_sc_ext, thr_sc_ext2.
  rewrite (crE (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
    rewrite !eqv_join; unfold eqv_rel; red; ins; exfalso; desf.
    by destruct y as [??[]].
  rewrite inclusion_seq_eqv_l with (dom:=is_acq) at 1; rewrite thr_sb_ext; 
  eauto 8 with rel.
Qed.

Lemma gstep_t_cur_urr_fence (F: is_fence a) l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  t_acq urr acts sb rmw rf sc (thread a) l x /\ is_acq a \/
  S_tm acts sb rmw rf l x /\ is_sc a.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_urr_fence; ins.
  autorewrite with rel_dom; fold (urr_rel acts sb rmw rf sc).
  rewrite eqv_join, seq_eqv_r, !or_assoc; repeat apply or_more;
    unfold sb_ext, sc_ext, clos_refl, eqv_rel, dom_rel, seq;
    split; ins; desf; eauto 12.

  exploit c_acq_actb; ins; eauto using urr_actb.
  exploit c_acq_doma; ins; desc; eauto; exploit c_acq_domb; ins; desc; eauto 12.

  exploit S_tmr_actb; ins; eauto; exploit S_tmr_domb; ins; eauto 8.
Qed.


Lemma gstep_t_cur_rwr_fence (F: is_fence a) l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  t_acq rwr acts sb rmw rf sc (thread a) l x /\ is_acq a \/
  S_tm acts sb rmw rf l x /\ is_sc a.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_rwr_fence; ins.
  autorewrite with rel_dom.
  rewrite eqv_join, seq_eqv_r, !or_assoc; repeat apply or_more;
    unfold sb_ext, sc_ext, clos_refl, eqv_rel, dom_rel, seq;
    split; ins; desf; eauto 12.

  exploit c_acq_actb; ins; eauto using rwr_actb.
  exploit c_acq_doma; ins; desc; eauto; exploit c_acq_domb; ins; desc; eauto 12.

  exploit S_tmr_actb; ins; eauto; exploit S_tmr_domb; ins; eauto 8.
Qed.

Lemma gstep_t_cur_scr_fence (F: is_fence a) l x :
  t_cur scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur scr acts sb rmw rf sc (thread a) l x \/
  t_acq scr acts sb rmw rf sc (thread a) l x /\ is_acq a \/
  S_tm acts sb rmw rf l x /\ is_sc a.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_scr_fence; ins.
  autorewrite with rel_dom.
  rewrite eqv_join, seq_eqv_r, !or_assoc; repeat apply or_more;
    unfold sb_ext, sc_ext, clos_refl, eqv_rel, dom_rel, seq; 
    split; ins; desf; eauto 12.

  exploit c_acq_actb; ins; eauto using scr_actb.
  exploit c_acq_doma; ins; desc; eauto; exploit c_acq_domb; ins; desc; eauto 12.

  exploit S_tmr_actb; ins; eauto; exploit S_tmr_domb; ins; eauto 8.
Qed.

Lemma gstep_c_cur_urr_write (W: is_write a) l :
  c_cur (thread a) l (urr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (urr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, urr_rel, S_tmr.
  rewrite gstep_urr_write; ins; relsimp.
  rewrite !eqv_join, !thr_sb_ext, !thr_sb_ext2.
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  unfold eqv_rel; right; desf; desf.
Qed.

Lemma dom_seq_r2 A (r r': relation A) x :
  dom_rel (r ;; clos_refl r') x <-> dom_rel r x.
Proof.
  unfold clos_refl, seq, dom_rel; split; ins; desf; eauto. 
Qed.

Hint Rewrite dom_seq_r2 : rel_dom.

Lemma dom_seq_sc_ext r (D: domb r is_sc) (A: domb r (fun x => In x acts)) x :
  dom_rel (r ;; sc_ext) x <-> dom_rel r x /\ is_sc a.
Proof.
  unfold domb, seq, dom_rel, sc_ext in *; split; ins; desf; splits; eauto 12. 
Qed.

Hint Rewrite dom_seq_sc_ext : rel_dom.

Lemma gstep_t_cur_urr_write (W: is_write a) l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_urr_write; ins.
  autorewrite with rel_dom; done.
Qed.

Lemma gstep_c_cur_rwr_write (W: is_write a) l :
  c_cur (thread a) l (rwr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (rwr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, urr_rel, S_tmr.
  rewrite gstep_rwr_write; ins; relsimp.
  rewrite !eqv_join, !thr_sb_ext, !thr_sb_ext2.
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  unfold eqv_rel; right; desf; desf.
Qed.

Lemma gstep_t_cur_rwr_write (W: is_write a) l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_rwr_write; ins.
  autorewrite with rel_dom; done.
Qed.

Lemma gstep_sc_ext_l :
  <| is_sc |> ;; sc_ext <--> sc_ext.
Proof.
  unfold sc_ext; rewrite seq_eqv_l.
  by split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_c_cur_scr_write (W: is_write a) l :
  c_cur (thread a) l (scr acts' sb' rmw' rf' sc') <-->
  c_cur (thread a) l (scr acts sb rmw rf sc) ;; clos_refl sb_ext +++
  S_tmr acts sb rmw rf l ;; sc_ext +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, urr_rel, S_tmr.
  rewrite gstep_scr_write; ins; relsimp.
  rewrite !eqv_join, !thr_sb_ext, !thr_sb_ext2, gstep_sc_ext_l, thr_sc_ext.
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  try solve [unfold eqv_rel; right; desf; desf].
Qed.

Lemma gstep_t_cur_scr_write (W: is_write a) l x :
  t_cur scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur scr acts sb rmw rf sc (thread a) l x \/
  S_tm acts sb rmw rf l x /\ is_sc a \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_scr_write; ins.
  autorewrite with rel_dom; eauto using S_tmr_actb, S_tmr_domb. 
  split; ins; desf; eauto.
Qed.

(** Acquire view for non-reads *)

Lemma gstep_c_acq_nonread 
    tm tm' (MON: inclusion tm tm') (GA: gstep_a tm tm') (NR: ~ is_read a) l :
  c_acq acts' sb' rmw' rf' (thread a) l tm' <-->
  c_cur (thread a) l tm' +++
  c_acq acts sb rmw rf (thread a) l tm.
Proof.
  unfold c_acq; rewrite !crE; relsimp.
  rewrite (gstep_seq_max MON GA) with (r'' := _ ;; _); eauto with rel rel_max.
  rewrite (gstep_seq_max rel_mon); eauto with rel rel_max.
  rewrite (gstep_rf_nonread); relsimp. 
  split; repeat apply inclusion_union_l; eauto with rel. 
Qed.

Lemma gstep_t_acq_urr_nonread (NR: ~ is_read a) l x :
  t_acq urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x \/
  t_acq urr acts sb rmw rf sc (thread a) l x.
Proof.
  unfold t_cur, t_acq, msg_rel; rewrite gstep_c_acq_nonread, dom_union; 
    eauto with rel rel_max mon.
Qed.

Lemma gstep_t_acq_rwr_nonread (NR: ~ is_read a) l x :
  t_acq rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x \/
  t_acq rwr acts sb rmw rf sc (thread a) l x.
Proof.
  unfold t_cur, t_acq, msg_rel; rewrite gstep_c_acq_nonread, dom_union; 
    eauto with rel rel_max mon.
Qed.

Lemma gstep_t_acq_scr_nonread (NR: ~ is_read a) l x :
  t_acq scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur scr acts' sb' rmw' rf' sc' (thread a) l x \/
  t_acq scr acts sb rmw rf sc (thread a) l x.
Proof.
  unfold t_cur, t_acq, msg_rel; rewrite gstep_c_acq_nonread, dom_union; 
    eauto with rel rel_max mon.
Qed.


Lemma gstep_c_acq_read 
    tm tm' (MON: inclusion tm tm') (GA: gstep_a tm tm') b (RF: rf' b a) l :
  c_acq acts' sb' rmw' rf' (thread a) l tm' <-->
  c_cur (thread a) l tm' +++
  c_acq acts sb rmw rf (thread a) l tm +++
  m_rel acts sb rmw rf l tm ;; singl_rel b a ;; 
  <| is_rlx_rw |> ;; <| fun x : event => thread x = thread a |>.
Proof.
  unfold c_acq, m_rel; rewrite !crE; relsimp.
  rewrite (gstep_seq_max MON GA) with (r'' := _ ;; _); eauto with rel rel_max.
  rewrite (gstep_seq_max rel_mon); eauto with rel rel_max.
  rewrite (gstep_rf_read RF); relsimp. 
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_t_acq_urr_read b (RF: rf' b a) l x :
  t_acq urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_acq urr acts sb rmw rf sc (thread a) l x \/
  msg_rel urr acts sb rmw rf sc l x b /\ is_rlx_rw a.
Proof.
  unfold t_acq, msg_rel. 
  rewrite gstep_c_acq_read; try exact urr_mon; eauto with rel rel_max. 
  rewrite !dom_union, eqv_join, seq_eqv_r. 
  unfold singl_rel, dom_rel at 3, seq; split; ins; desf; eauto 8.
  eapply gstep_t_cur_urr_read in H; unfold c_acq in *; desf; eauto.
    by rewrite crE; relsimp; rewrite dom_union; eauto.
  right; split; ins.
  by eapply rf_domb in RF; eauto; destruct a as [??[]]; ins; destruct o.
Qed.

Lemma gstep_t_acq_rwr_read b (RF: rf' b a) l x :
  t_acq rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_acq rwr acts sb rmw rf sc (thread a) l x \/
  msg_rel rwr acts sb rmw rf sc l x b /\ is_rlx_rw a \/
  x = b /\ loc b = Some l.
Proof.
  unfold t_acq, msg_rel. 
  rewrite gstep_c_acq_read; try exact rwr_mon; eauto with rel rel_max. 
  rewrite !dom_union, eqv_join, seq_eqv_r. 
  unfold singl_rel, dom_rel at 3, seq; split; ins; desf; eauto 8.
  eapply gstep_t_cur_rwr_read in H; unfold c_acq in *; desf; desf; eauto.
    by rewrite crE; relsimp; rewrite dom_union; eauto.
  right; left; split; ins; desf.
  by eapply rf_domb in RF; eauto; destruct a as [??[]]; ins; destruct o.
  by subst; eauto. 
  by left; left; eapply gstep_t_cur_rwr_read; eauto.
Qed.

Lemma gstep_t_acq_scr_read b (RF: rf' b a) l x :
  t_acq scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_acq scr acts sb rmw rf sc (thread a) l x \/
  msg_rel scr acts sb rmw rf sc l x b /\ is_rlx_rw a \/
  x = b /\ loc b = Some l.
Proof.
  unfold t_acq, msg_rel. 
  rewrite gstep_c_acq_read; try exact scr_mon; eauto with rel rel_max. 
  rewrite !dom_union, eqv_join, seq_eqv_r. 
  unfold singl_rel, dom_rel at 3, seq; split; ins; desf; eauto 8.
  eapply gstep_t_cur_scr_read in H; unfold c_acq in *; desf; desf; eauto.
    by rewrite crE; relsimp; rewrite dom_union; eauto.
  right; left; split; ins; desf.
  by eapply rf_domb in RF; eauto; destruct a as [??[]]; ins; destruct o.
  by subst; eauto. 
  by left; left; eapply gstep_t_cur_scr_read; eauto.
Qed.

(** Changes to [S_tmr] *)

Lemma gstep_S_tmr_other (N: is_read a \/ ~ is_sc a) l :
  S_tmr acts' sb' rmw' rf' l <-->
  S_tmr acts sb rmw rf l.
Proof.
  assert (M: is_read a /\ ~ is_fence a /\ ~ (is_write a /\ loc a = Some l) \/ ~ is_sc a). 
    by desf; eauto; left; destruct a as [??[]]; intuition; ins.
  clear N; unfold S_tmr. 
  rewrite gstep_in_acts; relsimp.
  rewrite (seq_eqvAC _ (eq a)).
  rewrite crE at 2; relsimp.
  rewrite !seq_eq_max; relsimp; eauto with rel rel_max; cycle 1.
    by desf; eauto with rel.
  do 2 (apply seq_more; ins).
  rewrite !crE; relsimp; apply union_more; ins.
  rewrite (gstep_seq_max rf_mon); auto with rel rel_max.
  rewrite (gstep_seq_max hb_mon); desf; auto with rel rel_max.
Qed.

Lemma gstep_S_tm_other (N: is_read a \/ ~ is_sc a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x.
Proof.
  unfold S_tm; rewrite gstep_S_tmr_other; ins.
Qed.

Lemma gstep_S_tmr_write (W: is_write a) l :
  S_tmr acts' sb' rmw' rf' l <-->
  S_tmr acts sb rmw rf l +++ 
  <| fun x => x = a /\ is_sc a /\ loc a = Some l |>.
Proof.
  assert (M: ~ is_read a /\ ~ is_fence a); desc.
    by destruct a as [??[]]; intuition; ins.
  unfold S_tmr, c_cur.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)), !eqv_join; eauto with rel rel_max.
  rewrite (gstep_seq_max (clos_refl_mori rf_mon)); auto with rel rel_max.
  rewrite (gstep_seq_max hb_mon); auto with rel rel_max.
  apply union_more; ins; unfold eqv_rel; split; red; ins; desf; subst y; eauto.
Qed.

Lemma gstep_S_tm_write (W: is_write a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/ x = a /\ is_sc a /\ loc a = Some l.
Proof.
  unfold S_tm; rewrite gstep_S_tmr_write, dom_union, dom_eqv; ins.
Qed.

Lemma gstep_sb_ext_helper_dom (dom : _ -> Prop) (F: dom a) :
  sb_ext ;; <| dom |> <--> sb_ext.
Proof.
  unfold sb_ext; rewrite !seqA, !eqv_join, !seq_eqv_r, !seq_eqv_l.
  by split; red; ins; desf; eauto 10.
Qed.


Lemma dom_rel_sb_ext r (D: domb r (fun x => In x acts)) x :
  dom_rel (r ;; sb_ext) x <->
  dom_rel (r ;; <|fun x => thread x = thread a|>) x.
Proof.
  unfold sb_ext; rewrite <- seqA, !seq_eqv_r; unfold seq, dom_rel.
  split; ins; desf; eauto 8.
Qed.


Lemma gstep_S_tm_fence (F: is_fence a) (SC: is_sc a) (ACQ: is_acq a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/
  t_acq scr acts sb rmw rf sc (thread a) l x.
Proof.
  assert (M: ~ is_read a /\ ~ is_write a); desc.
    by destruct a as [??[]]; intuition; ins.
  unfold S_tm, t_acq, S_tmr.
  rewrite gstep_in_acts; relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r x)), !eqv_join; eauto with rel rel_max.
  rewrite (gstep_seq_max (clos_refl_mori rf_mon)); auto with rel rel_max.
  rewrite union_eq_helper2; [|by red; unfold eqv_rel; ins; desf].
  autorewrite with rel_dom.
  rewrite gstep_hb_fence; relsimp; autorewrite with rel_dom.
  rewrite (seq2 (gstep_sb_ext_helper_dom _ ACQ)),
          !(seq2 (gstep_sb_ext_helper_dom _ F)),
          (gstep_sb_ext_helper_dom _ SC).

  assert (X: c_acq acts sb rmw rf (thread a) l (scr acts sb rmw rf sc) <-->
             <| fun x => In x acts |> ;; 
             c_acq acts sb rmw rf (thread a) l (scr acts sb rmw rf sc)).
  {
    rewrite seq_eqv_l; split; red; ins; desf; split; ins.
    eapply c_acq_acta in H; eauto using scr_acta.
  }
  rewrite X; clear X; autorewrite with rel_dom.
  unfold c_acq, scr.
  rewrite !and_or_l.
  rewrite <- dom_eqv1 with (r := _ ;; _ ;; sb_ext) (d := fun x => In x acts).
  rewrite <- !seqA, !dom_rel_sb_ext, !seqA; 
   eauto 8 using seq_domb, seq_eqv_domb, seq_r_domb, rf_actb, hb_actb, eqv_domb.
  unfold c_acq, scr, rwr, urr; relsimp. 
  autorewrite with rel_dom.
  rewrite (crE rf) at 2 3; relsimp; autorewrite with rel_dom. 
  rewrite !(crE (rfhbsc _ _ _ _ _ ;; _)); relsimp; autorewrite with rel_dom. 
  rewrite !(crE (rel _ _ _ _ ;; _)); relsimp; autorewrite with rel_dom. 
  unfold rfhbsc; relsimp.
  split; ins; desf; eauto 17.
  by destruct H2 as (z & m & A & (? & B & _)); eapply sc_doma in B; eauto;
     left; splits; ins; exists m; apply seq_eqv_r; split; ins.
  by destruct H2 as (z & m & A & (? & B & _)); eapply sc_doma in B; eauto;
     left; splits; ins; exists m; apply seq_eqv_r; split; ins.
  by destruct H1 as (z & m & A & (? & B & _)); eapply sc_doma in B; eauto;
     left; splits; ins; exists m; apply seq_eqv_r; split; ins.
  by destruct H1 as (z & m & A & (? & B & _)); eapply sc_doma in B; eauto;
     left; splits; ins; exists m; apply seq_eqv_r; split; ins.
Qed.



End GstepLemmas.

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
