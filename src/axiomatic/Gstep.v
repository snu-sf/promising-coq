(******************************************************************************)
(** * Definitions of Graph Steps   *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import sflib.

Require Import Event.

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
  <| d |> ;; <| d' |> <--> <| fun x => d x /\ d' x |>. 
Proof.
  rewrite seq_eqv_l; unfold eqv_rel; split; red; ins; desf.
Qed.

Lemma eqv_joinA A (d d' : A -> Prop) r : 
  <| d |> ;; <| d' |> ;; r <--> <| fun x => d x /\ d' x |> ;; r. 
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


Lemma inclusion_step_r A (r : relation A)  : inclusion r (clos_refl r).
Proof. vauto. Qed.

Lemma inclusion_seq_emp_r A (r r' r'' : relation A) : 
  inclusion r r'' -> inclusion r (clos_refl r' ;; r'').
Proof. rewrite crE ; rel_simpl; eauto with rel. Qed.

Hint Resolve inclusion_step_r inclusion_seq_emp_r : rel.

Lemma dom_seq_eqv2 A (d : A -> Prop) r x (D: d x) :
  dom_rel (<| d |> ;; r) x <-> dom_rel r x.
Proof.
  autorewrite with rel_dom; tauto.
Qed.


Lemma dom_seq_r2 A (r r': relation A) x :
  dom_rel (r ;; clos_refl r') x <-> dom_rel r x.
Proof.
  unfold clos_refl, seq, dom_rel; split; ins; desf; eauto. 
Qed.

Hint Rewrite dom_seq_r2 : rel_dom.


Section Graph_steps.

Variable acts : list event.
Variables sb rmw rf mo sc : relation event.
Variable acts' : list event.  
Variables sb' rmw' rf' mo' sc' : relation event. 
  
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

Definition rmw_step prev a :=
  (rmw' <--> rmw) /\ prev = a \/
  (rmw' <--> rmw +++ singl_rel prev a) /\ prev <> a /\ thread prev = thread a.

Definition gstep prev a :=
  << FRESH: ~ In a acts >> /\
  << ACT_STEP: acts' = a :: acts >> /\
  << SB_STEP: forall x y, sb' x y <-> sb x y 
              \/ ((thread x = thread a \/ is_init x) /\ ~(x=a) /\ y = a) >> /\
  << RMW_STEP: rmw_step prev a >> /\
  << SC_AT_END: forall (SCa: is_sc a) x (SCa: is_sc x), sc' x a >> /\
  << INC: graph_inclusion >> /\
  << WF': Wf acts' sb' rmw' rf' mo' sc' >>.

(******************************************************************************)
(** ** Basic Lemmas    *)
(******************************************************************************)

Section GstepLemmas.

  Hypothesis (COH: Coherent acts sb rmw rf mo sc).
  Variable (prev a : event).
  Hypothesis (GSTEP: gstep prev a).

  Lemma gstep_wf : Wf acts'  sb' rmw' rf' mo' sc'.
  Proof. cdes GSTEP; done. Qed.

  Lemma gstep_inc : graph_inclusion.
  Proof. cdes GSTEP; done. Qed.

  Hint Resolve gstep_wf gstep_inc coh_wf.

  Lemma gstep_proper : is_proper a.
  Proof.
    eapply init_events_wf1; eauto.
    cdes GSTEP; rewrite ACT_STEP; ins; auto.
    intro; cdes GSTEP; cdes COH; cdes WF; cdes WF_ACTS; eauto.
  Qed.

  Lemma gstep_not_init : ~ is_init a.
  Proof.
    eauto using proper_non_init, gstep_proper.
  Qed.

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
  Lemma rfhbsc_opt_mon l : 
    inclusion (rfhbsc_opt acts sb rmw rf l) (rfhbsc_opt acts' sb' rmw' rf' l).
  Proof. unfold rfhbsc_opt; eauto 20 with mon. Qed.
  Hint Resolve rfhbsc_opt_mon: mon.
  Lemma urr_mon l : inclusion (urr acts sb rmw rf sc l) (urr acts' sb' rmw' rf' sc' l).
  Proof. unfold urr; eauto 20 with mon. Qed.
  Hint Resolve urr_mon: mon.
  Lemma rwr_mon l : inclusion (rwr acts sb rmw rf sc l) (rwr acts' sb' rmw' rf' sc' l).
  Proof. unfold rwr; eauto 20 with mon. Qed.
  Hint Resolve rwr_mon: mon.
  Lemma scr_mon l : inclusion (scr acts sb rmw rf sc l) (scr acts' sb' rmw' rf' sc' l).
  Proof. unfold scr; eauto 20 with mon. Qed.
  Hint Resolve scr_mon: mon.
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
    red in RMW_STEP; desf; apply RMW_STEP in REL.
    eapply FRESH, rmw_acta; edone.
    unfold union, singl_rel in REL; desf; try congruence.
    eapply FRESH, rmw_acta; eauto. 
  Qed.

  Lemma max_elt_rf : max_elt rf' a.
  Proof.
    red; ins; assert (X:=REL); eapply rf_actb with (acts:=acts') in X; eauto. 
    cdes GSTEP; cdes INC; subst acts'; clear ACT_STEP; ins; desf.
      by eapply irr_rf with (rf:=rf'); eauto.
    assert(N: exists z, rf z b); desc.
      by eapply COH; eauto; eapply rf_domb; eauto.
    assert(M:=N); apply INC_RF in N. 
    cdes WF'; cdes WF_RF; specialize (RF_FUN _ _ _ N REL); subst. 
    eapply FRESH, rf_acta with (acts:=acts); eauto.
  Qed. 

  Lemma max_elt_sc : max_elt sc' a.
  Proof.
    red; ins; cdes GSTEP; cdes INC; cdes WF'; cdes WF_SC.
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
  Lemma wmax_elt_rfhbsc_opt l : wmax_elt (rfhbsc_opt acts' sb' rmw' rf' l) a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rfhbsc_opt : rel_max.

  Lemma wmax_elt_urr l : wmax_elt (urr acts' sb' rmw' rf' sc' l) a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_urr : rel_max.
  Lemma wmax_elt_rwr l : wmax_elt (rwr acts' sb' rmw' rf' sc' l) a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_rwr : rel_max.
  Lemma wmax_elt_scr l : wmax_elt (scr acts' sb' rmw' rf' sc' l) a.
  Proof. eauto 14 with rel_max rel. Qed.
  Hint Resolve wmax_elt_scr : rel_max.

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

  Lemma gstep_t_wde_a R R' (H1: wmax_elt R' a) (H2: gstep_a R R'): 
    gstep_a (clos_trans R) (clos_trans R').
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
     gstep_id_a gstep_t_wde_a gstep_restr_eq_rel_loc_a: rel_max.

  Lemma gstep_sb_a : gstep_a sb sb'.
  Proof.
    red; ins; cdes GSTEP; cdes INC.
    assert (is_proper y).
      eapply sb_domb; eauto.
    assert (In y acts).
      eapply sb_actb with (acts:=acts') in H; eauto.
      rewrite ACT_STEP in H; ins; desf; eauto.
      exfalso; eauto.
    apply SB_STEP in H; desf; try edone.
  Qed.

  Lemma gstep_rmw_a : gstep_a rmw rmw'.
  Proof.
    red; ins; cdes GSTEP; cdes INC.
    red in RMW_STEP; desf; unfold union, singl_rel in *; desf;
    apply RMW_STEP in H; desf; try done.
  Qed.

  Lemma gstep_rf_a : gstep_a rf rf'.
  Proof.
    red; ins; cdes GSTEP; cdes INC; cdes COH; cdes WF; cdes WF_RF.
    cdes WF'; cdes WF_RF0.
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
    cdes WF'; cdes WF_SC.
    assert (x<>a).
      intro H1. rewrite H1 in *. eby eapply max_elt_sc.
    destruct (classic (x=y)) as [E|N].
      by rewrite E in *; exfalso; eapply SC_IRR; edone.
    cdes COH; cdes WF; eapply WF_SC0 in N; splits; eauto; rewrite ACT_STEP in *.
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
  Lemma gstep_rfhbsc_opt_a l : 
    gstep_a (rfhbsc_opt acts sb rmw rf l) (rfhbsc_opt acts' sb' rmw' rf' l).
  Proof. unfold rfhbsc_opt; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rfhbsc_opt_a : rel_max.
  Lemma gstep_urr_a l : gstep_a (urr acts sb rmw rf sc l) (urr acts' sb' rmw' rf' sc' l).
  Proof. unfold urr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_urr_a : rel_max.
  Lemma gstep_rwr_a l : gstep_a (rwr acts sb rmw rf sc l) (rwr acts' sb' rmw' rf' sc' l).
  Proof. unfold rwr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_rwr_a : rel_max.
  Lemma gstep_scr_a l : gstep_a (scr acts sb rmw rf sc l) (scr acts' sb' rmw' rf' sc' l).
  Proof. unfold scr; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_scr_a : rel_max.

  Lemma gstep_m_rel_a tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' ->
    gstep_a (m_rel acts sb rmw rf tm) (m_rel acts' sb' rmw' rf' tm').
  Proof. unfold m_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_m_rel_a : rel_max.

  Lemma gstep_c_rel_a i l tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_rel i l tm) (c_rel i l tm').
  Proof. unfold c_rel; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_rel_a : rel_max.
   
  Lemma gstep_c_cur_a i tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_cur i tm) (c_cur i tm').
  Proof. unfold c_cur; eauto 30 with rel rel_max. Qed.
  Hint Resolve gstep_c_cur_a : rel_max.
   
  Lemma gstep_c_acq_a i tm tm' : 
    wmax_elt tm' a -> gstep_a tm tm' -> gstep_a (c_acq acts sb rmw rf i tm) (c_acq acts' sb' rmw' rf' i tm').
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
  cdes WF'; cdes WF_MO.
  cdes COH; cdes WF; cdes WF_MO.
  desf; ins.
  cdes WF_RF; cdes WF_MO; cdes INC.
  exploit (RF_TOT a). by left; eauto. eauto with acts.
  intros; desc. exploit rf_lv; try edone; intro; desc.
  eexists; splits; eauto.
  apply RF_ACTa in x0; destruct x0; eauto.
  exfalso; subst; destruct (lab a0); ins.
Qed.

Lemma gstep_mo 
  x y (NEQx: x <> a) (NEQy: y <> a) (MO: mo' x y): mo x y.
Proof.
cdes GSTEP; cdes INC; cdes WF'; cdes WF_MO.
specialize (MO_LOC _ _ MO).
destruct (classic (x=y)) as [E|N].
  by rewrite E in *; exfalso; eapply MO_IRR; edone.
cdes COH; cdes WF; eapply WF_MO0 in N; splits; eauto; rewrite ACT_STEP in *.
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
  cdes WF'; cdes WF_MO.
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
  cdes WF'; cdes WF_SC.
  specialize (SC_DOMa _ _ H); red in SC_DOMa.
  specialize (SC_DOMb _ _ H); red in SC_DOMb.
  unfold is_sc in *.
  eapply gstep_sc_a; try edone;
  by intro A; rewrite A in *; edestruct (lab a); ins.
Qed.

Definition sc_ext x y := 
  In x acts /\ is_sc x /\ is_sc y /\ y = a.

Definition sb_ext :=
  <| fun x => In x acts |> ;; 
  (fun x y => thread x = thread y \/ is_init x) ;; <| eq a |>.

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
  cdes WF'; cdes WF_SC.
  specialize (SC_ACTa _ _ H); subst acts'; ins; des; try subst x. 
    by apply max_elt_sc in H.
  specialize (SC_ACTb _ _ H); ins; des; try subst y; eauto 8.
  left; eapply gstep_sc_a; try edone; intro; subst y; eauto.
Qed.

Lemma inclusion_sb1 : 
  inclusion sb 
    (<| fun x => In x acts |> ;; (fun x y => thread x = thread y \/ init_pair x y) ;; 
     <| fun x => In x acts |>).
Proof.
  clear a GSTEP.
  rewrite seq_eqv_r, seq_eqv_l; red; ins.
  cdes COH; cdes WF; cdes WF_SB; splits; eauto 6.
  apply SB_TID in H; desf; eauto.
Qed.

Lemma sb_sb_ext : inclusion (sb;; sb_ext) sb_ext.
Proof.
  cdes COH; cdes WF; cdes WF_SB; cdes WF_ACTS.
  rewrite inclusion_sb1, inclusion_seq_eqv_r.
  unfold sb_ext, seq, eqv_rel, init_pair; red; ins; desc; subst.  exists z1; splits; eauto.
  exists y; splits; eauto.
  desf.
  - left; splits. congruence. 
  - right; splits; try done. eapply init_events_wf2; eauto.
    intro. eapply init_proper_thread; eauto.
  - right; splits; eauto.
  - exfalso. eapply init_not_proper with (a:=z0); eauto.
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
  cdes WF'; cdes WF_SB.
  assert (is_proper a).
    eapply gstep_proper.
  split; red; ins; unfold union, seq, eqv_rel in *.
  exploit SB_ACTa; try edone; 
  exploit SB_ACTa; try edone;
  exploit SB_TID; try edone;
  rewrite SB_STEP in *; ins.
  - destruct H0; eauto; desc; subst a.
    right; exists x; splits; eauto.
    rewrite ACT_STEP in x1; ins; destruct x1; eauto; subst y.
    exfalso; auto.
  - destruct H0; eauto; desc; subst a.
    subst z z0.
    destruct H1.
    * apply SB_STEP.
      right; splits; eauto.
      intro; subst x; eauto.
    * apply WF_SB. done.
      rewrite ACT_STEP; left; done.
Qed.

Lemma gstep_rmw :
  rmw' <--> rmw +++ (fun x y => x = prev /\ y = a /\ prev <> a /\ is_write a).
Proof.
  cdes GSTEP; cdes RMW_STEP; desf; rewrite RMW_STEP0;
  unfold union, singl_rel; split; red; ins; desf; eauto.
  right; splits; eauto.
  cdes WF'; eapply WF_RMW, RMW_STEP0; vauto.
Qed.

Lemma gstep_rmw_nonwrite (N: ~ is_write a) :
  rmw' <--> rmw.
Proof.
  rewrite gstep_rmw; unfold union; split; red; ins; desf; eauto.
Qed.



Lemma gstep_rf :
  rf' <--> rf +++ <| fun x => In x acts |> ;; rf' ;; <| eq a |>.
Proof.
  rewrite seq_eqv_r, seq_eqv_l.
  split; unfold union, singl_rel; red; ins; desf; eauto using rf_mon.
  destruct (classic (y = a)); subst.
  2: by eapply gstep_rf_a in H; vauto.
  cdes GSTEP; cdes INC; cdes WF'; cdes WF_RF; eauto.
  desf; exploit RF_ACTa; eauto; ins; desf; try subst a; eauto.
  exploit RF_DOMa; eauto; exploit RF_DOMb; eauto; clear.
  by destruct x as [??[]].
Qed.

Lemma gstep_rf_rmw :
  rf' ;; rmw' <--> 
  rf ;; rmw +++
  rf ;; (fun x y => x = prev /\ y = a /\ prev <> a /\ is_write a).
Proof.
  rewrite (gstep_seq_max rf_mon); auto with rel rel_max.
  rewrite gstep_rmw; relsimp; apply union_more, seq_more; ins.
Qed.

Lemma gstep_useq :
  useq rmw' rf' <--> 
  useq rmw rf +++ 
  clos_refl (useq rmw rf) ;; rf ;; 
  (fun x y => x = prev /\ y = a /\ prev <> a /\ is_write a /\ is_rlx_rw a).
Proof.
  unfold useq; rewrite (seq2 gstep_rf_rmw); relsimp.
  rewrite (seq_eqv_r (fun x y : event => x = prev /\ y = a /\ prev <> a /\ is_write a)
                     is_rlx_rw).
  rewrite path_decomp_u_3, cr_of_t. 
  split; repeat apply inclusion_union_l; eauto 6 with rel.
    by unfold seq; right; ins; desf; eauto 10.
    by unfold seq; right; ins; desf; eauto 10.
  by red; unfold seq; ins; desf; cdes GSTEP; eapply rf_acta in H0; eauto.
  by red; unfold seq; ins; desf; cdes GSTEP; eapply rf_acta in H0; eauto.
Qed.

Lemma gstep_rf_rmw_nonwrite (N: ~ is_write a) :
  rf' ;; rmw' <--> rf ;; rmw.
Proof.
  rewrite (gstep_seq_max rf_mon); auto with rel rel_max.
  rewrite gstep_rmw_nonwrite; relsimp.
Qed.

Lemma gstep_useq_nonwrite (N: ~ is_write a) :
  useq rmw' rf' <--> useq rmw rf.
Proof.
  by unfold useq; rewrite (seq2 (gstep_rf_rmw_nonwrite N)), seqA.
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
  rseq acts sb rmw rf ;; rf ;; 
  (fun x y => x = prev /\ y = a /\ prev <> a /\ is_write a /\ is_rlx_rw a) +++
  <| is_write |> ;; restr_eq_rel loc sb_ext ;; <| is_write |> ;; <| is_rlx_rw |> +++
  <| is_write |> ;; <| is_rlx_rw |> ;; <| eq a |>.
Proof.
  unfold rseq; rewrite gstep_in_acts; relsimp.
  apply union_more; cycle 1.
    rewrite (seq_eqvAC (eq a)).
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite 2!(seq_eqvAC (eq a)).
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    by rewrite (seq2 (seq_eqvK _)).
  rewrite gstep_sb at 1; relsimp. 
  unfold sb_ext; relsimp.
  rewrite 3!(seq_eqvAC (eq a)).
  rewrite (seq_eq_max_r), (seq_eqvC (eq a)); eauto with rel rel_max.
  rewrite gstep_useq; relsimp.
  rewrite (seq_eqvAC is_write (fun x => In x acts)), (seq2 (seq_eqvK _)).
  repeat split; repeat apply inclusion_union_l; eauto 10 with rel.
Qed.

Lemma gstep_eq_acts' : 
  <| eq a |>;; <| fun a0 => In a0 acts' |> <--> <| eq a |>.
Proof.
  rewrite gstep_in_acts; relsimp; apply seq_eqvK.
Qed.

Lemma gstep_rel :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  rel acts sb rmw rf ;; rf ;; 
  (fun x y => x = prev /\ y = a /\ prev <> a /\ is_write a /\ is_rlx_rw a) +++
  <| is_rel |> ;; <| is_write |> ;; <| eq a |> +++
  <| is_rel |> ;; <| is_write |> ;; restr_eq_rel loc sb_ext ;; 
  <| is_write |> ;; <| is_rlx_rw |> +++
  <| is_rel |> ;; <| is_fence |> ;; sb_ext ;; <| is_write |> ;; <| is_rlx_rw |>.
Proof.
  unfold rel at 1; rewrite gstep_sb at 1; relsimp.
  assert (X: sb_ext;; rseq acts' sb' rmw' rf' <--> 
             sb_ext;; <| is_write |> ;; <| is_rlx_rw |>).
    unfold sb_ext, rseq; rewrite !seqA.
    rewrite (seq2 gstep_eq_acts').
    rewrite (seq_eqvAC (eq a)).
    rewrite (fun x => seq2 (seq_eq_max_r x)); auto with rel rel_max.
    rewrite 3!(seq_eqvAC (eq a)).
    rewrite (fun x => seq_eq_max_r x); auto with rel rel_max.
    rewrite (seq2 (seq_eqvK _)).
    by rewrite (seq_eqvC _).  
  rewrite X; clear X.
  unfold rel; relsimp.
  rewrite gstep_rseq; relsimp.
  rewrite !(seq2 (seq_eqvK _)), !eqv_join.
  split; repeat apply inclusion_union_l; eauto 20 with rel.
  * by unfold eqv_rel; do 2 left; right; ins; desf.
  * apply inclusion_union_r; right; do 2 (apply seq_mori; ins).
    by rewrite inclusion_restr_eq, inclusion_seq_eqv_l, <- seqA, sb_sb_ext. 
  * red; ins; exfalso; revert H; unfold seq, eqv_rel; ins; desf.
    apply GSTEP; eapply sb_actb in H1; eauto.
  * unfold eqv_rel; left; right; ins; desf; splits; ins.
    by destruct y as [??[]]; ins; destruct o.
Qed.

Lemma gstep_rseq_nonwrite (N: ~ is_write a) :
  rseq acts' sb' rmw' rf' <--> rseq acts sb rmw rf.
Proof.
  unfold rseq; rewrite <- gstep_useq_nonwrite, gstep_in_acts, gstep_sb; ins.
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


Lemma gstep_rfhbsc_opt_nonscfence l (NF: ~ is_sc_fence a) :
  rfhbsc_opt acts' sb' rmw' rf' l <--> 
  rfhbsc_opt acts sb rmw rf l +++ 
  <| fun x : event => is_write x /\ loc x = Some l |>;; <| eq a |>.
Proof.
  unfold rfhbsc_opt.
  rewrite gstep_in_acts; relsimp.
  rewrite crE at 2; relsimp.
  rewrite seq_eq_max; eauto 6 with rel rel_max; relsimp.
  rewrite gstep_rf at 1; relsimp.
  rewrite seq_eq_max; relsimp; auto with rel rel_max; relsimp. 
  rewrite (gstep_seq_max hb_mon); relsimp; auto with rel rel_max; relsimp. 
Qed.

Lemma thr_sb_ext :
  sb_ext ;; <| fun x => thread x = thread a \/ is_init x |> <--> sb_ext.
Proof.
  unfold sb_ext; rewrite seq_eqv_l, seq_eqv_r; 
  unfold seq, eqv_rel; split; red; ins; desf; eauto 10.
Qed.

Lemma thr_sb_ext2 :
  <| fun x => thread x = thread a \/ is_init x|> ;; sb_ext <--> sb_ext.
Proof.
  unfold sb_ext; rewrite seq_eqv_l, seq_eqv_r; 
  unfold seq, eqv_rel; split; red; ins; desf; eauto 10.
Qed.



Lemma gstep_m_rel_nonwrite tm tm' (MON: inclusion tm tm') 
      (GA: gstep_a tm tm') (W: ~ is_write a) :
  m_rel acts' sb' rmw' rf' tm' <--> 
  m_rel acts sb rmw rf tm.
Proof.
  unfold m_rel.
  rewrite (gstep_seq_max MON); eauto with rel rel_max.
  rewrite gstep_rel_nonwrite; ins.
Qed.


Lemma gstep_sb_ext_helper_dom (dom : _ -> Prop) (F: dom a) :
  sb_ext ;; <| dom |> <--> sb_ext.
Proof.
  unfold sb_ext; rewrite !seqA, !eqv_join, !seq_eqv_r, !seq_eqv_l.
  by split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_sc_ext_helper_dom (dom : _ -> Prop) (F: dom a) :
  sc_ext ;; <| dom |> <--> sc_ext.
Proof.
  unfold sc_ext; rewrite seq_eqv_r.
  by split; red; ins; desf; eauto 10.
Qed.


Lemma dom_rel_sb_ext r (D: domb r (fun x => In x acts)) x :
  dom_rel (r ;; sb_ext) x <->
  dom_rel (r ;; <|fun x => thread x = thread a \/ is_init x|>) x.
Proof.
  unfold sb_ext; rewrite <- seqA, !seq_eqv_r; unfold seq, dom_rel.
  split; ins; desf; eauto 8.
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
      ==> same_relation ==> same_relation ==> eq  ==> eq ==> iff as gstep_more.
Proof.
intros acts sb sb0 SB rmw rmw0 RMW rf rf0 RF mo mo0 MO sc sc0 SC.
intros acts' sb' sb0' SB' rmw' rmw0' RMW' rf' rf0' RF' mo' mo0' MO' sc' sc0' SC'.
intros prev a.
unfold gstep, rmw_step; unnw.
rewrite SB, RMW, RF, MO, SC, SB', RMW', RF', MO', SC'.
split; splits; desc; eauto; try (intros; apply SC'; eauto).
by intros; eapply iff_trans; [eby apply iff_sym, same_relation_exp|];
   rewrite H1; split; ins; desf; eauto; left; apply SB.
by intros; eapply iff_trans; [eby apply same_relation_exp|];
   rewrite H1; split; ins; desf; eauto; left; apply SB.
Qed.
