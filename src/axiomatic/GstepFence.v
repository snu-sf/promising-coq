(******************************************************************************)
(** * Lemmas about fences *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import sflib.

Require Import Event.

Require Import Gevents model Gstep.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Graph_steps_fence.

  Variable acts : list event.
  Variables sb rmw rf mo sc : relation event.
  Variable acts' : list event.  
  Variables sb' rmw' rf' mo' sc' : relation event. 
  
  Hypothesis (COH: Coherent acts sb rmw rf mo sc).
  Variables (prev a : event).
  Hypothesis (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a).

  Lemma gstep_wf : Wf acts'  sb' rmw' rf' mo' sc'.
  Proof. cdes GSTEP; done. Qed.

  Hint Resolve gstep_wf coh_wf.

  Hint Resolve 
    inclusion_refl2 clos_refl_mori clos_trans_mori clos_refl_trans_mori 
    restr_rel_mori restr_eq_rel_mori seq_mori union_mori : mon.

  Hint Resolve act_mon sb_mon rmw_mon rf_mon mo_mon sc_mon: mon.
  Hint Resolve useq_mon: mon.
  Hint Resolve rseq_mon: mon.
  Hint Resolve rel_mon: mon.
  Hint Resolve sw_mon: mon.
  Hint Resolve hb_mon: mon.
  Hint Resolve rfhbsc_opt_mon: mon.
  Hint Resolve urr_mon: mon.
  Hint Resolve rwr_mon: mon.
  Hint Resolve S_tmr_mon: mon.

  Hint Resolve wmax_elt_eqv : rel.
  Hint Resolve max_elt_sb max_elt_rmw max_elt_rf max_elt_sc : rel_max.
  Hint Resolve max_elt_useq : rel_max.
  Hint Resolve wmax_elt_rseq : rel_max.
  Hint Resolve wmax_elt_rel : rel_max.
  Hint Resolve max_elt_sw : rel_max.
  Hint Resolve max_elt_hb : rel_max.
  Hint Resolve wmax_elt_rfhbsc_opt : rel_max.
  Hint Resolve wmax_elt_urr : rel_max.
  Hint Resolve wmax_elt_rwr : rel_max.

  Hint Resolve 
     gstep_r_a gstep_seq_wde_a gstep_eqv_rel_a gstep_union_a
     gstep_id_a gstep_t_wde_a gstep_restr_eq_rel_loc_a: rel_max.
  Hint Resolve gstep_sb_a gstep_rmw_a gstep_rf_a gstep_sc_a : rel_max.
  Hint Resolve gstep_useq_a : rel_max.
  Hint Resolve gstep_rseq_a : rel_max.
  Hint Resolve gstep_rel_a : rel_max.
  Hint Resolve gstep_sw_a : rel_max.
  Hint Resolve gstep_hb_a : rel_max.
  Hint Resolve gstep_rfhbsc_opt_a : rel_max.
  Hint Resolve gstep_urr_a : rel_max.
  Hint Resolve gstep_rwr_a : rel_max.
  Hint Resolve gstep_m_rel_a : rel_max.
  Hint Resolve gstep_c_rel_a : rel_max.
  Hint Resolve gstep_c_cur_a : rel_max.
  Hint Resolve gstep_c_acq_a : rel_max.
  Hint Resolve gstep_S_tmr_a : rel_max.

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

Hypothesis (F: is_fence a).

Hint Resolve (fence_non_read a F).

Lemma gstep_sw_fence :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ 
  rel acts sb rmw rf;; rf;; <| is_rlx_rw |>;; sb_ext acts a ;; <| is_acq |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold sw; rewrite (gstep_rel_nonwrite COH GSTEP), 
                     (gstep_rf_nonread COH GSTEP); try edone. 
  relsimp; rewrite !crE; relsimp.
  rewrite unionA; apply union_more; ins.
  rewrite (gstep_sb COH GSTEP); unfold sb_ext; relsimp.
  apply union_more; ins.
  do 5 (apply seq_more; ins); unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
Qed.

Lemma gstep_hb_fence :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++ 
  clos_refl (hb acts sb rmw rf) ;; 
  (sb_ext acts a +++ 
   rel acts sb rmw rf;; rf ;; <| is_rlx_rw |>;; sb_ext acts a ;; <| is_acq |>).
Proof.
  unfold hb; rewrite gstep_sw_fence, (gstep_sb COH GSTEP); try edone.
  rewrite unionAC, unionA, unionAC, <- unionA.
  rewrite path_absorb_rt, cr_of_t; ins.
    left; rewrite inclusion_seq_eqv_r.
    etransitivity. 
      eapply seq_mori, inclusion_refl. 
      instantiate (1 := (fun _ _ => True) ;; <| eq a |>). 
      unfold sb_ext; apply inclusion_union_l; rewrite <- !seqA; apply seq_mori; ins. 
    rewrite seqA, sbsw_de; eauto; relsimp.
  apply transitiveI.
    rewrite inclusion_seq_eqv_r at 1.
    etransitivity. 
      eapply seq_mori, inclusion_refl. 
      instantiate (1 := (fun _ _ => True) ;; <| eq a |>). 
      unfold sb_ext; apply inclusion_union_l; rewrite <- !seqA; apply seq_mori; ins. 
  relsimp.
  rewrite !seq_eq_max; relsimp.
  2: by unfold sb_ext, seq, eqv_rel; red; ins; desf; apply GSTEP.
  unfold rel, rseq, seq, union, eqv_rel, singl_rel; ins; desf.
  by red; ins; apply GSTEP; cdes COH; cdes WF; cdes WF_SB; desf; eauto.
Qed.

Lemma gstep_rfhbsc_opt_fence l :
  rfhbsc_opt acts' sb' rmw' rf' l <--> 
  rfhbsc_opt acts sb rmw rf l +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; sb_ext acts a ;; <| is_sc_fence |> +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf);;
  rel acts sb rmw rf;; rf;; <| is_rlx_rw |>;; sb_ext acts a ;; <| is_acq |> ;; <| is_sc_fence |>.
Proof.
  unfold rfhbsc_opt.
  rewrite (gstep_in_acts GSTEP); relsimp.
  rewrite union_eq_helper2.
    2: by unfold seq, eqv_rel; red; ins; destruct a as [??[]]; desf; ins; desf. 
  rewrite (gstep_rf_nonread COH GSTEP) at 1; eauto; relsimp.
  rewrite gstep_hb_fence; relsimp.
  rewrite unionA; apply union_more; ins.
  rewrite !eqv_doma with (d := fun x => In x acts);
    ins; unfold sb_ext; repeat apply seq_r_doma; 
    eauto using HahnDom.eqv_doma, seq_doma, seq_doma, rf_acta, hb_acta, rel_acta.
Qed.


Lemma gstep_urr_fence l :
  urr acts' sb' rmw' rf' sc' l <-->
  urr acts sb rmw rf sc l +++
  urr acts sb rmw rf sc l ;; sb_ext acts a +++
  urr acts sb rmw rf sc l ;; rel acts sb rmw rf;; rf ;; <| is_rlx_rw |> ;; 
    sb_ext acts a ;; <| is_acq |> +++
  rfhbsc_opt acts sb rmw rf l ;; sc_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf);; sb_ext acts a ;; <| is_sc_fence |> +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf);;
  rel acts sb rmw rf;; rf;; <| is_rlx_rw |>;; sb_ext acts a ;; 
  <| is_acq |>;; <| is_sc_fence |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  assert (X : sc_ext acts a ;; <| is_sc_fence |> <--> sc_ext acts a).
    rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf; eauto 7 with acts.
  unfold urr.
  transitivity (
      rfhbsc_opt acts' sb' rmw' rf' l +++
      rfhbsc_opt acts sb rmw rf l ;;
        clos_refl sc';; clos_refl (hb acts' sb' rmw' rf') +++
      <| fun x => is_write x /\ loc x = Some l |> ;; rf' ;; 
        <| is_rlx_rw |> ;; clos_refl (hb acts' sb' rmw' rf')).
  { rewrite !crE; rel_simpl.
    rewrite !(gstep_seq_max (a:=a) (rfhbsc_opt_mon GSTEP (l:=l))); eauto with rel rel_max. 
    rewrite !seqA.
    split; repeat apply inclusion_union_l; eauto 8 with rel mon.
  }
  rewrite (gstep_sc COH GSTEP); relsimp.
rewrite (seq_sc_ext_max_r); eauto with rel rel_max; relsimp.
  rewrite gstep_hb_fence; try done; relsimp.
  rewrite gstep_rfhbsc_opt_fence; try done; relsimp.
  rewrite (gstep_rf_nonread COH GSTEP); try edone; relsimp.
  split; repeat apply inclusion_union_l; eauto 12 with rel.
  by rewrite <- !inclusion_union_r1; rewrite crE, crE; relsimp; eauto with rel.
Qed.


Lemma gstep_rwr_fence l :
  rwr acts' sb' rmw' rf' sc' l <-->
  rwr acts sb rmw rf sc l +++
  rwr acts sb rmw rf sc l ;; sb_ext acts a +++
  rwr acts sb rmw rf sc l ;; rel acts sb rmw rf ;; rf;; <| is_rlx_rw |> ;; 
    sb_ext acts a ;; <| is_acq |> +++
  rfhbsc_opt acts sb rmw rf l ;; sc_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf);; sb_ext acts a ;; <| is_sc_fence |> +++
  <| fun x => is_write x /\ loc x = Some l |>;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf);;
  rel acts sb rmw rf;; rf;; <| is_rlx_rw |>;; sb_ext acts a ;; 
  <| is_acq |>;; <| is_sc_fence |>.
Proof.
  assert (N: ~ is_write a /\ ~ is_read a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold rwr.
  rewrite seq2; eauto with rel rel_max.
  rewrite (gstep_rf_nonread COH GSTEP) at 2; try edone; relsimp.
  rewrite gstep_urr_fence, gstep_hb_fence; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 12 with rel. 
Qed.


(** Lemmas about sequentially consistent fences *)

Lemma gstep_S_tmr_scfence_expand (SC: is_sc_fence a) l :
  S_tmr acts' sb' rmw' rf' l <-->
        S_tmr acts sb rmw rf l +++
        <| fun x => is_write x /\ loc x = Some l |> ;;
        clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; sb_ext acts a +++
        <| fun x => is_write x /\ loc x = Some l |> ;;
        clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; 
        clos_refl (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>) ;; sb_ext acts a ;; <| is_acq |>.
Proof. 
  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.
  rewrite (crE (_ ;; _)); rel_simpl.
  unfold S_tmr.
  rewrite gstep_rfhbsc_opt_fence; ins.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ FSC)),
          (gstep_sb_ext_helper_dom GSTEP _ FSC).
  relsimp.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ SC)),
          (gstep_sb_ext_helper_dom GSTEP _ SC).
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  rewrite inclusion_seq_eqv_r at 1; eauto with rel.
Qed.

Lemma gstep_S_tmr_sscfence_expand (SC: is_sc_fence a) (ACQ: is_acq a) l :
  S_tmr acts' sb' rmw' rf' l <-->
        S_tmr acts sb rmw rf l +++
        <| fun x => is_write x /\ loc x = Some l |> ;;
        clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; 
        clos_refl (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>) ;; sb_ext acts a.
Proof. 
  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.
  rewrite (crE (_ ;; _)); rel_simpl.
  unfold S_tmr.
  rewrite gstep_rfhbsc_opt_fence; ins.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ FSC)),
          (gstep_sb_ext_helper_dom GSTEP _ FSC).
  relsimp.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ SC)),
          (gstep_sb_ext_helper_dom GSTEP _ SC),
          (gstep_sb_ext_helper_dom GSTEP _ ACQ).
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
Qed.

Lemma gstep_acq_rwr_scfence_expand (SC : is_sc a) l :
  c_acq acts' sb' rmw' rf' (thread a) (rwr acts' sb' rmw' rf' sc' l) <-->
  c_acq acts sb rmw rf (thread a) (rwr acts sb rmw rf sc l) +++
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; sb_ext acts a +++
  c_acq acts sb rmw rf (thread a) (rwr acts sb rmw rf sc l) ;; 
    sb_ext acts a ;; <| is_acq |> +++
  rfhbsc_opt acts sb rmw rf l;; sc_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |> ;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; sb_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |> ;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; 
  clos_refl (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>) ;; sb_ext acts a ;; <| is_acq |>.
Proof.
  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.
  assert (X: sb_ext acts a;; <| is_acq |>;;
             clos_refl (rel acts' sb' rmw' rf';; rf';; <| is_rlx_rw |>);;
             <| fun x => thread x = thread a \/ is_init x |> <-->
             sb_ext acts a;; <| is_acq |>).
    rewrite crE; relsimp.
    rewrite seq_eqvC, (fun x => seq2 (gstep_sb_ext_helper_dom GSTEP _ x)); auto.
    by apply union_eq_helper2; rewrite inclusion_seq_eqv_l, seq_sb_ext_max; 
       eauto with rel rel_max.

  unfold c_cur, c_acq; rewrite gstep_rwr_fence; ins.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ FSC)),
          (gstep_sb_ext_helper_dom GSTEP _ FSC).
  relsimp.
  rewrite X; clear X.
  rewrite !(fun x => seq2 (seq_sb_ext_max_r GSTEP x)); eauto with rel rel_max.
  rewrite !(fun x => seq2 (seq_sc_ext_max_r acts x)); eauto with rel rel_max.
  rewrite !(gstep_sc_ext_helper_dom acts); auto 2.
  rewrite !(gstep_sb_ext_helper_dom GSTEP (fun x => thread x = thread a 
                                                    \/ is_init x)); auto 2.
  rewrite (gstep_seq_max (a:=a) (rel_mon GSTEP)); eauto with rel rel_max.
  rewrite (gstep_rf_nonread COH GSTEP), !unionA; eauto with rel rel_max.
  apply union_more; ins.
  rewrite !(seq2 (thr_sb_ext2 GSTEP)).
  rewrite (thr_sb_ext2 GSTEP).
  rewrite (crE (_ ;; _)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_r at 1; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_r at 1; eauto 10 with rel.
Qed.


Lemma gstep_cur_rwr_scfence_expand (SC : is_sc a) l :
  c_cur (thread a) (rwr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  c_acq acts sb rmw rf (thread a) (rwr acts sb rmw rf sc l) ;; 
    sb_ext acts a ;; <| is_acq |> +++
  rfhbsc_opt acts sb rmw rf l;; sc_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |> ;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; sb_ext acts a +++
  <| fun x => is_write x /\ loc x = Some l |> ;;
  clos_refl rf;; clos_refl (hb acts sb rmw rf) ;; 
  clos_refl (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>) ;; sb_ext acts a ;; <| is_acq |>.
Proof.
  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.
  assert (X: sb_ext acts a;; <| is_acq |>;;
             <| fun x => thread x = thread a \/ is_init x |> <-->
             sb_ext acts a;; <| is_acq |>).
    by rewrite seq_eqvC, (fun x => seq2 (gstep_sb_ext_helper_dom GSTEP _ x)); auto.

  rewrite (crE (sb_ext acts a)); rel_simpl.
  unfold c_cur, c_acq; rewrite gstep_rwr_fence; ins.
  rewrite seq_eqvC.
  rewrite (seq2 (gstep_sb_ext_helper_dom GSTEP _ FSC)),
          (gstep_sb_ext_helper_dom GSTEP _ FSC).
  relsimp.
  rewrite X; clear X.
  rewrite !(gstep_sb_ext_helper_dom GSTEP (fun x => thread x = thread a 
                                                    \/ is_init x)); auto 2.
  rewrite !(seq2 (thr_sb_ext2 GSTEP)), (thr_sb_ext2 GSTEP).
  rewrite !(gstep_sc_ext_helper_dom acts); auto 2.
  rewrite (crE (_ ;; _)); relsimp. 
  split; repeat apply inclusion_union_l; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_r at 1; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_r at 1; eauto 10 with rel.
Qed.

Lemma gstep_t_rel_urr_scfence (SC: is_sc_fence a) l' l x :
  t_rel urr acts' sb' rmw' rf' sc' (thread a) l' l x <->
  S_tm acts' sb' rmw' rf' l x.
Proof.
  destruct (classic (is_write x /\ loc x = Some l /\ In x acts')); cycle 1.
    by split; intros; desf; destruct H; splits;
       eauto with rel acts. 

  assert (M: ~ is_read a /\ ~ is_write a /\ <<REL: is_rel a >> /\ << FSC: is_sc_fence a >>); desc.
    eauto 10 with acts.

  unfold t_rel, S_tm, S_tmr, c_rel, urr, rfhbsc_opt.
  rewrite !eqv_join, !seqA, !dom_seq_eqv2; ins.
  split; cycle 1.
- intros (z & y & D & <- & K).
    eexists a, a. split; ins.
   left; repeat eexists; eauto.
   destruct (classic (y = a)); subst; vauto.
    cdes GSTEP; right; unfold seq, eqv_rel; eauto.
    apply SC_AT_END; eauto.
    unfold clos_refl at 1, seq, eqv_rel in D; desf; subst; eauto with acts.
       by simpls; desf; eauto.
    eapply hb_actb in D0; eauto.
    by simpl in D0; desf; eauto; congruence.
  by exists a; repeat eexists; eauto.
- rewrite !(crE (_ ;; _)); relsimp.
  rewrite seq_eqvK.
  rewrite !dom_union; intro X; desf; revert X; rewrite !dom_seq_eqv2; ins.
  * right; exists a; apply seqA; eapply seq_eqv_r; split; try done.
    exists x; splits; vauto.
    unfold dom_rel, clos_refl, eqv_rel, seq in *; desc; eauto.
    destruct H2; try by eapply sc_doma in H2; eauto; destruct x as [??[]]; ins.
    subst z z0.
    destruct H7; try eby exfalso; eapply init_not_rel.
    destruct (classic (y = a)); try subst y. 
    by destruct H3; vauto.
    eapply clos_refl_seq_step; eauto using hb_trans.
    eapply sb_in_hb; cdes GSTEP; apply SB_AT_END; eauto.
    { destruct H3; subst; eauto.
      by destruct H1; subst; eauto; exfalso; auto.
      eapply hb_actb in H3; eauto.
      by destruct H3; subst; eauto; exfalso; auto. }
  * unfold dom_rel, clos_refl, eqv_rel, seq in *; desc; eauto 10.
  * right.
    unfold dom_rel, clos_refl, eqv_rel, seq in *; desc; subst.
    exists a, z0; splits; auto.
    exists a; splits; auto.
    destruct (classic (y = a)); try subst y.
    by destruct H4; vauto; destruct a as [??[]]; ins.
    destruct H8; try eby exfalso; eapply init_not_rel.
    eapply clos_refl_seq_step; eauto using hb_trans.
    eapply sb_in_hb; cdes GSTEP; apply SB_AT_END; vauto.
    { eapply rf_actb in H2; eauto.
      destruct H4; subst; eauto.
      by destruct H2; subst; eauto; exfalso; auto.
      eapply hb_actb in H4; eauto.
      by destruct H4; subst; eauto; exfalso; auto. }
Qed.

Lemma gstep_S_tm_wscfence (SC: is_sc_fence a) (NRA: ~ is_acq a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/
  t_cur rwr acts sb rmw rf sc (thread a) l x.
Proof.
  destruct (classic (is_write x /\ loc x = Some l /\ In x acts)); cycle 1.
    split; intros; desf; destruct H; splits;
    eauto with rel acts. 
    assert (AA: In x acts') by (eapply dom_in_acts; eauto using S_tmr_acta).
    cdes GSTEP; rewrite ACT_STEP in AA; ins; des; try subst x; ins.
    by apply S_tm_dom1 in H0; destruct a as [??[]].

  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.

  unfold S_tm; rewrite gstep_S_tmr_scfence_expand, dom_union, dom_seq_eqv2; 
  ins; auto with acts.
  rewrite seq_sb_ext_max; eauto with rel; relsimp.

  rewrite (crE rf); relsimp; eauto.
  rewrite !dom_union, <- (dom_seq_eqv2 (fun x => In x acts) (_ ;; _)); ins.
  rewrite !dom_seq_eqv2; ins.
  unfold t_cur, c_cur.
  rewrite <- dom_rel_sb_ext with (acts:=acts); eauto using rwr_actb.
  unfold S_tmr, rwr, rwr, urr; relsimp.
  rewrite ?dom_union, !dom_seq_eqv2; ins.
  autorewrite with rel_dom.
  unfold rfhbsc_opt; relsimp.
  rewrite !dom_seq_eqv2; ins.
  rewrite (crE (clos_refl rf;; hb acts sb rmw rf;; <| is_sc_fence |>)) at 3; relsimp.
  rewrite (crE rf) at 3; relsimp.
  autorewrite with rel_dom.
  unfold dom_rel; split; intro K; desf; 
    try by unfold clos_refl, eqv_rel, seq in *; desf; eauto 15.
  destruct K as [x' [[X|X] K]]; subst; eauto.
  by eapply sc_doma in X; eauto; destruct x as [??[]]; ins.
Qed.

Lemma gstep_S_tm_sscfence (SC: is_sc_fence a) (ACQ: is_acq a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/
  t_acq rwr acts sb rmw rf sc (thread a) l x.
Proof.
  destruct (classic (is_write x /\ loc x = Some l /\ In x acts)); cycle 1.
    split; intros; desf; destruct H; splits;
    eauto with rel acts. 
    assert (AA: In x acts') by (eapply dom_in_acts; eauto using S_tmr_acta).
    cdes GSTEP; rewrite ACT_STEP in AA; ins; des; try subst x; ins.
    by apply S_tm_dom1 in H0; destruct a as [??[]].

  assert (M: ~ is_read a /\ ~ is_write a /\ << FSC: is_sc_fence a >>); desc.
    by destruct a as [??[]]; intuition; ins.

  unfold S_tm; rewrite gstep_S_tmr_sscfence_expand, dom_union, dom_seq_eqv2; 
  ins; auto with acts.

  rewrite (crE rf); relsimp; eauto.
  rewrite dom_union, <- (dom_seq_eqv2 (fun x => In x acts) (_ ;; _)); ins.
  rewrite <- !seqA, !dom_rel_sb_ext, !seqA, dom_seq_eqv2;
    eauto 15 using rf_actb, hb_actb, seq_domb, eqv_domb, seq_eqv_domb, seq_r_domb.
  unfold S_tmr, t_acq, c_acq, rwr, urr; relsimp.
  rewrite (crE sc); relsimp. 
  autorewrite with rel_dom.
  unfold rfhbsc_opt; relsimp.
  rewrite !dom_seq_eqv2; ins.
  rewrite seq_eqv_r.
  unfold dom_rel; split; intro K; desf; eauto 20.
  by right; left; left; left; exists y, x; vauto.
  by destruct K as (m & A & B); destruct A as [->|A]; desf; eauto;
     left; eexists; split; eauto; unfold seq, eqv_rel in A; desf; auto with acts.
  by destruct K as (m & A & (? & B & _)); eapply sc_doma in B; eauto;
     left; splits; ins; exists m; apply seq_eqv_r; split; ins.
  by unfold clos_refl, eqv_rel, seq in *; desf; eauto 20.
Qed.


Lemma gstep_S_tm_scfence (SC: is_sc_fence a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  t_acq rwr acts sb rmw rf sc (thread a) l x /\ is_acq a.
Proof.
  destruct (classic (is_acq a));
    [rewrite gstep_S_tm_sscfence | rewrite gstep_S_tm_wscfence]; ins; 
    split; ins; desf; eauto using inclusion_refl2, t_cur_acq_mon.
Qed.



Lemma gstep_t_cur_rwr_scfence (SC: is_sc_fence a) l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  S_tm acts' sb' rmw' rf' l x.
Proof.
  split; [|by rewrite <- gstep_t_rel_urr_scfence with (l':=l); ins; eauto with rel_mon].
  unfold S_tm, t_cur.
  rewrite gstep_cur_rwr_scfence_expand, !dom_union, dom_seq_r2; ins; desf; auto with acts.
    by apply gstep_S_tm_scfence; eauto.
    by apply gstep_S_tm_scfence; eauto;
       unfold t_acq, dom_rel, sb_ext, seq, eqv_rel in *; desf; eauto.
    2: by rewrite gstep_S_tmr_scfence_expand, !dom_union; eauto.
    2: by rewrite gstep_S_tmr_scfence_expand, !dom_union; eauto.
    unfold dom_rel, S_tmr, sc_ext, eqv_rel, seq in *; desf. 
    eby eexists; eexists; splits; try apply (rfhbsc_opt_mon GSTEP).
Qed.

Lemma gstep_t_acq_rwr_scfence (SC: is_sc_fence a) (ACQ: is_acq a) l x :
  t_acq rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  S_tm acts' sb' rmw' rf' l x.
Proof.
  split; [|by rewrite <- gstep_t_rel_urr_scfence with (l':=l); ins; eauto with rel_mon].
  unfold S_tm, t_acq.
  rewrite gstep_acq_rwr_scfence_expand, !dom_union; ins; desf; auto with acts.
    by apply gstep_S_tm_scfence; eauto.
    by apply gstep_S_tm_scfence; eauto;
       unfold t_cur, t_acq, dom_rel, sb_ext, seq, eqv_rel in *; desf; eauto.
    by apply gstep_S_tm_scfence; eauto;
       unfold t_cur, t_acq, dom_rel, sb_ext, seq, eqv_rel in *; desf; eauto.
    2: by rewrite gstep_S_tmr_scfence_expand, !dom_union; eauto.
    2: by rewrite gstep_S_tmr_scfence_expand, !dom_union; eauto.
    unfold dom_rel, S_tmr, sc_ext, eqv_rel, seq in *; desf. 
    eby eexists; eexists; splits; try apply (rfhbsc_opt_mon GSTEP).
Qed.

Section EasyCases.

  Hypotheses (SC: is_sc_fence a).
  Variables (l' l : Loc.t) (x : event).
  Ltac local := split; 
     solve [rewrite <- gstep_t_acq_rwr_scfence; eauto with rel_mon |
           rewrite <- gstep_t_cur_rwr_scfence; eauto with rel_mon |
           rewrite <- gstep_t_rel_urr_scfence with (l':=l); eauto with rel_mon | 
           rewrite <- gstep_t_rel_urr_scfence; eauto with rel_mon ].
  Hint Resolve inclusion_refl2 : rel_mon.

  Lemma gstep_t_acq_urr_scfence (ACQ: is_acq a) :
    t_acq urr acts' sb' rmw' rf' sc' (thread a) l x <->
    S_tm acts' sb' rmw' rf' l x.
  Proof. local. Qed.

  Lemma gstep_t_cur_urr_scfence :
    t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
    S_tm acts' sb' rmw' rf' l x.
  Proof. local. Qed.

  Lemma gstep_t_rel_rwr_scfence :
    t_rel rwr acts' sb' rmw' rf' sc' (thread a) l' l x <->
    S_tm acts' sb' rmw' rf' l x.
  Proof. local. Qed.

End EasyCases.


(** Lemmas about non-SC fences: how the release view is updated. *)


Lemma gstep_sb_ext_helper_w l dom :
  sb_ext acts a ;;
        <| dom |>;;
        <| fun x => is_write x /\ loc x = Some l \/ is_fence x |>;;
        <| fun x => thread x = thread a \/ is_init x |> <-->
        <| fun x => thread x = thread a \/ is_init x  |> ;; sb_ext acts a ;; <| dom |>.
Proof.
  unfold sb_ext; rewrite !seqA, !eqv_join, <- !seqA, !eqv_join, !seq_eqv_l, !seq_eqv_r.
  by split; red; ins; desf; eauto 12.
Qed.

Lemma gstep_sc_ext_helper_fence l :
  sc_ext acts a ;; <| is_rel |> ;;
    <| fun x => is_write x /\ loc x = Some l \/ is_fence x |>;;
    <| fun x => thread x = thread a \/ is_init x |> <-->
  <| is_sc |> ;; sc_ext acts a.
Proof.
  rewrite !eqv_join, !seq_eqv_l, !seq_eqv_r; unfold sc_ext.
  split; red; ins; desf; splits; eauto 10 with acts.
Qed.

Section NonSCfences.

Hypothesis (NSC: ~ is_sc a).

Let non_sc_fence : ~ is_sc_fence a.
Proof.
  auto with acts.
Qed.

Hint Resolve non_sc_fence .

Lemma gstep_sc_ext_rafence :
  sc_ext acts a <--> (fun _ _ => False).
Proof.
  by unfold sc_ext; split; red; ins; desf; auto with acts.
Qed.

Lemma gstep_c_rel_urr_rafence l l' :
  c_rel (thread a) l' (urr acts' sb' rmw' rf' sc' l) <-->
  c_rel (thread a) l' (urr acts sb rmw rf sc l) +++
  c_cur (thread a) (urr acts sb rmw rf sc l) ;; sb_ext acts a ;; <| is_rel |> +++
  c_acq acts sb rmw rf (thread a) (urr acts sb rmw rf sc l) ;; sb_ext acts a ;;
  <| fun x => is_acq x /\ is_rel x |>.
Proof.
  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_urr_fence, gstep_sc_ext_rafence; try edone.
  rewrite !seq_sb_ext_max with (r := <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seq_sb_ext_max with (r := _ ;; <| is_sc_fence |>); eauto with rel rel_max.
  relsimp.
  rewrite (seq2 (eqv_join is_acq is_rel)).
  rewrite !gstep_sb_ext_helper_w; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by rewrite crE; relsimp; eauto 10 with rel.
  rewrite crE; relsimp; apply inclusion_union_l; eauto 10 with rel.
  rewrite <- (eqv_join is_acq is_rel).
  rewrite inclusion_seq_eqv_l with (dom := is_acq) at 1; eauto 10 with rel.
Qed.

Lemma gstep_c_rel_rwr_rafence l l' :
  c_rel (thread a) l' (rwr acts' sb' rmw' rf' sc' l) <-->
  c_rel (thread a) l' (rwr acts sb rmw rf sc l) +++
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; sb_ext acts a ;; <| is_rel |> +++
  c_acq acts sb rmw rf (thread a) (rwr acts sb rmw rf sc l) ;; sb_ext acts a ;;
  <| fun x => is_acq x /\ is_rel x |>.
Proof.
  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_rwr_fence, gstep_sc_ext_rafence; try edone.
  rewrite !seq_sb_ext_max with (r := <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seq_sb_ext_max with (r := _ ;; <| is_sc_fence |>); eauto with rel rel_max.
  relsimp.
  rewrite (seq2 (eqv_join is_acq is_rel)).
  rewrite !gstep_sb_ext_helper_w; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    by rewrite crE; relsimp; eauto 10 with rel.
  rewrite crE; relsimp; apply inclusion_union_l; eauto 10 with rel.
  rewrite <- (eqv_join is_acq is_rel).
  rewrite inclusion_seq_eqv_l with (dom := is_acq) at 1; eauto 10 with rel.
Qed.

Lemma gstep_t_rel_urr_rafence l l' x :
  t_rel urr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel urr acts sb rmw rf sc (thread a) l l' x \/
  t_cur urr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  t_acq urr acts sb rmw rf sc (thread a) l' x /\ is_rel a /\ is_acq a.
Proof.
  unfold t_rel, t_cur, t_acq, S_tm; rewrite gstep_c_rel_urr_rafence; try edone;
  autorewrite with rel_dom.
  rewrite !or_assoc; repeat apply or_more; ins;
  unfold sb_ext, sc_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ 
          (thread y = thread a \/ is_init y));
    desc; eauto 16.
    exploit c_cur_actb; try eassumption; eauto using urr_actb.
    unfold c_cur, urr, rfhbsc_opt, seq, eqv_rel, union in H; desf; eauto.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ 
          (thread y = thread a \/ is_init y));
    desc; eauto 16.
    exploit c_acq_actb; try eassumption; 
    eauto using urr_actb; ins; splits; eauto; pattern x;
    try solve [eapply c_acq_doma; eauto using urr_doma1, urr_doma2 |
               eapply c_acq_domb; eauto].
Qed.

Lemma gstep_t_rel_rwr_rafence l l' x :
  t_rel rwr acts' sb' rmw' rf' sc' (thread a) l l' x <->
  t_rel rwr acts sb rmw rf sc (thread a) l l' x \/
  t_cur rwr acts sb rmw rf sc (thread a) l' x /\ is_rel a \/
  t_acq rwr acts sb rmw rf sc (thread a) l' x /\ is_rel a /\ is_acq a.
Proof.
  unfold t_rel, t_cur, t_acq, S_tm; rewrite gstep_c_rel_rwr_rafence; try edone;
  autorewrite with rel_dom. 
  rewrite !or_assoc; repeat apply or_more; ins;
  unfold sb_ext, sc_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ 
          (thread y = thread a \/ is_init y));
    desc; eauto 16.
    exploit c_cur_actb; try eassumption; eauto using rwr_actb.
    by unfold c_cur, rwr, union, urr, rfhbsc_opt, seq, eqv_rel in *; desf; eauto.

  assert (In y acts /\ is_write x /\ loc x = Some l' /\ 
          (thread y = thread a \/ is_init y));
    desc; eauto 16.
    exploit c_acq_actb; try eassumption; 
    eauto using rwr_actb; ins; splits; eauto; pattern x;
    try solve [eapply c_acq_doma; eauto using rwr_doma1, rwr_doma2 |
               eapply c_acq_domb; eauto].
Qed.

(** How the current view is updated *)

Lemma gstep_c_cur_urr_rafence l :
  c_cur (thread a) (urr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (urr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  c_acq acts sb rmw rf (thread a) (urr acts sb rmw rf sc l) ;;
  sb_ext acts a ;; <| is_acq |> +++
  S_tmr acts sb rmw rf l ;; sc_ext acts a.
Proof.
  rewrite crE; relsimp. 
  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_urr_fence, gstep_sc_ext_rafence; try edone.
  rewrite !seq_sb_ext_max with (r := <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seq_sb_ext_max with (r := _ ;; <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seqA, (seq2 (thr_sb_ext2 GSTEP)).
  relsimp.
  rewrite !(thr_sb_ext GSTEP), (thr_sb_ext2 GSTEP), seq_eqvC.
  rewrite (seq2 (thr_sb_ext GSTEP)).
  rewrite (crE (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
  rewrite inclusion_seq_eqv_r at 1; eauto with rel.
Qed.

Lemma gstep_c_cur_rwr_rafence l :
  c_cur (thread a) (rwr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  c_acq acts sb rmw rf (thread a) (rwr acts sb rmw rf sc l) ;;
  sb_ext acts a ;; <| is_acq |>.
Proof.
  rewrite crE; relsimp. 
  unfold c_rel, c_cur, c_acq, S_tmr.
  rewrite gstep_rwr_fence, gstep_sc_ext_rafence; try edone.
  rewrite !seq_sb_ext_max with (r := <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seq_sb_ext_max with (r := _ ;; <| is_sc_fence |>); eauto with rel rel_max.
  rewrite !seqA, (seq2 (thr_sb_ext2 GSTEP)).
  relsimp.
  rewrite !(thr_sb_ext GSTEP), (thr_sb_ext2 GSTEP), seq_eqvC.
  rewrite (seq2 (thr_sb_ext GSTEP)).
  rewrite (crE (rel acts sb rmw rf;; rf;; <| is_rlx_rw |>)); relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
  rewrite inclusion_seq_eqv_r at 1; eauto with rel.
Qed.

Lemma gstep_t_cur_urr_rafence l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  t_acq urr acts sb rmw rf sc (thread a) l x /\ is_acq a.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_urr_rafence; ins.
  autorewrite with rel_dom.
  rewrite seq_eqv_r, !or_assoc; repeat apply or_more;
    unfold sb_ext, sc_ext, clos_refl, eqv_rel, dom_rel, seq;
    split; ins; desf; eauto 12.
  exploit c_acq_actb; try eassumption; eauto using urr_actb.
  exploit c_acq_domb; try eassumption; ins; desc; eauto 15 with acts.
Qed.

Lemma gstep_t_cur_rwr_rafence l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  t_acq rwr acts sb rmw rf sc (thread a) l x /\ is_acq a.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_rwr_rafence; ins.
  autorewrite with rel_dom.
  rewrite seq_eqv_r; repeat apply or_more;
    unfold sb_ext, sc_ext, clos_refl, eqv_rel, dom_rel, seq;
    split; ins; desf; eauto 12.
  exploit c_acq_actb; try eassumption; eauto using rwr_actb.
  exploit c_acq_domb; try eassumption; ins; desc; eauto 15. 
Qed.


End NonSCfences.

End Graph_steps_fence.
