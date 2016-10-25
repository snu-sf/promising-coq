(******************************************************************************)
(** * Definitions of Graph Steps   *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import sflib.

Require Import Event.

Require Import Gevents model Gstep.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Graph_steps_read.

  Variable acts : list event.
  Variables sb rmw rf mo sc : relation event.
  Variable acts' : list event.  
  Variables sb' rmw' rf' mo' sc' : relation event. 
  
  Hypothesis (COH: Coherent acts sb rmw rf mo sc).
  Variables (prev a : event).
  Hypothesis (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a).
  Variable b : event.
  Hypothesis (RF: rf' b a).


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

Lemma gstep_rf_read :
  rf' <--> rf +++ singl_rel b a.
Proof.
  split; unfold union, singl_rel; red; ins; desf; eauto using (rf_mon GSTEP).
  destruct (classic (y = a)); subst.
    by cdes GSTEP; cdes INC; cdes WF'; cdes WF_RF; eauto.
  by eapply gstep_rf_a in H; vauto.
Qed.

Lemma gstep_sw_read :
  sw acts' sb' rmw' rf' <--> 
  sw acts sb rmw rf +++ 
  rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>.
Proof.
  assert (R: is_read a) by (eapply rf_domb in RF; eauto).
  assert (N: ~ is_write a /\ ~ is_fence a); desc.
    by unfold is_read, is_write, is_fence in *; destruct (lab a); ins.
  unfold sw; rewrite gstep_rel_nonwrite, gstep_rf_read; try edone. 
  relsimp. 
  apply union_more; ins.
  2: by rewrite (fun x => seq2 (seq_singl_max_r _ x)); eauto with rel rel_max. 
   do 2 (apply seq_more; ins). 
  rewrite (gstep_sb COH GSTEP); unfold sb_ext; relsimp.
  rewrite seq_eq_contra2; relsimp.
Qed.

Lemma gstep_hb_read :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++ 
  clos_refl (hb acts sb rmw rf) ;; 
  (sb_ext acts a +++ rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>).
Proof.
  unfold hb; rewrite gstep_sw_read, (gstep_sb COH GSTEP); try edone.
  rewrite unionAC, unionA, unionAC, <- unionA.
  rewrite path_absorb_rt, cr_of_t; ins; unfold sb_ext.
  {
    left; unfold seq, union, eqv_rel, singl_rel; red; ins; desc.
    exfalso.
    assert (z = a); [by clear H0; desf|clear H; desf]. 
      by apply GSTEP; cdes COH; cdes WF; cdes WF_SB; eauto.
    by apply GSTEP; eapply sw_acta; eauto.
  }
  {
    rewrite !seq_eqv_r, !seq_eqv_l; unfold seq, union, eqv_rel, singl_rel; red; ins; desc.
    assert (y = a); [by clear H0; desf|clear H; des; subst y z]. 
      by exfalso; apply GSTEP.
      by eapply rf_domb in RF; eauto; unfold is_init in *; desf.
      by exfalso; apply GSTEP; eapply rel_acta in H0; eauto.
  }
Qed.

Lemma seq_singl_max_eqv_r X (rel : relation X) a' b' d (MAX: max_elt rel b') :
  singl_rel a' b' ;; <| d |> ;; clos_refl rel <--> singl_rel a' b' ;; <| d |>.
Proof.
  rewrite <- seqA. eapply seq_max_r; eauto.
  unfold seq, eqv_rel, singl_rel; ins; desf.
Qed.


Lemma seq_singl_wmax_eqv_r X (rel : relation X) a' b' d (MAX: wmax_elt rel b') :
  singl_rel a' b' ;; <| d |> ;; clos_refl rel <--> singl_rel a' b' ;; <| d |>.
Proof.
  rewrite <- seqA. eapply seq_wmax_r; eauto.
  unfold seq, eqv_rel, singl_rel; ins; desf.
Qed.

Lemma gstep_urr_read l :
  urr acts' sb' rmw' rf' sc' l <-->
  urr acts sb rmw rf sc l +++
  urr acts sb rmw rf sc l ;; sb_ext acts a +++
  urr acts sb rmw rf sc l ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_acq |> +++
  <| fun x : event => is_write x /\ loc x = Some l |> ;; singl_rel b a ;; <| is_rlx_rw |>.
Proof.
  unfold urr.
  assert (NF: ~ is_sc_fence a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]].
  rewrite gstep_rfhbsc_opt_nonscfence; eauto with rel; relsimp.
  rewrite unionA, unionAC, unionC.
  rewrite union_eq_helper2; cycle 1. 
    unfold sc_ext, seq, eqv_rel; red; ins; desc.
    by eapply rf_domb in RF; eauto; destruct a as [??[]]; desf.
  rewrite <- (gstep_sc_nonsc COH GSTEP); try edone. 
  rewrite gstep_rf_read at 2; try edone; relsimp.
  rewrite seq_singl_max_eqv_r; eauto with rel rel_max.
  rewrite gstep_hb_read; eauto; relsimp.
  split; repeat apply inclusion_union_l; eauto 7 with rel.
Qed.

Lemma gstep_act_singl_read : 
  <| fun x => In x acts |>;; singl_rel b a <--> singl_rel b a.
Proof.
  rewrite seq_eqv_l; unfold singl_rel; split; red; ins; desf; intuition.
  cdes GSTEP. 
  exploit rf_acta; eauto; rewrite ACT_STEP; clear ACT_STEP; ins; desf. 
  by exfalso; eapply irr_rf in RF; eauto.
Qed. 

Lemma gstep_singl_domE (d : event -> Prop) (D : d a) : 
  singl_rel b a ;;  <| d |> <--> singl_rel b a.
Proof.
  rewrite seq_eqv_r; split; unfold singl_rel; red; ins; desf.
Qed. 

Lemma gstep_rwr_read l :
  rwr acts' sb' rmw' rf' sc' l <-->
  rwr acts sb rmw rf sc l +++
  rwr acts sb rmw rf sc l ;; sb_ext acts a +++
  rwr acts sb rmw rf sc l ;; rel acts sb rmw rf ;; singl_rel b a;; <| is_acq |> +++
  <| fun x : event => is_write x /\ loc x = Some l |> ;; singl_rel b a.
Proof.
  unfold rwr.
  rewrite seq2; trivial with rel rel_max.
  rewrite gstep_rf_read at 2; try edone; relsimp.
  rewrite seq_singl_max_r; eauto with rel rel_max.
  rewrite gstep_urr_read, gstep_hb_read; try edone.
  relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  by apply inclusion_union_r; right; rewrite inclusion_seq_eqv_r.
Qed.

(** Current view *)


Lemma seq_eqvC A (dom1 dom2 : A -> Prop) :
  eqv_rel dom1 ;; eqv_rel dom2 <--> eqv_rel dom2 ;; eqv_rel dom1.
Proof.
  unfold eqv_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma gstep_c_cur_urr_read l :
  c_cur (thread a) (urr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (urr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  <| fun x : event => is_write x /\ loc x = Some l |> ;; singl_rel b a ;; <| is_rlx_rw |> +++
  urr acts sb rmw rf sc l ;; rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>.
Proof.
  assert (N: ~ is_write a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]]. 
  rewrite crE; unfold c_cur.
  rewrite gstep_urr_read; try edone; relsimp.
  rewrite !(thr_sb_ext GSTEP), !(thr_sb_ext2 GSTEP), seq_eqvC.
  rewrite (fun x => seq2 (gstep_singl_domE _ x)); auto.
  rewrite seq_eqvC, (fun x => seq2 (gstep_singl_domE _ x)); auto.
  split; repeat apply inclusion_union_l; eauto with rel.
Qed. 

Lemma gstep_c_cur_rwr_read l :
  c_cur (thread a) (rwr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  <| fun x => is_write x /\ loc x = Some l |> ;; singl_rel b a +++
  rwr acts sb rmw rf sc l ;; rel acts sb rmw rf ;; singl_rel b a ;; <| is_acq |>.
Proof.
  assert (N: ~ is_write a).
    by eapply rf_domb in RF; eauto; destruct a as [??[]]. 
  rewrite crE; unfold c_cur.
  rewrite gstep_rwr_read; try edone; relsimp.
  rewrite !(thr_sb_ext GSTEP), !(thr_sb_ext2 GSTEP), seq_eqvC.
  rewrite !(fun x => seq2 (gstep_singl_domE (fun x => thread x = thread a \/ is_init x) x));
    auto.
  rewrite !(gstep_singl_domE (fun x => thread x = thread a \/ is_init x)); auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
Qed.

Lemma gstep_t_cur_urr_read l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  msg_rel urr acts sb rmw rf sc l x b /\ is_acq a \/
  x = b /\ loc x = Some l /\ is_rlx_rw a.
Proof.
  unfold t_cur, msg_rel, m_rel; rewrite gstep_c_cur_urr_read; try edone.
  autorewrite with rel_dom.
  unfold seq, eqv_rel, dom_rel, singl_rel; split; ins; desf; eauto 15.
  eapply rf_doma in RF; eauto 10.
Qed.

Lemma gstep_t_cur_rwr_read l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  msg_rel rwr acts sb rmw rf sc l x b /\ is_acq a \/
  x = b /\ loc x = Some l.
Proof.
  unfold t_cur, msg_rel, m_rel; rewrite gstep_c_cur_rwr_read; try edone;
  autorewrite with rel_dom.
  unfold seq, eqv_rel, dom_rel, singl_rel; split; ins; desf; eauto 15.
  eapply rf_doma in RF; eauto 10.
Qed.

(** Acquire view *)

Lemma gstep_c_acq_read 
    tm tm' (MON: inclusion tm tm') (GA: gstep_a a tm tm') :
  c_acq acts' sb' rmw' rf' (thread a) tm' <-->
  c_cur (thread a) tm' +++
  c_acq acts sb rmw rf (thread a) tm +++
  m_rel acts sb rmw rf tm ;; singl_rel b a ;; <| is_rlx_rw |>.
Proof.
  unfold c_acq, m_rel; rewrite !crE; relsimp.
  rewrite (gstep_seq_max MON GA) with (r'' := _ ;; _); eauto with rel rel_max.
  rewrite (gstep_seq_max (a:=a) (rel_mon GSTEP)); eauto with rel rel_max.
  rewrite gstep_rf_read, seq_eqvC; relsimp.
  rewrite !(fun x => seq2 (gstep_singl_domE (fun x => thread x = thread a \/ is_init x) x));
    auto.
   split; repeat apply inclusion_union_l; eauto 10 with rel.
Qed.

Lemma gstep_t_acq_urr_read l x :
  t_acq urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_acq urr acts sb rmw rf sc (thread a) l x \/
  msg_rel urr acts sb rmw rf sc l x b /\ is_rlx_rw a \/
  x = b /\ loc x = Some l /\ is_rlx_rw a.
Proof.
  unfold t_acq, msg_rel. 
  rewrite gstep_c_acq_read; try apply (urr_mon GSTEP); eauto with rel rel_max. 
  rewrite !dom_union, seq_eqv_r. 
  unfold singl_rel, dom_rel at 3, seq; split; ins; desf; eauto 8.
  eapply gstep_t_cur_urr_read in H; unfold c_acq in *; desf; eauto.
    by rewrite crE; relsimp; rewrite dom_union; eauto.
  right; left; split; ins; desf.  
  by eapply rf_domb in RF; eauto; destruct a as [??[]]; ins; destruct o.
  by left; left; eapply gstep_t_cur_urr_read; eauto.
Qed.

Lemma gstep_t_acq_rwr_read l x :
  t_acq rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_acq rwr acts sb rmw rf sc (thread a) l x \/
  msg_rel rwr acts sb rmw rf sc l x b /\ is_rlx_rw a \/
  x = b /\ loc b = Some l.
Proof.
  unfold t_acq, msg_rel. 
  rewrite gstep_c_acq_read; try apply (rwr_mon GSTEP); eauto with rel rel_max. 
  rewrite !dom_union, seq_eqv_r. 
  unfold singl_rel, dom_rel at 3, seq; split; ins; desf; eauto 8.
  eapply gstep_t_cur_rwr_read in H; unfold c_acq in *; desf; desf; eauto.
    by rewrite crE; relsimp; rewrite dom_union; eauto.
  right; left; split; ins; desf.
  by eapply rf_domb in RF; eauto; destruct a as [??[]]; ins; destruct o.
  by left; left; eapply gstep_t_cur_rwr_read; eauto.
Qed.

End Graph_steps_read.  
