(******************************************************************************)
(** * Lemmas about Unchanged Relations *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import sflib.
Require Import Event.
Require Import Gevents model Gstep.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Graph_steps_other.

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
          | rewrite restr_eq_seq_eqv_l 
          | rewrite restr_eq_seq_eqv_rel 
          | rewrite restr_eq_union 
          | rewrite clos_refl_union1 
          | rewrite seq_union_l
          | rewrite seq_union_r 
          | rewrite seqA ]; try done.


(** 1. The [msg_rel] relation changes only for writes. *)

Lemma gstep_msg_rel_urr_nonwrite (W: ~ is_write a) l x y :
  msg_rel urr acts' sb' rmw' rf' sc' l x y <-> 
  msg_rel urr acts sb rmw rf sc l x y.
Proof.
  eapply same_relation_exp, gstep_m_rel_nonwrite;
    eauto with mon rel_max.
Qed.

Lemma gstep_msg_rel_rwr_nonwrite (W: ~ is_write a) l x y :
  msg_rel rwr acts' sb' rmw' rf' sc' l x y <-> 
  msg_rel rwr acts sb rmw rf sc l x y.
Proof.
  eapply same_relation_exp, gstep_m_rel_nonwrite; 
    eauto with mon rel_max.
Qed.

(** Easy cases when the thread views do not change *)

Lemma gstep_c_rel_other tm tm' 
      (GA: gstep_a a tm tm') (MON: inclusion tm tm') 
      i l' (NT: thread a <> i
                  \/ ~ is_rel a
                  \/ is_read a) :
  c_rel i l' tm' <--> c_rel i l' tm.
Proof.
  unfold c_rel; split; eauto with mon.
  rewrite !eqv_join; rewrite !seq_eqv_r; red; ins; desc; subst. 
  splits; try done; apply GA; eauto; intro; desf; eauto;
  try by destruct a as [??[]]; try eby eapply init_not_rel.
Qed.

Lemma gstep_c_cur_other tm tm' 
      (GA: gstep_a a tm tm') (MON: inclusion tm tm') 
      i (NT: thread a <> i) :
  c_cur i tm' <--> c_cur i tm.
Proof.
  unfold c_cur; split; eauto with mon.
  rewrite !seq_eqv_r; red; ins; desc; subst. 
  splits; try done; apply GA; eauto; intro; desf; eauto.
  eby eapply gstep_not_init.
Qed.

Lemma gstep_c_acq_other tm tm' 
      (GA: gstep_a a tm tm') (MON: inclusion tm tm') 
      i (NT: thread a <> i) :
  c_acq acts' sb' rmw' rf' i tm' <--> c_acq acts sb rmw rf i tm.
Proof.
  assert (~ is_init a). eby eapply gstep_not_init.
  unfold c_acq; split; eauto 8 with mon.
  rewrite (gstep_seq_max (a:=a) MON); eauto with rel rel_max; cycle 1.
    eapply max_elt_seq2; eauto 6 with rel rel_max.
    by unfold eqv_rel; red; ins; desf; eauto.
  apply seq_mori; ins.
  rewrite (gstep_seq_max (a:=a) (rel_mon GSTEP)); eauto with rel rel_max.
  rewrite !crE; relsimp.
  rewrite (gstep_seq_max (a:=a) (rf_mon GSTEP)); eauto with rel rel_max.
  by unfold seq, eqv_rel; red; ins; desf; eauto.
Qed.

Lemma gstep_t_rel_other tm l
   (GA: gstep_a a (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   (MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   i l' (NT: thread a <> i \/ ~ is_rel a \/ is_read a) x :
  t_rel tm acts' sb' rmw' rf' sc' i l' l x <->
  t_rel tm acts sb rmw rf sc i l' l x.
Proof.
  unfold t_rel, dom_rel; split; ins; desc; exists y;
  by eapply (gstep_c_rel_other GA MON).
Qed.

Lemma gstep_t_cur_other tm l
   (GA: gstep_a a (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   (MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   i (NT: thread a <> i) x :
  t_cur tm acts' sb' rmw' rf' sc' i l  x <->
  t_cur tm acts sb rmw rf sc i l  x.
Proof.
  unfold t_cur, dom_rel; split; ins; desc; exists y;
  by eapply (gstep_c_cur_other GA MON).
Qed.

Lemma gstep_t_acq_other tm l
   (GA: gstep_a a (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   (MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l)) 
   i (NT: thread a <> i) x :
  t_acq tm acts' sb' rmw' rf' sc' i l x <->
  t_acq tm acts sb rmw rf sc i l x.
Proof.
  unfold t_acq, dom_rel; split; ins; desc; exists y;
  eapply (fun x => gstep_c_acq_other x MON); 
    eauto with rel rel_max.
Qed.

(** The global view changes only by SC fences. *)

Lemma gstep_S_tmr_other (N: ~ is_sc_fence a) l :
  S_tmr acts' sb' rmw' rf' l <-->
  S_tmr acts sb rmw rf l.
Proof.
  assert (M: ~ is_fence a \/ ~ is_sc a).
    by destruct a as [??[]]; intuition; ins.
  unfold S_tmr.
  rewrite (gstep_rfhbsc_opt_nonscfence COH GSTEP); relsimp.
    by apply union_eq_helper2; rewrite !eqv_join; unfold eqv_rel; red; ins; desc; subst x y; 
       desf; eauto with acts.
Qed.

Lemma gstep_S_tm_other (N: ~ is_sc_fence a) l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x.
Proof.
  unfold S_tm; rewrite gstep_S_tmr_other; ins.
Qed.

(** The acquire view for non-reads changes exactly as the current view. *)

Lemma gstep_c_acq_nonread 
    tm tm' (MON: inclusion tm tm') (GA: gstep_a a tm tm') (NR: ~ is_read a) :
  c_acq acts' sb' rmw' rf' (thread a) tm' <-->
  c_cur (thread a) tm' +++
  c_acq acts sb rmw rf (thread a) tm.
Proof.
  unfold c_acq; rewrite !crE; relsimp.
  rewrite (gstep_seq_max MON GA) with (r'' := _ ;; _); eauto with rel rel_max.
  rewrite (gstep_seq_max (a:=a) (rel_mon GSTEP)); eauto with rel rel_max.
  rewrite (gstep_rf_nonread COH GSTEP); relsimp. 
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

End Graph_steps_other.
