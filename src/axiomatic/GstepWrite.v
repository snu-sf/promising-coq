(******************************************************************************)
(** * Lemmas about Writes *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import sflib.
Require Import Event.
Require Import Gevents model Gstep.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Graph_steps_write.

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
  Hint Resolve scr_mon: mon.
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
  Hint Resolve wmax_elt_scr : rel_max.

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
  Hint Resolve gstep_scr_a : rel_max.
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

Hypothesis (W: is_write a).

Hint Resolve (write_non_fence _ W).

Lemma gstep_sw_write  :
  sw acts' sb' rmw' rf' <--> sw acts sb rmw rf.
Proof.
  unfold sw. 
  rewrite (gstep_rel COH GSTEP); relsimp.
  rewrite (fun x => seq2 (seq_eq_max (b:=a) x)); eauto with rel rel_max; relsimp.
  rewrite union_eq_helper2; cycle 1.
    by rewrite !inclusion_seq_eqv_l, (seq_sb_ext_max GSTEP); eauto with rel rel_max. 
  rewrite union_eq_helper2; cycle 1.
    rewrite !inclusion_seq_eqv_l; unfold sb_ext; relsimp.
    rewrite (fun x => seq2 (seq_eq_max x)); eauto with rel rel_max; relsimp.
  rewrite (gstep_rf_nonread COH GSTEP), (gstep_sb GSTEP); ins; relsimp; auto 2 with acts.
  apply union_eq_helper2; ins.
  rewrite seq_sb_ext_max; relsimp; eauto with rel.
Qed.


Lemma gstep_hb_write :
  hb acts' sb' rmw' rf' <--> 
  hb acts sb rmw rf +++
  hb acts sb rmw rf ;; sb_ext acts a +++ 
  sb_ext acts a.
Proof.
  unfold hb; rewrite gstep_sw_write; ins.
  rewrite (gstep_sb GSTEP); relsimp.
  rewrite unionA, unionAC, unionC.
  rewrite path_decomp_u_3, crtE. 
    by relsimp; repeat split; repeat apply inclusion_union_l; eauto with rel.
  rewrite (seq_sb_ext_max GSTEP); ins. 
    apply max_elt_union; red; intros; apply GSTEP; 
    [eapply sb_acta in REL|eapply sw_acta in REL]; 
    eauto.
  by cdes GSTEP; unfold sb_ext, seq, eqv_rel; red; ins; desf.
Qed.

Lemma gstep_urr_write l :
  urr acts' sb' rmw' rf' sc' l <-->
  urr acts sb rmw rf sc l +++
  urr acts sb rmw rf sc l ;; sb_ext acts a +++
  <| fun x => x = a /\ loc a = Some l |>.
Proof.
  assert (~ is_sc_fence a) by (destruct a as [??[]]; done).
  unfold urr.
  rewrite (gstep_rfhbsc_opt_nonscfence COH GSTEP); relsimp.
  rewrite (fun x => seq2 (seq_eq_max_r (b:=a) x)); eauto with rel rel_max; relsimp.
  rewrite seq_eq_max_r, eqv_join; eauto with rel rel_max.
  rewrite (gstep_seq_max (a:=a) (sc_mon GSTEP)); eauto with rel rel_max; relsimp.
  rewrite gstep_hb_write; eauto; relsimp.
  split; repeat (match goal with |- inclusion (_ +++ _) _ => apply inclusion_union_l end);
    eauto 12 with rel. 
  by unfold eqv_rel; repeat right; ins; desf; eauto.
  by rewrite (crE (hb _ _ _ _)) at 1; relsimp; eauto 8 with rel.
  by unfold eqv_rel; repeat right; ins; desf; desf; eauto.
Qed.

Lemma gstep_rwr_write l :
  rwr acts' sb' rmw' rf' sc' l <-->
  rwr acts sb rmw rf sc l +++
  rwr acts sb rmw rf sc l ;; sb_ext acts a +++
  <| fun x => x = a /\ loc a = Some l |>.
Proof.
  unfold rwr; relsimp.
  rewrite (gstep_rf_nonread COH GSTEP) at 2; ins; eauto with acts. 
  rewrite gstep_urr_write, gstep_hb_write; eauto; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
  by rewrite (crE (hb _ _ _ _)) at 1; relsimp; eauto 8 with rel.
Qed.

Lemma gstep_scr_write l :
  scr acts' sb' rmw' rf' sc' l <-->
  scr acts sb rmw rf sc l +++
  scr acts sb rmw rf sc l ;; sb_ext acts a +++
  rfhbsc_opt acts sb rmw rf l;; sc_ext acts a +++
  <| fun x : event => x = a /\ loc a = Some l |>.
Proof.
  assert (X : sc_ext acts a ;; <| is_write |> <--> sc_ext acts a).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  unfold scr; relsimp.
  rewrite (gstep_seq_max (a:=a) (rfhbsc_opt_mon GSTEP (l:=l))); eauto with rel rel_max.
  rewrite (gstep_sc COH GSTEP) at 2; relsimp. 
  rewrite !(seq2 X), seq_sc_ext_max_r; eauto with rel rel_max.
  rewrite gstep_rwr_write, gstep_hb_write; eauto; relsimp.
  split;
    repeat (match goal with |- inclusion (_ +++ _) _ => apply inclusion_union_l end);
    eauto 12 with rel; eauto 20 with rel.
  by rewrite (crE (hb _ _ _ _)) at 1; relsimp; eauto 10 with rel.
Qed.


Lemma gstep_rel_write :
  rel acts' sb' rmw' rf' <--> 
  rel acts sb rmw rf +++
  <| is_rel |> ;; <| eq a |> +++
  <| is_rel |> ;; <| is_write |>;; restr_eq_rel loc (sb_ext acts a) +++
  <| is_rel |> ;; <| is_fence |> ;; sb_ext acts a.
Proof.
  rewrite (gstep_rel COH GSTEP).
  assert (X : <| is_write |>;; <| eq a |> <--> <| eq a |>); [|rewrite X].
    by rewrite seq_eqv_l; unfold eqv_rel; split; red; ins; desf.
  rewrite seq_eqvC in X. 
  unfold sb_ext; rewrite !seqA, X; relsimp; rewrite X.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
Qed.

Lemma gstep_eqa_rel_write : 
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

Lemma gstep_eqv_rel_write (d : event -> Prop) 
      (D: forall x, d x -> x = a)  :
  <| d |> ;; rel acts' sb' rmw' rf' <--> 
  <| d |> ;; <| is_rel |>. 
Proof.
  assert (INC: inclusion <| d |> <| eq a |>).
    by unfold eqv_rel; red; ins; desf; eauto using eq_sym.
  rewrite gstep_rel_write; relsimp.
  split; repeat apply inclusion_union_l; eauto with rel. 
    2: by rewrite inclusion_seq_eqv_r.
    4: by rewrite !eqv_join; unfold eqv_rel, union; red; ins; desf;
          eauto 10 using eq_sym.
  all: rewrite INC at 1.
  by cdes GSTEP; rewrite seq_eq_max; ins; red; ins; eapply rel_acta in REL; eauto.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
  rewrite seq_eq_max; ins; red.
  by unfold sb_ext, seq, eqv_rel, restr_eq_rel; ins; desf; apply GSTEP.
Qed.

Lemma gstep_sb_ext_rel_write :
  sb_ext acts a ;; rel acts' sb' rmw' rf' <--> 
  sb_ext acts a ;; <| is_rel |>. 
Proof.
  unfold sb_ext; rewrite !seqA; auto using gstep_eqa_rel_write, seq_more.
Qed.

Lemma gstep_sc_ext_rel_write :
  sc_ext acts a ;; rel acts' sb' rmw' rf' <--> 
  sc_ext acts a ;; <| is_rel |>. 
Proof.
  assert (X: sc_ext acts a <--> sc_ext acts a ;; <| eq a |>).
    by rewrite seq_eqv_r; unfold sc_ext; split; red; ins; desf.
  by rewrite X, !seqA, gstep_eqa_rel_write.
Qed.

Lemma gstep_urr_rel_write (F: is_write a) l :
  urr acts' sb' rmw' rf' sc' l ;; rel acts' sb' rmw' rf' <--> 
  urr acts sb rmw rf sc l ;; rel acts sb rmw rf +++
  <| fun x => x = a /\ loc a = Some l /\ is_rel a |> +++
  urr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_write |> ;; 
  restr_eq_rel loc (sb_ext acts a) +++
  urr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext acts a +++
  urr acts sb rmw rf sc l ;; sb_ext acts a ;; <| is_rel |>.
Proof.
  rewrite gstep_urr_write; ins; relsimp.
  rewrite gstep_eqv_rel_write, gstep_sb_ext_rel_write; ins; desf.

  rewrite gstep_rel_write, !eqv_join; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel. 
    red; ins; exfalso; unfold seq, eqv_rel in *; desf.
    by apply GSTEP; eapply urr_actb in H; eauto.
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 8. 
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 8. 
Qed.

Lemma gstep_rwr_rel_write l :
  rwr acts' sb' rmw' rf' sc' l ;; rel acts' sb' rmw' rf' <--> 
  rwr acts sb rmw rf sc l ;; rel acts sb rmw rf +++
  <| fun x => x = a /\ loc a = Some l /\ is_rel a |> +++
  rwr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_write |> ;; 
  restr_eq_rel loc (sb_ext acts a) +++
  rwr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext acts a +++
  rwr acts sb rmw rf sc l ;; sb_ext acts a ;; <| is_rel |>.
Proof.
  rewrite gstep_rwr_write; ins; relsimp.
  rewrite gstep_eqv_rel_write, gstep_sb_ext_rel_write; ins; desf.

  rewrite gstep_rel_write, !eqv_join; relsimp.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    red; ins; exfalso; unfold seq, eqv_rel in *; desf.
    by apply GSTEP; eapply rwr_actb in H; eauto.
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 8. 
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 8. 
Qed.

Lemma gstep_scr_rel_write l :
  scr acts' sb' rmw' rf' sc' l ;; rel acts' sb' rmw' rf' <--> 
  scr acts sb rmw rf sc l ;; rel acts sb rmw rf +++
  <| fun x => x = a /\ loc a = Some l /\ is_rel a |> +++
  scr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_write |> ;; 
  restr_eq_rel loc (sb_ext acts a) +++
  scr acts sb rmw rf sc l ;; <| is_rel |> ;; <| is_fence |> ;; sb_ext acts a +++
  scr acts sb rmw rf sc l ;; sb_ext acts a ;; <| is_rel |> +++
  rfhbsc_opt acts sb rmw rf l ;; sc_ext acts a ;; <| is_rel |>.
Proof.
  rewrite gstep_scr_write; ins; relsimp.
  rewrite gstep_eqv_rel_write, gstep_sb_ext_rel_write; ins; desf.
  rewrite gstep_sc_ext_rel_write; ins; desf.
  rewrite gstep_rel_write, !eqv_join; relsimp.
  split; repeat apply inclusion_union_l; eauto 11 with rel.
    red; ins; exfalso; unfold seq, eqv_rel in *; desf.
    by apply GSTEP; eapply scr_actb in H; eauto.
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 10. 
  by unfold union, eqv_rel; red; ins; desf; desf; eauto 10. 
Qed.

Lemma gstep_msg_rel_urr_write1 l (LOC: loc a = Some l) l' :
  msg_rel urr acts' sb' rmw' rf' sc' l' <--> 
  msg_rel urr acts sb rmw rf sc l' +++
  <| fun x => x = a /\ loc a = Some l' /\ is_rel a |> +++
  c_rel (thread a) l (urr acts sb rmw rf sc l') ;; (fun _ y => y = a) +++
  c_cur (thread a) (urr acts sb rmw rf sc l') ;; (fun _ y => y = a /\ is_rel a). 
Proof.
  unfold msg_rel, m_rel, c_rel, c_cur.
  rewrite gstep_urr_rel_write; ins; relsimp.
  unfold sb_ext.
  rewrite !(seq2 (eqv_join _ _)), seq_eqv_r, (seq_eqv_l _ (fun x => In x acts)), 
  !seq_eqv_l, !seq_eqv_r.
  unfold restr_eq_rel.
  split; repeat apply inclusion_union_l; eauto 9 with rel.
  by unfold seq; left; right; desf; rewrite LOC in *; eauto 10.
  by unfold seq; left; right; desf; eauto 10.
  by unfold seq; right; desf; eauto 10.
  unfold seq; red; ins; desf. 
    left; left; right; desf; eexists; splits; eauto; 
      try solve [exploit urr_actb; try eassumption; eauto]; congruence. 
    left; right; desf; eexists; splits; eauto;
      try solve [exploit urr_actb; try eassumption; eauto].
  by unfold seq; right; desf; eexists; splits; eauto;
      try solve [exploit urr_actb; try eassumption; eauto].
Qed.

Lemma gstep_msg_rel_rwr_write1 l (LOC: loc a = Some l) l' :
  msg_rel rwr acts' sb' rmw' rf' sc' l' <--> 
  msg_rel rwr acts sb rmw rf sc l' +++
  <| fun x => x = a /\ loc a = Some l' /\ is_rel a |> +++
  c_rel (thread a) l (rwr acts sb rmw rf sc l') ;; (fun _ y => y = a) +++
  c_cur (thread a) (rwr acts sb rmw rf sc l') ;; (fun _ y => y = a /\ is_rel a). 
Proof.
  unfold msg_rel, m_rel, c_rel, c_cur.
  rewrite gstep_rwr_rel_write; ins; relsimp.
  unfold sb_ext.
  rewrite !(seq2 (eqv_join _ _)), seq_eqv_r, (seq_eqv_l _ (fun x => In x acts)), 
  !seq_eqv_l, !seq_eqv_r.
  unfold restr_eq_rel.
  split; repeat apply inclusion_union_l; eauto 9 with rel.
  by unfold seq; left; right; desf; rewrite LOC in *; eauto 10.
  by unfold seq; left; right; desf; eauto 10.
  by unfold seq; right; desf; eauto 10.
  unfold seq; red; ins; desf. 
    left; left; right; desf; eexists; splits; eauto; 
      try solve [exploit rwr_actb; try eassumption; eauto]; congruence. 
    left; right; desf; eexists; splits; eauto;
      try solve [exploit rwr_actb; try eassumption; eauto].
  by unfold seq; right; desf; eexists; splits; eauto;
      try solve [exploit rwr_actb; try eassumption; eauto].
Qed.

Lemma gstep_msg_rel_scr_write1 l (LOC: loc a = Some l) l' :
  msg_rel scr acts' sb' rmw' rf' sc' l' <--> 
  msg_rel scr acts sb rmw rf sc l' +++
  <| fun x => x = a /\ loc a = Some l' /\ is_rel a |> +++
  c_rel (thread a) l (scr acts sb rmw rf sc l') ;; (fun _ y => y = a) +++
  c_cur (thread a) (scr acts sb rmw rf sc l') ;; (fun _ y => y = a /\ is_rel a) +++
  S_tmr acts sb rmw rf l' ;; (fun _ y => y = a /\ is_sc a).
Proof.
  unfold msg_rel, m_rel, c_rel, c_cur, S_tmr.
  rewrite gstep_scr_rel_write; ins; relsimp.
  unfold sb_ext.
  rewrite !(seq2 (eqv_join _ _)), seq_eqv_r, (seq_eqv_l _ (fun x => In x acts)), 
  !seq_eqv_l, !seq_eqv_r.
  unfold restr_eq_rel, sc_ext.
  split; repeat apply inclusion_union_l; eauto 9 with rel.
  by unfold seq; left; left; right; desf; rewrite LOC in *; eauto 10.
  by unfold seq; left; left; right; desf; eauto 10.
  by unfold seq; left; right; desf; eauto 10.
  by unfold seq; right; desf; eauto 10.
  unfold seq; red; ins; desf. 
    left; left; left; right; desf; eexists; splits; eauto; 
      try solve [exploit scr_actb; try eassumption; eauto]; congruence. 
    left; left; right; desf; eexists; splits; eauto;
      try solve [exploit scr_actb; try eassumption; eauto].
  by unfold seq; left; right; desf; eexists; splits; eauto;
      try solve [exploit scr_actb; try eassumption; eauto].
  unfold seq; right; desf; eexists; splits; eauto;
      try solve [exploit rfhbsc_opt_actb; try eassumption; eauto];
      by destruct a as [??[]]; ins; destruct o.
Qed.

Lemma gstep_msg_rel_urr_write l (LOC: loc a = Some l) l' x y :
  msg_rel urr acts' sb' rmw' rf' sc' l' x y <-> 
  msg_rel urr acts sb rmw rf sc l' x y \/
  x = y /\ y = a /\ loc a = Some l' /\ is_rel a \/
  t_rel urr acts sb rmw rf sc (thread a) l l' x /\ y = a \/
  t_cur urr acts sb rmw rf sc (thread a) l' x /\ y = a /\ is_rel a. 
Proof.
  rewrite (same_relation_exp (gstep_msg_rel_urr_write1 LOC l')).
  unfold t_rel, t_cur, union, seq, eqv_rel, dom_rel; split; ins; desf; eauto 8. 
Qed.

Lemma gstep_msg_rel_rwr_write l (LOC: loc a = Some l) l' x y :
  msg_rel rwr acts' sb' rmw' rf' sc' l' x y <-> 
  msg_rel rwr acts sb rmw rf sc l' x y \/
  x = y /\ y = a /\ loc a = Some l' /\ is_rel a \/
  t_rel rwr acts sb rmw rf sc (thread a) l l' x /\ y = a \/
  t_cur rwr acts sb rmw rf sc (thread a) l' x /\ y = a /\ is_rel a. 
Proof.
  rewrite (same_relation_exp (gstep_msg_rel_rwr_write1 LOC l')).
  unfold t_rel, t_cur, union, seq, eqv_rel, dom_rel; split; ins; desf; eauto 8. 
Qed.

Lemma gstep_msg_rel_scr_write l (LOC: loc a = Some l) l' x y :
  msg_rel scr acts' sb' rmw' rf' sc' l' x y <-> 
  msg_rel scr acts sb rmw rf sc l' x y \/
  x = y /\ y = a /\ loc a = Some l' /\ is_rel a \/
  t_rel scr acts sb rmw rf sc (thread a) l l' x /\ y = a \/
  t_cur scr acts sb rmw rf sc (thread a) l' x /\ y = a /\ is_rel a \/
  S_tm acts sb rmw rf l' x /\ y = a /\ is_sc a. 
Proof.
  rewrite (same_relation_exp (gstep_msg_rel_scr_write1 LOC l')).
  unfold t_rel, t_cur, S_tm, union, seq, eqv_rel, dom_rel; split; ins; desf; eauto 10. 
Qed.


Lemma gstep_S_tmr_write l :
  S_tmr acts' sb' rmw' rf' l <-->
  S_tmr acts sb rmw rf l +++ 
  <| fun x => x = a /\ is_sc a /\ loc a = Some l |>.
Proof.
  assert (M: ~ is_read a /\ ~ is_sc_fence a); desc.
    by destruct a as [??[]]; intuition; ins.
  unfold S_tmr.
  rewrite (gstep_rfhbsc_opt_nonscfence COH GSTEP); relsimp; rewrite !eqv_join.
  apply union_more; ins; unfold eqv_rel; split; red; ins; desf; subst y; eauto.
Qed.

Lemma gstep_S_tm_write l x :
  S_tm acts' sb' rmw' rf' l x <->
  S_tm acts sb rmw rf l x \/ x = a /\ is_sc a /\ loc a = Some l.
Proof.
  unfold S_tm; rewrite gstep_S_tmr_write, dom_union, dom_eqv; ins.
Qed.

Lemma gstep_sb_ext_helper_w2 l :
  sb_ext acts a ;;
        <| is_rel |>;;
        <| fun x => is_write x /\ loc x = Some l \/ is_fence x |>;;
        <| fun x => thread x = thread a |> <-->
        <| fun x => thread x = thread a |> ;; sb_ext acts a ;; 
        <| fun x => loc x = Some l /\ is_rel x |>.
Proof.
  unfold sb_ext; rewrite !seqA, !eqv_join, <- !seqA, !eqv_join, !seq_eqv_l, !seq_eqv_r.
  split; red; ins; desf; splits; try subst a; eauto 10.
  by destruct y as [??[]]; ins.
Qed.

(** Release view for writes *)

Lemma gstep_c_rel_urr_write l l' :
  c_rel (thread a) l' (urr acts' sb' rmw' rf' sc' l) <-->
  c_rel (thread a) l' (urr acts sb rmw rf sc l) +++
  c_cur (thread a)  (urr acts sb rmw rf sc l) ;; sb_ext acts a ;; 
  <| fun x => loc x = Some l' /\ is_rel x |> +++
  <| fun x => x = a /\ loc a = Some l' /\ l = l' /\ is_rel a |>.
Proof.
  unfold c_rel, c_cur.
  rewrite gstep_urr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w2; ins.
  split; repeat apply inclusion_union_l; eauto 12 with rel.
    red; unfold seq, eqv_rel; ins; desf; try (by destruct a as [??[]]).
    by right; eauto.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf. 
  subst y; splits; ins; tauto.
Qed.

Lemma gstep_c_rel_rwr_write l l' :
  c_rel (thread a) l' (rwr acts' sb' rmw' rf' sc' l) <-->
  c_rel (thread a) l' (rwr acts sb rmw rf sc l) +++
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; sb_ext acts a ;; 
  <| fun x => loc x = Some l' /\ is_rel x |> +++
  <| fun x => x = a /\ loc a = Some l' /\ l = l' /\ is_rel a |>.
Proof.
  unfold c_rel, c_cur.
  rewrite gstep_rwr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w2; ins.
  split; repeat apply inclusion_union_l; eauto 12 with rel.
    red; unfold seq, eqv_rel; ins; desf; try (by destruct a as [??[]]).
    by right; eauto.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf. 
  subst y; splits; ins; tauto.
Qed.

Lemma gstep_c_rel_scr_write l l' :
  c_rel (thread a) l' (scr acts' sb' rmw' rf' sc' l) <-->
  c_rel (thread a) l' (scr acts sb rmw rf sc l) +++
  c_cur (thread a) (scr acts sb rmw rf sc l) ;; sb_ext acts a ;;
  <| fun x => loc x = Some l' /\ is_rel x |> +++
  S_tmr acts sb rmw rf l ;; sc_ext acts a ;;
  <| fun x => loc x = Some l' |> +++
  <| fun x => x = a /\ loc a = Some l' /\ l = l' /\ is_rel a |>.
Proof.
  assert (Y: sc_ext acts a ;;
             <| is_rel |>;;
             <| fun x : event => is_write x /\ loc x = Some l' \/ is_fence x |>;;
             <| fun x : event => thread x = thread a |> <-->
             <| is_sc |> ;; sc_ext acts a ;; <| fun x => loc x = Some l' |>).
    rewrite !eqv_join, !seq_eqv_r, !seq_eqv_l; unfold sc_ext.
    split; red; ins; desf; splits; eauto 10;
    by destruct a as [??[]]; ins; destruct o; ins.

  unfold c_rel, c_cur, S_tmr.
  rewrite gstep_scr_write; try edone; relsimp.
  rewrite gstep_sb_ext_helper_w2, Y; auto.
  split; repeat apply inclusion_union_l; eauto 10 with rel.
    red; unfold seq, eqv_rel; ins; desf; try (by destruct a as [??[]]).
    by right; eauto.
  rewrite <- inclusion_union_r2, !eqv_join; unfold eqv_rel; red; ins; desf; 
  subst y; tauto.
Qed.

Lemma gstep_t_rel_urr_write l' l x :
  t_rel urr acts' sb' rmw' rf' sc' (thread a) l' l x <->
  t_rel urr acts sb rmw rf sc (thread a) l' l x \/
  t_cur urr acts sb rmw rf sc (thread a) l x /\ is_rel a /\ loc a = Some l' \/
  x = a /\ loc a = Some l' /\ l = l' /\ is_rel a.
Proof.
  unfold t_cur, t_rel; rewrite gstep_c_rel_urr_write; try edone;
  autorewrite with rel_dom. 
  unfold sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.
  assert (In y acts /\ thread y = thread a); desc; eauto 18.
  by unfold c_cur, seq, eqv_rel in *; desf; eapply urr_actb in H; eauto.
Qed.

Lemma gstep_t_rel_rwr_write l' l x :
  t_rel rwr acts' sb' rmw' rf' sc' (thread a) l' l x <->
  t_rel rwr acts sb rmw rf sc (thread a) l' l x \/
  t_cur rwr acts sb rmw rf sc (thread a) l x /\ is_rel a /\ loc a = Some l' \/
  x = a /\ loc a = Some l' /\ l = l' /\ is_rel a.
Proof.
  unfold t_cur, t_rel; rewrite gstep_c_rel_rwr_write; try edone.
  autorewrite with rel_dom. 
  unfold sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 12.
  assert (In y acts /\ thread y = thread a); desc; eauto 18.
  by unfold c_cur, seq, eqv_rel in *; desf; eapply rwr_actb in H; eauto.
Qed.

Lemma gstep_t_rel_scr_write l l' x :
  t_rel scr acts' sb' rmw' rf' sc' (thread a) l' l x <->
  t_rel scr acts sb rmw rf sc (thread a) l' l x \/
  t_cur scr acts sb rmw rf sc (thread a) l x /\ is_rel a /\ loc a = Some l' \/
  S_tm acts sb rmw rf l x /\ is_sc a /\ loc a = Some l' \/
  x = a /\ loc a = Some l' /\ l = l' /\ is_rel a.
Proof.
  unfold S_tm, t_cur, t_rel; rewrite gstep_c_rel_scr_write; try edone.
  autorewrite with rel_dom. 
  unfold sc_ext, sb_ext, seq, eqv_rel, dom_rel; split; ins; desf; eauto 16.
  assert (In y acts /\ thread y = thread a); desc; eauto 18.
  by unfold c_cur, seq, eqv_rel in *; desf; eapply scr_actb in H; eauto.
  assert (In y acts /\ is_sc y); desc; eauto 18.
  split; [eapply S_tmr_actb in H|eapply S_tmr_domb in H]; eauto.
Qed.

Lemma gstep_c_cur_urr_write l :
  c_cur (thread a) (urr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (urr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, S_tmr.
  rewrite gstep_urr_write; ins; relsimp.
  rewrite !eqv_join, !(thr_sb_ext GSTEP), !(thr_sb_ext2 GSTEP).
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  unfold eqv_rel; right; desf; desf.
Qed.


Lemma dom_seq_sc_ext r (D: domb r is_sc) (A: domb r (fun x => In x acts)) x :
  dom_rel (r ;; sc_ext acts a) x <-> dom_rel r x /\ is_sc a.
Proof.
  unfold domb, seq, dom_rel, sc_ext in *; split; ins; desf; splits; eauto 12. 
Qed.

Hint Rewrite dom_seq_sc_ext : rel_dom.

Lemma gstep_t_cur_urr_write l x :
  t_cur urr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur urr acts sb rmw rf sc (thread a) l x \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_urr_write; ins.
  autorewrite with rel_dom; done.
Qed.

Lemma gstep_c_cur_rwr_write l :
  c_cur (thread a) (rwr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (rwr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, S_tmr.
  rewrite gstep_rwr_write; ins; relsimp.
  rewrite !eqv_join, !(thr_sb_ext GSTEP), !(thr_sb_ext2 GSTEP).
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  unfold eqv_rel; right; desf; desf.
Qed.

Lemma gstep_t_cur_rwr_write l x :
  t_cur rwr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur rwr acts sb rmw rf sc (thread a) l x \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_rwr_write; ins.
  autorewrite with rel_dom; done.
Qed.

Lemma thr_sc_ext :
  sc_ext acts a ;; <| fun x => thread x = thread a |> <--> sc_ext acts a.
Proof.
  unfold sc_ext; rewrite seq_eqv_r; split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_sc_ext_l :
  <| is_sc |> ;; sc_ext acts a <--> sc_ext acts a.
Proof.
  unfold sc_ext; rewrite seq_eqv_l.
  by split; red; ins; desf; eauto 10.
Qed.

Lemma gstep_c_cur_scr_write l :
  c_cur (thread a) (scr acts' sb' rmw' rf' sc' l) <-->
  c_cur (thread a) (scr acts sb rmw rf sc l) ;; clos_refl (sb_ext acts a) +++
  S_tmr acts sb rmw rf l ;; sc_ext acts a +++
  <| fun x => x = a /\ loc x = Some l |>.
Proof.
  rewrite crE; unfold c_cur, c_acq, S_tmr.
  rewrite gstep_scr_write; ins; relsimp.
  rewrite !eqv_join, !(thr_sb_ext GSTEP), !(thr_sb_ext2 GSTEP).

  rewrite gstep_sc_ext_l, thr_sc_ext.
  split; repeat apply inclusion_union_l; eauto 10 with rel;
  try solve [unfold eqv_rel; right; desf; desf].
Qed.

Lemma gstep_t_cur_scr_write l x :
  t_cur scr acts' sb' rmw' rf' sc' (thread a) l x <->
  t_cur scr acts sb rmw rf sc (thread a) l x \/
  S_tm acts sb rmw rf l x /\ is_sc a \/
  x = a /\ loc x = Some l.
Proof.
  unfold t_cur, t_acq, S_tm; rewrite gstep_c_cur_scr_write; ins.
  autorewrite with rel_dom; eauto using S_tmr_actb, S_tmr_domb. 
  split; ins; desf; eauto.
Qed.


End Graph_steps_write.
