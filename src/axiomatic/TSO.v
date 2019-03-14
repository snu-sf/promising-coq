(******************************************************************************)
(** * Definition of TSO and relation to the axiomatic promise-free model *)
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
Require Import model.

Set Implicit Arguments.
Remove Hints plus_n_O.

(** Definition of the TSO memory model using a memory order [mo] that is total on
    stores and SC fences. *)

Definition WfTSO_MO acts (mo : relation event) :=
  << MO_ACTa: forall a b (MO: mo a b), In a acts >> /\
  << MO_ACTb: forall a b (MO: mo a b), In b acts >> /\
  << MO_DOMa: forall a b (MO: mo a b), is_write a \/ is_sc_fence a >> /\
  << MO_DOMb: forall a b (MO: mo a b), is_write b \/ is_sc_fence b >> /\
  << MO_IRR: irreflexive mo >> /\
  << MO_T: transitive mo >> /\
  << MO_TOT: is_total (fun a => In a acts /\ (is_write a \/ is_sc_fence a)) mo >>.

Definition WfTSO acts sb rmw rf mo :=
  << WF_ACTS : WfACTS acts >> /\
  << WF_SB   : WfSB acts sb >> /\
  << WF_RMW  : WfRMW sb rmw >> /\
  << WF_RF   : WfRF acts rf >> /\
  << WF_MO   : WfTSO_MO acts mo >>.

Definition reads_before_tso rf mo :=
  transp rf ;; restr_eq_rel loc (restr_rel is_write mo).

Definition external sb rf (x y : event) :=
  rf x y /\ ~ sb x y.

Definition CoherentTSO acts sb rmw rf mo :=
  << WF : WfTSO acts sb rmw rf mo >> /\
  << hbI: acyclic (sb +++ rf) >> /\
  << Cww : irreflexive (mo ;; clos_trans (sb +++ rf)) >> /\
  << Cwr : irreflexive (reads_before_tso rf mo ;; clos_trans (sb +++ rf)) >> /\
  << Cat : Atomicity rmw rf (restr_eq_rel loc (restr_rel is_write mo)) >> /\
  << Crfe: irreflexive (reads_before_tso rf mo ;; mo ;; external sb rf ;; sb) >> /\
  << Cscf: irreflexive (reads_before_tso rf mo ;; mo ;; <| is_sc_fence |> ;; sb) >> /\
  << Cscu: irreflexive (reads_before_tso rf mo ;; mo ;; transp rmw ;; rmw ;; sb) >>.

Hint Immediate inclusion_eqv_rt : rel.

Section Inside_SB_RF.

Variable acts: list event.
Variables sb rmw rf : relation event.
Hypothesis WF_RMW: WfRMW sb rmw.

Lemma rmw_in_sb : inclusion rmw sb.
Proof. apply WF_RMW. Qed.

Lemma useq_in_sb_rf : inclusion (useq rmw rf) (clos_trans (sb +++ rf)).
Proof.
  unfold useq; rewrite rmw_in_sb, inclusion_seq_eqv_r.
  eauto using inclusion_t_t2, inclusion_step2_ct with rel.
Qed.

Lemma rseq_in_sb_rf : inclusion (rseq acts sb rmw rf) (clos_refl_trans (sb +++ rf)).
Proof.
  unfold rseq.
  rewrite !inclusion_seq_eqv_l, useq_in_sb_rf, inclusion_restr_eq, cr_of_t; ins.
  eapply inclusion_seq_rt; eauto with rel. 
Qed.

Lemma rel_in_sb_rf :inclusion (rel acts sb rmw rf) (clos_refl_trans (sb +++ rf)).
Proof.
  unfold rel.
  rewrite !inclusion_seq_eqv_l, rseq_in_sb_rf; ins.
  eapply inclusion_seq_rt; eauto with rel. 
Qed.

Lemma sw_in_sb_rf : inclusion (sw acts sb rmw rf) (clos_trans (sb +++ rf)).
Proof.
  unfold sw; rewrite !inclusion_seq_eqv_l, !inclusion_seq_eqv_r, rel_in_sb_rf; ins.
  rewrite <- rt_ct; apply inclusion_seq_mon; ins. 
  rewrite crE; rel_simpl; eauto using inclusion_step2_ct with rel. 
Qed.

Lemma hb_in_sb_rf : inclusion (hb acts sb rmw rf) (clos_trans (sb +++ rf)).
Proof.
  unfold hb; rewrite sw_in_sb_rf; ins; eauto using inclusion_t_t2 with rel.
Qed.

End Inside_SB_RF.

Lemma sb_rf_to_ext_end acts sb rf (WF: WfSB acts sb) : 
 inclusion (tc (sb +++ rf))
   (sb +++ clos_refl_trans (sb +++ rf) ;; external sb rf ;; clos_refl sb). 
Proof.
  assert (IN: inclusion rf (sb +++ external sb rf)).
    by unfold union, external, inclusion; ins; destruct (classic (sb x y)); auto.
  assert (SB: inclusion (sb ;; sb) sb).
    eby unfold seq, inclusion; ins; desf; eapply WF. 
  assert (SBR: inclusion (clos_refl sb ;; sb) sb).
    by rewrite crE, seq_union_l, seq_id_l, SB, unionK. 

  eapply inclusion_t_ind_right;
    [rewrite IN at 1 | rewrite IN at 3];
  rewrite <- unionA, unionK, ?seq_union_l, ?seq_union_r; repeat apply inclusion_union_l; vauto.
  by right; repeat (eexists; try edone); vauto. 
  rewrite SB; eauto with rel.
  rewrite crE, !seq_union_r, seq_id_r; eauto 8 with rel.
  rewrite !seqA, SBR; eauto with rel.
  apply inclusion_union_r; right; apply inclusion_seq_mon.
    repeat eapply inclusion_seq_rt; eauto with rel.
    by unfold external; red; ins; desf; vauto.
  by eexists; vauto.
Qed.


(** This following theorem essentially proves the soundness of compilation to TSO: 
every TSO-coherent execution graph can be mapped to a PromiseFree-coherent execution graph.
We note that the condition [Cscu] of TSO coherence is not used in the proof. *)

Theorem CoherentTSO_implies_CoherentPF acts sb rmw rf mo :
  CoherentTSO acts sb rmw rf mo ->
  Coherent acts sb rmw rf (restr_eq_rel loc (restr_rel is_write mo))
           (restr_rel is_sc_fence mo).
Proof.
  unfold CoherentTSO, Coherent, Wf, WfTSO; ins; desc; unnw.
  clear Cscu.

  assert (INC: inclusion (rf ;; tc (sb +++ rf)) (tc (sb +++ rf))).
    by eauto using inclusion_seq_mon, inclusion_r_t_t with rel. 
  assert (INC2: inclusion (clos_refl rf ;; tc (sb +++ rf)) (tc (sb +++ rf))).
    by eauto using inclusion_seq_mon, inclusion_r_t_t with rel. 

  assert (TOT:  is_total (fun a => In a acts /\ is_sc_fence a) (restr_rel is_sc_fence mo)).
    by unfold restr_rel; red in WF_MO; desc; red; ins; desf; eapply MO_TOT in NEQ; desf; eauto.
  splits; try done.
{
  red in WF_MO; desc; red; splits; eauto using restr_eq_trans, restr_rel_trans;
  unfold restr_eq_rel, restr_rel; ins; desf; eauto.
  unfold loc in *; destruct a as [??[]]; simpls; destruct b as [??[]]; simpls; vauto. 
  red; ins; desf; eauto.
  red; ins; desf; eapply MO_TOT in NEQ; desf; eauto; [left|right]; splits; eauto; congruence.
}
{
  red in WF_MO; desc; red; splits; eauto using restr_eq_trans, restr_rel_trans;
  unfold restr_eq_rel, restr_rel; ins; desf; eauto.
  red; ins; desf; eauto.
}

  all: red. 
  by rewrite hb_in_sb_rf, inclusion_restr_eq, inclusion_restr, INC; try done.
  by rewrite hb_in_sb_rf, inclusion_restr_eq, inclusion_restr; try done.
  by rewrite <- seqA, irreflexive_seqC, <- seqA, hb_in_sb_rf.
  
  by rewrite inclusion_seq_eqv_l, hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, INC, <- seqA. 
  by rewrite inclusion_seq_eqv_l, hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, INC, <- seqA. 
  by rewrite inclusion_seq_eqv_l, !hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, ct_ct, INC, <- seqA.

{
  rewrite hb_in_sb_rf, <- (seqA (clos_refl rf)), INC2, <- !seqA, irreflexive_seqC, !seqA; try done.
  intros a (b & B & c & C & d & D & e & E & A). 
  assert (MO: mo c d). {
    red in WF_MO; desc. 
    assert (NEQ: c <> d) by (intro; desf; eauto). 
    eapply MO_TOT in NEQ; desf; eauto.
        by edestruct Cww; vauto.
      by unfold restr_eq_rel, restr_rel in C; desc; eauto.
    by unfold restr_eq_rel, restr_rel in E; desc; eauto.
  }
  clear D; red in B; desf.
    apply inclusion_restr_eq, inclusion_restr in C; apply inclusion_restr in E.
    by eapply (Cww b); exists e; split; eauto; do 2 (eapply WF_MO; eauto).
  eapply sb_rf_to_ext_end in A; eauto; red in A; desf.
    eapply (Cscf a); exists c; split; vauto; exists e; split; vauto. 
      by eapply WF_MO; eauto; eapply E.
    by eexists e; split; vauto; split; ins; eapply E. 
  destruct A as (f & F & g & G & [A|A]); subst.
    red in WF_RF; red in G; desc. 
    assert (f = b) by (eapply RF_FUN; eauto); subst.
    assert (mo b e).
      apply inclusion_restr_eq, inclusion_restr in C; apply inclusion_restr in E.
      do 2 (eapply WF_MO; eauto).
    by eapply clos_refl_transE in F; desf; [eapply WF_MO | apply (Cww b); exists e]; eauto.
  eapply (Crfe a); exists c; split; vauto; eexists f; split; vauto.
  red in E; desf; eapply WF_MO; eauto.
  eapply clos_refl_transE in F; desf; eapply WF_MO; eauto.
  red in WF_MO; desc. 
  assert (NEQ: e <> f) by (intro; desf; eauto). 
  red in G; desc.
  eapply MO_TOT in NEQ; desf; eauto.
    by edestruct Cww; vauto.
  by red in WF_RF; desc; eauto.
}

 red in WF_MO; desc.
 eapply acyclic_decomp_u_total; eauto. 
   by unfold restr_rel; ins; desf; eauto 8. 
   by rewrite inclusion_restr, ct_of_trans, irreflexive_seqC, crtE, 
      seq_union_r, seq_id_r, irreflexive_union.
Qed.

