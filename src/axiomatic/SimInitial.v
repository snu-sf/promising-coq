(******************************************************************************)
(** * Simulation between initial states  *)
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
Require Import TView.

Require Import Gevents.
Require Import model.
Require Import Machine.
Require Import SimRel.

Set Implicit Arguments.
Remove Hints plus_n_O.

Require Import Setoid Permutation.

Lemma coherent_initial G (INIT: initial_exec G) : 
  Coherent (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G).
Proof.
destruct INIT; red; splits; red; splits; try red; splits; ins; eauto.
all: try by specialize (ACTS a); tauto.
all: try by exfalso; specialize (SB a b); tauto.
all: try by exfalso; specialize (RMW a b); tauto.
all: try by exfalso; specialize (RF a b); tauto.
all: try by exfalso; specialize (RF a c); tauto.
all: try by exfalso; specialize (MO a b); tauto.
all: try by exfalso; specialize (SC a b); tauto.
by unfold init_pair in *; desc; eapply proper_non_init in INIT0; 
specialize (ACTS b); tauto.
by intro; ins; eapply SB; eauto.
by intro; ins; exfalso; eapply SB; eauto.
by exfalso; eapply proper_non_init in PROPERa; specialize (ACTS a); tauto.
{ apply read_non_write in READ.
  assert (is_init b -> is_write b).
  by eapply init_is_write.
  specialize (ACTS b).
  tauto. }
by intro; ins; eapply MO; eauto.
by intro; ins; exfalso; eapply MO; eauto.
{ intro; ins; desc.
  exfalso.
  apply NEQ.
  apply same_init.
  specialize (ACTS a); tauto.
  specialize (ACTS b); tauto.
  congruence. }
by intro; ins; eapply SC; eauto.
by intro; ins; exfalso; eapply SC; eauto.
{ intro; ins; desc.
  apply ACTS, init_not_sc in IWa.
  exfalso; eauto with acts. }
{ intros x H. apply t_step_rt in H; desc.
  unfold Relation_Operators.union in H; desf; exfalso.
  specialize (SB x z); tauto.
  specialize (RF x z); tauto.
  specialize (SC x z); tauto. }
Qed.

Lemma sim_initial_GM :
  forall s ax_st (INIT: initial ax_st s),
    GMsim (Configuration.init s) ax_st.
Proof.
ins.
destruct INIT.
assert (Coherent (acts (exec ax_st)) (sb (exec ax_st)) (rmw (exec ax_st)) 
  (rf (exec ax_st)) (mo (exec ax_st)) (sc (exec ax_st))).
by apply coherent_initial.
destruct EXEC; desc.
red; splits; try done.
- by apply Configuration.init_wf.
- by ins; apply find_mapD in TID; desf.
- rewrite STATES.
  unfold Configuration.init, Threads.init.
  ins; apply IdentMap.eq_leibniz; intro y.
  rewrite !IdentMap.Facts.map_o; ins.
  by unfold option_map; desf.
- eexists (fun x => Time.bot), (fun x => Time.bot).
  red; splits.
  * eby red; ins; exfalso; eapply MO.
  * ins.
    unfold Threads.init in *.
    apply find_mapD in TID; desf.
    unfold Local.init in *; ins.
    red; splits; red; splits; ins.
    all:rewrite tm_find_bot in *.
    all: unfold t_cur, t_acq, t_rel, dom_rel, c_cur, c_acq, c_rel, seq, eqv_rel in *; desc; subst.
    all: try by eapply max_value_empty; ins; intro X; desc;
      eapply init_not_rel; try edone; eapply ACTS, scr_actb; eauto.
    all: try by eapply max_value_empty; ins; intro X; desc;
      eapply init_not_rel; try edone; eapply ACTS, rwr_actb; eauto.
    all: try by eapply max_value_empty; ins; intro X; desc;
      eapply init_not_rel; try edone; eapply ACTS, urr_actb; eauto.
    all: unfold max_value; splits.
    all: try by ins; right.
    all: right.
    all: repeat (exists (init_event l); splits).
    all: try match goal with
         | [|- rwr _ _ _ _ _ _ _ _] => left     end.
    all: repeat (exists (init_event l); splits).
    all: try by econs.
    all: unfold eqv_rel; splits; eauto.
    all: try by apply ACTS; red; eauto.
    all: try by right; red; eauto.
  * ins; rewrite tm_find_bot in *.
    eapply max_value_empty; ins; intro X; desc.
    unfold S_tm, dom_rel, seq, eqv_rel in *; desc; subst.
    eapply init_not_sc, sc_wf_is_sc; try edone.
    eapply ACTS, S_tmr_actb; eauto.
    eby eapply sc_fence_is_sc_wf, S_tmr_domb.
  * red; splits; ins.
    apply UsualFMapPositive.UsualPositiveMap'.singleton_find_inv in CELL; desf.
    exists (init_event l); splits; eauto.
    by eapply ACTS; red; eauto.
    by eapply init_is_write; red; eauto.
    red; splits.
    by ins.
    by right; splits; try red; eauto.
    2: by exfalso; unfold seq in *; desc;
      eapply read_non_write; [eapply rf_domb | eapply init_is_write, ACTS, rf_actb]; eauto.
    red; splits; ins; rewrite tm_find_bot in *.
    all: eapply max_value_empty; ins; intro X; desc.
    all: unfold msg_rel, m_rel, rel, seq, eqv_rel  in *; desf.
    all: eapply init_not_rel; try edone; eapply ACTS.
    by eapply urr_actb; eauto.
    by eapply rwr_actb; eauto.
Qed.

Lemma sim_initial_MG :
  forall s ax_st (INIT: initial ax_st s),
    MGsim (Configuration.init s) ax_st.
  ins.
  exploit sim_initial_GM; eauto.
  unfold GMsim, MGsim in *.
  ins; desc; splits; eauto.
  eexists _,_; splits; eauto.
  - destruct INIT, EXEC.
  ins; exfalso; specialize (MO x y); tauto.
  - destruct INIT, EXEC.
  ins; exfalso; eapply proper_non_init; try edone.
  by apply ACTS. 
Qed.
