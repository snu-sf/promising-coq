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

Lemma sim_initial :
  forall s ax_st (INIT: initial ax_st s),
    GMsim (Configuration.init s) ax_st.
Proof.
ins.
destruct INIT.
red; splits.
- by apply coherent_initial.
- apply Configuration.init_wf.
- ins. unfold Threads.init in *.
  apply find_mapD in TID; desc.
  desf.
- admit.
- eexists _,_.
red; splits.
* red; ins; exfalso.
destruct EXEC; desc.
eapply MO; edone.
* ins.
unfold Threads.init in *.
  apply find_mapD in TID; desf.
unfold Local.init in *; ins.
red; splits; red; splits; ins.
all: eapply max_value_empty.
all: ins; intro H.
all: unfold t_cur, t_acq, t_rel, dom_rel, c_cur, c_acq, c_rel, seq, eqv_rel in *; desc.
(* + 
eapply urr_actb in H; eauto using coherent_initial.

destruct EXEC.
apply ACTS in H.
red in H.
unfold init_event in *.
desc; destruct y as [??[]]; ins; desf.
+ 
red in H.
red in H.
desc.
red in H.
 *)
(* 
unfold  *)
all: admit.
Admitted.
