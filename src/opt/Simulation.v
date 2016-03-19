Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* TODO: liveness *)
(* TODO: maybe `BASE_STEP` is too weak to prove some hand-optimizations. *)
Module Simulation.
  Section Simulation.
    Variable (sim: forall (idx:nat) (src tgt:Configuration.t), Prop).

    Definition INIT (prog_src prog_tgt:Configuration.syntax): Prop :=
      exists idx,
        sim idx (Configuration.init prog_src) (Configuration.init prog_tgt).

    Inductive internal_step (conf0:Configuration.t) (idx0:nat) (conf1:Configuration.t) (idx1:nat): Prop :=
    | internal_step_step
        (CONF: Configuration.internal_step conf0 conf1)
    | internal_step_stop
        (CONF: conf0 = conf1)
        (IDX: idx0 > idx1)
    .

    Inductive step (conf0:Configuration.t) (idx0:nat): forall (e:option Event.t) (conf1:Configuration.t) (idx1:nat), Prop :=
    | step_internal
        conf1 idx1
        (STEP: internal_step conf0 idx0 conf1 idx1):
        step conf0 idx0 None conf1 idx1
    | step_external
        e conf1 idx1
        (STEP: Configuration.external_step conf0 e conf1):
        step conf0 idx0 (Some e) conf1 idx1
    .

    Definition STEP: Prop :=
      forall idx0 src0 tgt0 e tgt2
        (SIM: sim idx0 src0 tgt0)
        (STEP: Configuration.step tgt0 e tgt2),
      exists idx2 src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: step src1 idx0 e src2 idx2>> /\
        <<SIM: sim idx2 src2 tgt2>>.

    Definition TERMINAL: Prop :=
      forall idx0 src0 tgt0
        (SIM: sim idx0 src0 tgt0)
        (TERM: Configuration.is_terminal tgt0),
      exists src1,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<TERM: Configuration.is_terminal src1>>.
  End Simulation.

  Structure t (prog_src prog_tgt:Configuration.syntax): Prop := mk {
    sim: forall (idx:nat) (src tgt:Configuration.t), Prop;
    init: INIT sim prog_src prog_tgt;
    step: STEP sim;
    terminal: TERMINAL sim;
  }.

  Section BaseSimulation.
    Variable (sim: forall (idx:nat) (src tgt:Configuration.t), Prop).

    Inductive sim_lift (idx:nat) (src tgt:Configuration.t): Prop :=
    | sim_lift_intro
        (SIM: sim idx src tgt)
        (SRC: Configuration.consistent src)
        (TGT: Configuration.consistent tgt)
    .

    Definition CONSISTENT: Prop :=
      forall idx src tgt
        (SIM: sim idx src tgt)
        (CONFIRM: ~ Messages.declared tgt.(Configuration.messages)),
        Configuration.consistent src.

    Definition BASE_STEP: Prop :=
      forall idx0 src0 tgt0 confirmed tgt2
        (SIM: sim idx0 src0 tgt0)
        (STEP: Configuration.base_step tgt0 confirmed tgt2)
        (SRC0: ~ confirmed -> Configuration.consistent src0)
        (TGT0: Configuration.consistent tgt0)
        (TGT2: Configuration.consistent tgt2),
      exists idx2 src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: internal_step src1 idx0 src2 idx2>> /\
        <<SIM: sim idx2 src2 tgt2>>.

    Definition EXTERNAL_STEP: Prop :=
      forall idx0 src0 tgt0 e tgt2
        (SIM: sim idx0 src0 tgt0)
        (STEP: Configuration.external_step tgt0 e tgt2)
        (SRC0: Configuration.consistent src0)
        (TGT0: Configuration.consistent tgt0)
        (TGT2: Configuration.consistent tgt2),
      exists idx2 src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.external_step src1 e src2>> /\
        <<SIM: sim idx2 src2 tgt2>>.

    Lemma I (C:CONSISTENT) (B:BASE_STEP):
      forall idx0 src0 tgt0 tgt2
        (SIM: sim idx0 src0 tgt0)
        (STEP: Configuration.internal_step tgt0 tgt2)
        (TGT2: Configuration.consistent tgt2),
      exists idx2 src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: internal_step src1 idx0 src2 idx2>> /\
        <<SIM: sim idx2 src2 tgt2>>
    with F' (C:CONSISTENT) (B:BASE_STEP):
      forall idx0 src0 tgt0
        (SIM: sim idx0 src0 tgt0)
        (TGT0: Configuration.consistent tgt0),
        Configuration.consistent src0.
    Proof.
      - i. inv STEP0; eapply B; eauto.
        eapply Configuration.internal_steps_consistent; eauto.
        econs 2; eauto.
        + econs 1. eauto.
        + econs 1.
      - i. inv TGT0. revert idx0 src0 SIM CONFIRM. induction STEPS.
        + i. eapply C; eauto.
        + i. exploit I; eauto.
          { econs; eauto. }
          i. des.
          eapply Configuration.internal_steps_consistent; eauto.
          exploit IHSTEPS; eauto. intro SRC0.
          inv STEP1; auto.
          eapply Configuration.internal_steps_consistent; eauto.
          econs 2; eauto. econs 1.
    Qed.

    Lemma step_lemma (C:CONSISTENT) (B:BASE_STEP) (E:EXTERNAL_STEP): STEP (sim_lift).
    Proof.
      ii. inv SIM. inv STEP0.
      - exploit I; eauto. i. des.
        exploit F'; eauto. intro SRC2.
        eexists _, _, _. splits; eauto.
        + econs 1. eauto.
        + econs; eauto.
      - exploit E; eauto. i. des.
        exploit F'; eauto. intro SRC2.
        eexists _, _, _. splits; eauto.
        + econs; eauto.
        + econs; eauto.
    Qed.

    Lemma sim_lemma
          (prog_src prog_tgt:Configuration.syntax)
          (I:INIT sim prog_src prog_tgt)
          (C:CONSISTENT) (B:BASE_STEP) (E:EXTERNAL_STEP)
          (T:TERMINAL sim):
      Simulation.t prog_src prog_tgt.
    Proof.
      econs; try apply step_lemma; auto.
      - unfold INIT in *. des.
        eexists. econs; eauto.
        + apply Configuration.init_consistent.
        + apply Configuration.init_consistent.
      - ii. inv SIM. exploit T; eauto.
    Qed.
  End BaseSimulation.
End Simulation.
