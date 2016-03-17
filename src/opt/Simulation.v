Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* TODO: liveness *)
Module Simulation.
  Section Simulation.
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Definition INIT (prog_src prog_tgt:Configuration.syntax): Prop :=
      sim (Configuration.init prog_src) (Configuration.init prog_tgt).

    (* TODO: too weak a step lemma *)
    Definition STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.step tgt0 e tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition TERMINAL: Prop :=
      forall src0 tgt0
        (SIM: sim src0 tgt0)
        (TERM: Configuration.is_terminal tgt0),
      exists src1,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<TERM: Configuration.is_terminal src1>>.
  End Simulation.

  Structure t (prog_src prog_tgt:Configuration.syntax): Prop := mk {
    sim: forall (src tgt:Configuration.t), Prop;
    init: INIT sim prog_src prog_tgt;
    step: STEP sim;
    terminal: TERMINAL sim;
  }.

  Section BaseSimulation.
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Inductive sim_lift (src tgt:Configuration.t): Prop :=
    | sim_lift_intro
        (SIM: sim src tgt)
        (SRC: Configuration.feasible src)
        (TGT: Configuration.feasible tgt)
    .

    Definition FEASIBLE: Prop :=
      forall src tgt
        (SIM: sim src tgt)
        (CONFIRM: ~ Messages.declared tgt.(Configuration.messages)),
        Configuration.feasible src.

    Definition BASE_STEP: Prop :=
      forall src0 tgt0 confirmed tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.base_step tgt0 confirmed tgt2)
        (SRC0: ~ confirmed -> Configuration.feasible src0)
        (TGT0: Configuration.feasible tgt0)
        (TGT2: Configuration.feasible tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition EXTERNAL_STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.external_step tgt0 e tgt2)
        (SRC0: Configuration.feasible src0)
        (TGT0: Configuration.feasible tgt0)
        (TGT2: Configuration.feasible tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.external_step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Lemma internal_step (F:FEASIBLE) (B:BASE_STEP):
      forall src0 tgt0 tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_step tgt0 tgt2)
        (TGT2: Configuration.feasible tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>
    with feasible (F:FEASIBLE) (B:BASE_STEP):
      forall src0 tgt0
        (SIM: sim src0 tgt0)
        (TGT0: Configuration.feasible tgt0),
        Configuration.feasible src0.
    Proof.
      - i. inv STEP0; eapply B; eauto.
        eapply Configuration.internal_steps_feasible; eauto.
        econs 2; eauto.
        + econs 1. eauto.
        + econs 1.
      - i. inv TGT0. revert src0 SIM CONFIRM. induction STEPS.
        + i. eapply F; eauto.
        + i. exploit internal_step; eauto.
          { econs; eauto. }
          i. des.
          exploit IHSTEPS; eauto. i. des.
          eapply Configuration.internal_steps_feasible; eauto.
          eapply Configuration.internal_steps_feasible; eauto.
          econs 2; eauto. econs 1.
    Qed.

    Lemma step_lemma (F:FEASIBLE) (B:BASE_STEP) (E:EXTERNAL_STEP): STEP (sim_lift).
    Proof.
      ii. inv SIM. inv STEP0.
      - exploit internal_step; eauto. i. des.
        exploit feasible; eauto. intro SRC2.
        eexists _, _. splits; eauto.
        + econs; eauto.
        + econs; eauto.
      - exploit E; eauto. i. des.
        exploit feasible; eauto. intro SRC2.
        eexists _, _. splits; eauto.
        + econs; eauto.
        + econs; eauto.
    Qed.

    Lemma sim_lemma
          (prog_src prog_tgt:Configuration.syntax)
          (I:INIT sim prog_src prog_tgt)
          (F:FEASIBLE) (B:BASE_STEP) (E:EXTERNAL_STEP)
          (T:TERMINAL sim):
      Simulation.t prog_src prog_tgt.
    Proof.
      econs; try apply step_lemma; auto.
      - econs; auto.
        + apply Configuration.init_feasible.
        + apply Configuration.init_feasible.
      - ii. inv SIM. exploit T; eauto.
    Qed.
  End BaseSimulation.
End Simulation.
