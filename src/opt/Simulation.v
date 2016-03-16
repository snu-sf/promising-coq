Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* TODO: liveness *)
Module Simulation.
  Section Simulation.
    Variable (prog_src prog_tgt:Configuration.syntax).
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Definition INIT: Prop := sim (Configuration.init prog_src) (Configuration.init prog_tgt).

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

    Definition FEASIBLE: Prop :=
      forall src tgt
        (SIM: sim src tgt)
        (CONFIRM: ~ Messages.declared tgt.(Configuration.messages)),
        Configuration.feasible src.

    Definition BASE_STEP: Prop :=
      forall src0 tgt0 reading tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.base_step tgt0 reading tgt2)
        (VALIDATION:
           forall (READING: reading),
           exists src0' tgt0',
             <<SRC: Configuration.internal_steps src0 src0'>> /\
             <<TGT: Configuration.internal_steps tgt0 tgt0'>> /\
             <<CONFIRM: ~ Messages.declared tgt0'.(Configuration.messages)>> /\
             <<SIM: sim src0' tgt0'>>),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition EXTERNAL_STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.external_step tgt0 e tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.external_step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Lemma internal_step (B:BASE_STEP):
      forall src0 tgt0 tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_step tgt0 tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>
    with internal_steps (B:BASE_STEP):
      forall src0 tgt0 tgt1
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_steps tgt0 tgt1),
      exists src1,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<SIM: sim src1 tgt1>>.
    Proof.
      - i. inv STEP0; eapply B; eauto.
        + congruence.
        + exploit internal_steps; eauto. i. des.
          eexists _, _. splits; eauto.
      - i. revert src0 SIM. induction STEP0.
        + i. eexists. splits; eauto.
          econs 1.
        + i. exploit internal_step; eauto. i. des.
          exploit IHSTEP0; eauto. i. des.
          eexists. splits; [|eauto].
          eapply Configuration.internal_steps_append; eauto.
          econs 2; eauto.
    Qed.

    Lemma feasible_lemma (F:FEASIBLE) (B:BASE_STEP)
          src tgt
          (SIM: sim src tgt)
          (FEASIBLE: Configuration.feasible tgt):
      Configuration.feasible src.
    Proof.
      inv FEASIBLE. exploit internal_steps; eauto. i. des.
      exploit F; eauto. intro X. inv X.
      econs; [|eauto].
      eapply Configuration.internal_steps_append; eauto.
    Qed.

    Lemma step_lemma (F:FEASIBLE) (B:BASE_STEP) (E:EXTERNAL_STEP): STEP.
    Proof.
      ii. inv STEP0.
      - exploit internal_step; eauto. i. des.
        eexists _, _. splits; eauto.
        econs; eauto.
        eapply feasible_lemma; eauto.
      - exploit E; eauto. i. des.
        eexists _, _. splits; eauto.
        econs; eauto.
        eapply feasible_lemma; eauto.
    Qed.
  End Simulation.

  Structure t (prog_src prog_tgt:Configuration.syntax) := mk {
    sim: forall (src tgt:Configuration.t), Prop;
    init: INIT prog_src prog_tgt sim;
    step: STEP sim;
    terminal: TERMINAL sim;
  }.
End Simulation.
