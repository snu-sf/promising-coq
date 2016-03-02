Require Import sflib.

Require Import Event.
Require Import Memory.
Require Import Configuration.
Require Import Program.

Set Implicit Arguments.

Inductive tausteps: forall (src:Configuration.t) (src':Configuration.t), Prop :=
| tausteps_nil
    src:
    tausteps src src
| tausteps_cons
    src src' src''
    (STEP: Configuration.step src None src')
    (STEPS: tausteps src' src''):
    tausteps src src''
.

(* TODO: liveness *)
Module Simulation.
  Section Simulation.
    Variable (prog_src prog_tgt:Program.syntax).
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
        (FEASIBLE: InceptionSet.Empty tgt.(Configuration.memory).(Memory.inceptions)),
        Configuration.feasible src.

    Definition BASE_STEP: Prop :=
      forall src0 tgt0 tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.base_step tgt0 tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition INCEPTION_STEP: Prop :=
      forall src0 src1
        c0_tgt th0_tgt m0_tgt
        c1_tgt th1_tgt m1_tgt
        inception
        (STEPS_TGT: Configuration.internal_steps (Configuration.mk c0_tgt th0_tgt m0_tgt) (Configuration.mk c1_tgt th1_tgt m1_tgt))
        (INCEPTION: Memory.inception m0_tgt m1_tgt inception)
        (SIM0: sim src0 (Configuration.mk c0_tgt th0_tgt m0_tgt))
        (STEPS_SRC: Configuration.internal_steps src0 src1)
        (SIM1: sim src1 (Configuration.mk c1_tgt th1_tgt m1_tgt)),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 (Configuration.mk c0_tgt th0_tgt (Memory.mk m0_tgt.(Memory.buffers) (InceptionSet.add inception m0_tgt.(Memory.inceptions))))>>.

    Definition EXTERNAL_STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.external_step tgt0 e tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.external_step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Lemma internal_step (B:BASE_STEP) (I:INCEPTION_STEP):
      forall src0 tgt0 tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_step tgt0 tgt2),
      exists src1 src2,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>
    with internal_steps (B:BASE_STEP) (I:INCEPTION_STEP):
      forall src0 tgt0 tgt1
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_steps tgt0 tgt1),
      exists src1,
        <<INTERNAL: Configuration.internal_steps src0 src1>> /\
        <<SIM: sim src1 tgt1>>.
    Proof.
      - i. inv STEP0.
        + exploit B; eauto.
        + exploit internal_steps; eauto. i. des.
          exploit I; eauto.
      - i. revert src0 SIM. induction STEP0.
        + i. exists src0. splits; eauto. econs.
        + i. exploit internal_step; eauto. i. des.
          exploit IHSTEP0; eauto. i. des.
          exists src3. splits; auto.
          eapply Configuration.internal_steps_append; eauto.
          eapply Configuration.internal_steps_append; eauto.
          econs; eauto. econs.
    Qed.

    Lemma feasible_lemma (F:FEASIBLE) (B:BASE_STEP) (I:INCEPTION_STEP)
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

    Lemma step_lemma (F:FEASIBLE) (B:BASE_STEP) (I:INCEPTION_STEP) (E:EXTERNAL_STEP): STEP.
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

  Structure t (prog_src prog_tgt:Program.syntax) := mk {
    sim: forall (src tgt:Configuration.t), Prop;

    init: INIT prog_src prog_tgt sim;
    step: STEP sim;
    terminal: TERMINAL sim;
  }.
End Simulation.
