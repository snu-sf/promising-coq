Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* TODO: liveness *)
(* TODO: maybe `BASE_STEP` is too weak to prove some hand-optimizations. *)
Module Simulation.
  Section Simulation.
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Definition INIT (prog_src prog_tgt:Configuration.syntax): Prop :=
      sim (Configuration.init prog_src) (Configuration.init prog_tgt).

    Definition STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.step tgt0 e tgt2),
      exists src1 src2,
        <<INTERNAL: rtc Configuration.internal_step src0 src1>> /\
        <<STEP: Configuration.step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition TERMINAL: Prop :=
      forall src0 tgt0
        (SIM: sim src0 tgt0)
        (TERM: Configuration.is_terminal tgt0),
      exists src1,
        <<INTERNAL: rtc Configuration.internal_step src0 src1>> /\
        <<TERM: Configuration.is_terminal src1>>.
  End Simulation.

  Inductive t (prog_src prog_tgt:Configuration.syntax): Prop :=
  | t_intro
    sim
    (I: INIT sim prog_src prog_tgt)
    (S: STEP sim)
    (T: TERMINAL sim)
  .

  Section BaseSimulation.
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Definition CONSISTENT: Prop :=
      forall src tgt
        (SIM: sim src tgt)
        (CONFIRM: MessageSet.confirmed tgt.(Configuration.messages)),
        Configuration.consistent src.

    Definition BASE_STEP: Prop :=
      forall src0 tgt0 reading tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.base_step tgt0 reading tgt2)
        (READING:
           forall loc ts (READING: reading = Some (loc, ts)),
           exists (src0' tgt0':Configuration.t),
             <<SIM: sim src0' tgt0'>> /\
             <<SRC: rtc Configuration.internal_step src0 src0'>> /\
             <<TGT: rtc Configuration.internal_step tgt0 tgt0'>> /\
             <<DECLARE: MessageSet.declared tgt0'.(Configuration.messages) <2= MessageSet.declared tgt0.(Configuration.messages)>> /\
             <<NODECLARE: ~ MessageSet.declared tgt0'.(Configuration.messages) loc ts>>),
      exists src1 src2,
        <<INTERNAL: rtc Configuration.internal_step src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>.

    Definition EXTERNAL_STEP: Prop :=
      forall src0 tgt0 e tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.external_step tgt0 e tgt2),
      exists src1 src2,
        <<INTERNAL: rtc Configuration.internal_step src0 src1>> /\
        <<STEP: Configuration.external_step src1 e src2>> /\
        <<SIM: sim src2 tgt2>>.

    Lemma internal_step (B:BASE_STEP):
      forall src0 tgt0 tgt2
        (SIM: sim src0 tgt0)
        (STEP: Configuration.internal_step tgt0 tgt2),
      exists src1 src2,
        <<INTERNAL: rtc Configuration.internal_step src0 src1>> /\
        <<STEP: Configuration.internal_step src1 src2>> /\
        <<SIM: sim src2 tgt2>>.
    Proof.
      i. revert src0 SIM.
      induction STEP0 using Configuration.internal_step_strong_ind; i.
      - eapply B; eauto. congruence.
      - eapply B; eauto. i. inv READING.
        cut (exists src0', sim src0' c1' /\ rtc Configuration.internal_step src0 src0').
        { i. des. eexists _, _. splits; eauto. }
        revert src0 SIM. clear -PROP. induction PROP; i.
        + eexists. splits; eauto.
        + exploit H; eauto. i. des.
          exploit IHPROP; eauto. i. des.
          eexists. splits; eauto.
          eapply rtc_trans; eauto.
          econs 2; eauto.
    Qed.

    Lemma consistent (C:CONSISTENT) (B:BASE_STEP):
      forall src0 tgt0
        (SIM: sim src0 tgt0)
        (TGT0: Configuration.consistent tgt0),
        Configuration.consistent src0.
    Proof.
      i. inv TGT0. revert src0 SIM. induction STEPS; i.
      - eapply C; eauto.
      - exploit internal_step; eauto. i. des.
        exploit IHSTEPS; eauto. intro X. inv X.
        econs; [|eauto].
        eapply rtc_trans; eauto.
        econs 2; eauto.
    Qed.

    Lemma sim_lemma
          (prog_src prog_tgt:Configuration.syntax)
          (I:INIT sim prog_src prog_tgt)
          (C:CONSISTENT) (B:BASE_STEP) (E:EXTERNAL_STEP)
          (T:TERMINAL sim):
      Simulation.t prog_src prog_tgt.
    Proof.
      econs; eauto.
      ii. inv STEP0.
      - exploit internal_step; eauto. i. des.
        eexists _, _. splits; eauto.
        econs; auto.
        eapply consistent; eauto.
      - exploit E; eauto. i. des.
        eexists _, _. splits; eauto.
        econs; auto.
        eapply consistent; eauto.
    Qed.
  End BaseSimulation.
End Simulation.
