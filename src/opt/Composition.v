Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import Simulation.

Set Implicit Arguments.

Section Compose.
  Variable (ths1 ths2:Threads.t).
  Hypothesis (DISJOINT: Threads.disjoint ths1 ths2).

  Lemma compose_comm:
    Threads.compose ths1 ths2 = Threads.compose ths2 ths1.
  Proof.
    apply IdentMap.eq_leibniz. ii.
    rewrite ? Threads.compose_spec.
    unfold Threads.compose_option.
    destruct (IdentMap.find y ths1) eqn:SRC,
             (IdentMap.find y ths2) eqn:TGT; auto.
    exfalso. inv DISJOINT. eapply THREAD; eauto.
  Qed.

  Lemma compose_forall P:
    (forall tid lang st th (TH: IdentMap.find tid (Threads.compose ths1 ths2) = Some (existT _ lang st, th)),
        (P tid lang st th):Prop) <->
    (forall tid lang st th (TH: IdentMap.find tid ths1 = Some (existT _ lang st, th)),
        (P tid lang st th):Prop) /\
    (forall tid lang st th (TH: IdentMap.find tid ths2 = Some (existT _ lang st, th)),
        (P tid lang st th):Prop).
  Proof.
    econs; i.
    - i. splits.
      + i. eapply H; eauto.
        rewrite Threads.compose_spec. rewrite TH. ss.
      + i. eapply H; eauto.
        rewrite compose_comm.
        rewrite Threads.compose_spec. rewrite TH. ss.
    - des.
      rewrite Threads.compose_spec in TH.
      unfold Threads.compose_option in TH.
      destruct (IdentMap.find tid ths1) eqn:SRC; inv TH.
      + eapply H; eauto.
      + eapply H0; eauto.
  Qed.

  Lemma compose_forall_rev P:
    (forall tid lang st th (TH: IdentMap.find tid ths1 = Some (existT _ lang st, th)),
        (P tid lang st th):Prop) ->
    (forall tid lang st th (TH: IdentMap.find tid ths2 = Some (existT _ lang st, th)),
        (P tid lang st th):Prop) ->
    (forall tid lang st th (TH: IdentMap.find tid (Threads.compose ths1 ths2) = Some (existT _ lang st, th)),
        (P tid lang st th):Prop).
  Proof.
    i. apply compose_forall; auto.
  Qed.

  Lemma compose_is_terminal:
    Threads.is_terminal (Threads.compose ths1 ths2) <->
    Threads.is_terminal ths1 /\ Threads.is_terminal ths2.
  Proof.
    apply compose_forall.
  Qed.

  Lemma compose_threads_wf mem:
    Threads.wf (Threads.compose ths1 ths2) mem <->
    <<CONSISTENT1: Threads.wf ths1 mem>> /\
    <<CONSISTENT2: Threads.wf ths2 mem>>.
  Proof.
    econs; intro X; des; splits; ii.
    - econs; ss.
      + i. eapply X; eauto.
        * rewrite Threads.compose_spec.
          unfold Threads.compose_option.
          rewrite TH1. auto.
        * rewrite Threads.compose_spec.
          unfold Threads.compose_option.
          rewrite TH2. auto.
      + i. eapply X.
        rewrite Threads.compose_spec.
        unfold Threads.compose_option.
        rewrite TH. auto.
    - econs; ss.
      + i. eapply X; eauto.
        * rewrite compose_comm.
          rewrite Threads.compose_spec.
          unfold Threads.compose_option.
          rewrite TH1. auto.
        * rewrite compose_comm.
          rewrite Threads.compose_spec.
          unfold Threads.compose_option.
          rewrite TH2. auto.
      + i. eapply X.
        rewrite compose_comm.
        rewrite Threads.compose_spec.
        unfold Threads.compose_option.
        rewrite TH. auto.
    - inv CONSISTENT1. inv CONSISTENT2. econs; ss.
      + i. rewrite ? Threads.compose_spec in *.
        destruct (IdentMap.find tid1 ths1) eqn:TH11,
                 (IdentMap.find tid1 ths2) eqn:TH12,
                 (IdentMap.find tid2 ths1) eqn:TH21,
                 (IdentMap.find tid2 ths2) eqn:TH22;
          Configuration.simplify;
          try (by eapply DISJOINT; eauto);
          try (by eapply DISJOINT0; eauto);
          try (by eapply DISJOINT1; eauto).
        * symmetry. eapply DISJOINT; eauto.
        * symmetry. eapply DISJOINT; eauto.
      + i. rewrite ? Threads.compose_spec in *.
        unfold Threads.compose_option in *.
        destruct (IdentMap.find tid ths1) eqn:TH1.
        * inv TH. eapply THREADS. eauto.
        * eapply THREADS0. eauto.
  Qed.

  Lemma compose_threads_consistent sc mem:
    Threads.consistent (Threads.compose ths1 ths2) sc mem <->
    <<CONSISTENT1: Threads.consistent ths1 sc mem>> /\
    <<CONSISTENT2: Threads.consistent ths2 sc mem>>.
  Proof.
    econs; intro X; des; splits; ii.
    - eapply X; eauto.
      rewrite Threads.compose_spec.
      unfold Threads.compose_option.
      rewrite TH. auto.
    - eapply X; eauto.
      rewrite compose_comm.
      rewrite Threads.compose_spec.
      unfold Threads.compose_option.
      rewrite TH. auto.
    - rewrite ? Threads.compose_spec in *.
      destruct (IdentMap.find tid ths1) eqn:TH11,
               (IdentMap.find tid ths2) eqn:TH12,
               (IdentMap.find tid ths1) eqn:TH21,
               (IdentMap.find tid ths2) eqn:TH22;
        Configuration.simplify.
      + exfalso. inv DISJOINT. eapply THREAD; eauto.
      + eapply CONSISTENT1; eauto.
      + eapply CONSISTENT2; eauto.
  Qed.

  Lemma compose_wf sc mem:
    Configuration.wf (Configuration.mk (Threads.compose ths1 ths2) sc mem) <->
    <<WF1: Configuration.wf (Configuration.mk ths1 sc mem)>> /\
    <<WF2: Configuration.wf (Configuration.mk ths2 sc mem)>>.
  Proof.
    econs; intro X.
    - inv X. splits; econs; ss.
      + apply compose_threads_wf; auto.
      + apply compose_threads_wf; auto.
    - des. inv WF1. inv WF2. econs; ss.
      apply compose_threads_wf. auto.
  Qed.

  Lemma compose_consistent sc mem:
    Configuration.consistent (Configuration.mk (Threads.compose ths1 ths2) sc mem) <->
    <<CONSISTENT1: Configuration.consistent (Configuration.mk ths1 sc mem)>> /\
    <<CONSISTENT2: Configuration.consistent (Configuration.mk ths2 sc mem)>>.
  Proof.
    econs; intro X.
    - splits; apply compose_threads_consistent; auto.
    - apply compose_threads_consistent. auto.
  Qed.
End Compose.

Lemma compose_step
      ths1 ths2
      e tid sc mem ths' sc' mem'
      (DISJOINT: Threads.disjoint ths1 ths2)
      (STEP: Configuration.step
               e tid
               (Configuration.mk (Threads.compose ths1 ths2) sc mem)
               (Configuration.mk ths' sc' mem')):
  (exists ths1',
      <<NEXT: ths' = Threads.compose ths1' ths2>> /\
      <<STEP: Configuration.step
                e tid
                (Configuration.mk ths1 sc mem)
                (Configuration.mk ths1' sc' mem')>>) \/
  (exists ths2',
      <<NEXT: ths' = Threads.compose ths1 ths2'>> /\
      <<STEP: Configuration.step
                e tid
                (Configuration.mk ths2 sc mem)
                (Configuration.mk ths2' sc' mem')>>).
Proof.
  inv STEP. ss.
  rewrite Threads.compose_spec in TID.
  unfold Threads.compose_option in TID.
  destruct (IdentMap.find tid ths1) eqn:TH1,
           (IdentMap.find tid ths2) eqn:TH2; inv TID.
  - exfalso. inv DISJOINT. eapply THREAD; eauto.
  - left. exists (IdentMap.add tid (existT _ lang st3, lc3) ths1). splits; [|econs; eauto].
    apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    condtac; auto.
  - right. exists (IdentMap.add tid (existT _ lang st3, lc3) ths2). splits; [|econs; eauto].
    apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    condtac; auto.
    subst. unfold Threads.compose_option. rewrite TH1. auto.
Qed.

Lemma compose_step1
      ths1 ths2
      e tid sc mem ths1' sc' mem'
      (STEP: Configuration.step
               e tid
               (Configuration.mk ths1 sc mem)
               (Configuration.mk ths1' sc' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (WF1: Configuration.wf (Configuration.mk ths1 sc mem))
      (WF2: Configuration.wf (Configuration.mk ths2 sc mem))
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 sc mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 sc mem)):
  <<STEP: Configuration.step
            e tid
            (Configuration.mk (Threads.compose ths1 ths2) sc mem)
            (Configuration.mk (Threads.compose ths1' ths2) sc' mem')>> /\
  <<DISJOINT': Threads.disjoint ths1' ths2>> /\
  <<WF2': Configuration.wf (Configuration.mk ths2 sc' mem')>> /\
  <<CONSISTENT2': Configuration.consistent (Configuration.mk ths2 sc' mem')>>.
Proof.
  exploit Configuration.step_disjoint; eauto. s. i. des.
  splits; eauto. inv STEP. ss.
  replace (Threads.compose (IdentMap.add tid (existT _ lang st3, lc3) ths1) ths2)
  with (IdentMap.add tid (existT _ lang st3, lc3) (Threads.compose ths1 ths2)).
  - econs; eauto.
    s. rewrite Threads.compose_spec. unfold Threads.compose_option.
    rewrite TID. auto.
  - apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    condtac; auto.
Qed.

Lemma compose_step2
      ths1 ths2
      e tid sc mem ths2' sc' mem'
      (STEP: Configuration.step
               e tid
               (Configuration.mk ths2 sc mem)
               (Configuration.mk ths2' sc' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (WF1: Configuration.wf (Configuration.mk ths1 sc mem))
      (WF2: Configuration.wf (Configuration.mk ths2 sc mem))
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 sc mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 sc mem)):
  <<STEP: Configuration.step
            e tid
            (Configuration.mk (Threads.compose ths1 ths2) sc mem)
            (Configuration.mk (Threads.compose ths1 ths2') sc' mem')>> /\
  <<DISJOINT': Threads.disjoint ths1 ths2'>> /\
  <<WF1': Configuration.wf (Configuration.mk ths1 sc' mem')>> /\
  <<CONSISTENT1': Configuration.consistent (Configuration.mk ths1 sc' mem')>>.
Proof.
  exploit Configuration.step_disjoint; try symmetry; eauto. s. i. des.
  exploit compose_step1; try apply STEP; try apply CONSISTENT1; eauto.
  { symmetry. auto. }
  i. des. splits; eauto.
  - rewrite (@compose_comm ths1 ths2); auto.
    rewrite (@compose_comm ths1 ths2'); auto.
    symmetry. auto.
  - symmetry. auto.
Qed.

Lemma compose_opt_step1
      ths1 ths2
      e tid sc mem ths1' sc' mem'
      (STEP: Configuration.opt_step
               e tid
               (Configuration.mk ths1 sc mem)
               (Configuration.mk ths1' sc' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (WF1: Configuration.wf (Configuration.mk ths1 sc mem))
      (WF2: Configuration.wf (Configuration.mk ths2 sc mem))
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 sc mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 sc mem)):
  <<STEP: Configuration.opt_step
            e tid
            (Configuration.mk (Threads.compose ths1 ths2) sc mem)
            (Configuration.mk (Threads.compose ths1' ths2) sc' mem')>> /\
  <<DISJOINT': Threads.disjoint ths1' ths2>> /\
  <<WF2': Configuration.wf (Configuration.mk ths2 sc' mem')>> /\
  <<CONSISTENT2': Configuration.consistent (Configuration.mk ths2 sc' mem')>>.
Proof.
  inv STEP.
  - splits; eauto. econs 1.
  - exploit compose_step1; eauto. i. des. splits; eauto. econs 2. auto.
Qed.

Lemma compose_opt_step2
      ths1 ths2
      e tid sc mem ths2' sc' mem'
      (STEP: Configuration.opt_step
               e tid
               (Configuration.mk ths2 sc mem)
               (Configuration.mk ths2' sc' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (WF1: Configuration.wf (Configuration.mk ths1 sc mem))
      (WF2: Configuration.wf (Configuration.mk ths2 sc mem))
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 sc mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 sc mem)):
  <<STEP: Configuration.opt_step
            e tid
            (Configuration.mk (Threads.compose ths1 ths2) sc mem)
            (Configuration.mk (Threads.compose ths1 ths2') sc' mem')>> /\
  <<DISJOINT': Threads.disjoint ths1 ths2'>> /\
  <<WF1': Configuration.wf (Configuration.mk ths1 sc' mem')>> /\
  <<CONSISTENT1': Configuration.consistent (Configuration.mk ths1 sc' mem')>>.
Proof.
  inv STEP.
  - splits; eauto. econs 1.
  - exploit compose_step2; eauto. i. des. splits; eauto. econs 2. auto.
Qed.

Lemma compose_rtc_step1
      c1 c2 ths
      (STEPS: rtc Configuration.tau_step c1 c2)
      (DISJOINT: Threads.disjoint c1.(Configuration.threads) ths)
      (WF1: Configuration.wf c1)
      (WF: Configuration.wf (Configuration.mk ths c1.(Configuration.sc) c1.(Configuration.memory)))
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT: Configuration.consistent (Configuration.mk ths c1.(Configuration.sc) c1.(Configuration.memory))):
  <<STEPS: rtc Configuration.tau_step
               (Configuration.mk (Threads.compose c1.(Configuration.threads) ths) c1.(Configuration.sc) c1.(Configuration.memory))
               (Configuration.mk (Threads.compose c2.(Configuration.threads) ths) c2.(Configuration.sc) c2.(Configuration.memory))>> /\
  <<DISJOINT': Threads.disjoint c2.(Configuration.threads) ths>> /\
  <<WF': Configuration.wf (Configuration.mk ths c2.(Configuration.sc) c2.(Configuration.memory))>> /\
  <<CONSISTENT': Configuration.consistent (Configuration.mk ths c2.(Configuration.sc) c2.(Configuration.memory))>>.
Proof.
  revert CONSISTENT1 CONSISTENT. induction STEPS; auto. i. inv H.
  exploit Configuration.step_future; eauto. i. des.
  exploit Configuration.step_disjoint; eauto. i. des.
  destruct x, y. exploit compose_step1; eauto. s. i. des.
  exploit IHSTEPS; eauto. s. i. des.
  splits; eauto.
  econs; eauto. econs. eauto.
Qed.

Lemma compose_rtc_step2
      c1 c2 ths
      (STEPS: rtc Configuration.tau_step c1 c2)
      (DISJOINT: Threads.disjoint ths c1.(Configuration.threads))
      (WF1: Configuration.wf c1)
      (WF: Configuration.wf (Configuration.mk ths c1.(Configuration.sc) c1.(Configuration.memory)))
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT: Configuration.consistent (Configuration.mk ths c1.(Configuration.sc) c1.(Configuration.memory))):
  <<STEPS: rtc Configuration.tau_step
               (Configuration.mk (Threads.compose ths c1.(Configuration.threads)) c1.(Configuration.sc) c1.(Configuration.memory))
               (Configuration.mk (Threads.compose ths c2.(Configuration.threads)) c2.(Configuration.sc) c2.(Configuration.memory))>> /\
  <<DISJOINT': Threads.disjoint ths c2.(Configuration.threads)>> /\
  <<WF': Configuration.wf (Configuration.mk ths c2.(Configuration.sc) c2.(Configuration.memory))>> /\
  <<CONSISTENT': Configuration.consistent (Configuration.mk ths c2.(Configuration.sc) c2.(Configuration.memory))>>.
Proof.
  revert CONSISTENT1 CONSISTENT. induction STEPS; auto. i. inv H.
  exploit Configuration.step_future; eauto. i. des.
  exploit Configuration.step_disjoint; try symmetry; eauto. i. des.
  destruct x, y. exploit compose_step2; eauto. s. i. des.
  exploit IHSTEPS; try symmetry; eauto. s. i. des.
  splits; eauto.
  econs; eauto. econs. eauto.
Qed.


Lemma sim_compose
      ths1_src ths2_src sc0_src mem0_src
      ths1_tgt ths2_tgt sc0_tgt mem0_tgt
      (DISJOINT_SRC: Threads.disjoint ths1_src ths2_src)
      (DISJOINT_TGT: Threads.disjoint ths1_tgt ths2_tgt)
      (SIM1: sim ths1_src sc0_src mem0_src ths1_tgt sc0_tgt mem0_tgt)
      (SIM2: sim ths2_src sc0_src mem0_src ths2_tgt sc0_tgt mem0_tgt):
  sim (Threads.compose ths1_src ths2_src) sc0_src mem0_src
      (Threads.compose ths1_tgt ths2_tgt) sc0_tgt mem0_tgt.
Proof.
  revert
    ths1_src ths2_src sc0_src mem0_src
    ths1_tgt ths2_tgt sc0_tgt mem0_tgt
    DISJOINT_SRC DISJOINT_TGT
    SIM1 SIM2.
  pcofix CIH. i. pfold. ii.
  apply compose_wf in WF_SRC; auto.
  apply compose_wf in WF_TGT; auto.
  apply compose_consistent in CONSISTENT_SRC; auto.
  apply compose_consistent in CONSISTENT_TGT; auto.
  des. splits; i.
  - punfold SIM1. exploit SIM1; try apply SC1; eauto. i. des.
    apply compose_is_terminal in TERMINAL_TGT; auto. des.
    exploit TERMINAL; eauto. i. des.
    exploit Configuration.rtc_step_future; eauto. s. i. des.
    exploit Configuration.rtc_step_disjoint; eauto. s. i. des.
    exploit compose_rtc_step1; eauto. s. i. des.
    punfold SIM2. exploit SIM2; try apply SC; eauto.
    { etrans; eauto. }
    { etrans; eauto. }
    i. des.
    exploit TERMINAL0; eauto. i. des.
    exploit Configuration.rtc_step_future; eauto. s. i. des.
    exploit Configuration.rtc_step_disjoint; try symmetry; eauto. s. i. des.
    exploit compose_rtc_step2; eauto. s. i. des.
    esplits.
    + etrans; eauto.
    + eauto.
    + eauto.
    + apply compose_is_terminal; auto.
  - apply compose_step in STEP_TGT; auto. des; subst.
    + exploit Configuration.step_future; eauto. s. i. des.
      exploit Configuration.step_disjoint; eauto. s. i. des.
      punfold SIM1. exploit SIM1; try apply SC1; eauto. i. des.
      exploit STEP0; eauto. i. des. inv SIM; [|done].
      exploit Configuration.rtc_step_future; eauto. s. i. des.
      exploit Configuration.rtc_step_disjoint; eauto. s. i. des.
      exploit compose_rtc_step1; eauto. s. i. des.
      exploit Configuration.opt_step_future; eauto. s. i. des.
      exploit Configuration.opt_step_disjoint; eauto. s. i. des.
      exploit compose_opt_step1; eauto. i. des.
      esplits; eauto.
      right. apply CIH; auto.
      eapply sim_future; eauto.
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
    + exploit Configuration.step_future; eauto. s. i. des.
      exploit Configuration.step_disjoint; try symmetry; eauto. s. i. des.
      punfold SIM2. exploit SIM2; try apply SC1; eauto. i. des.
      exploit STEP0; eauto. i. des. inv SIM; [|done].
      exploit Configuration.rtc_step_future; eauto. s. i. des.
      exploit Configuration.rtc_step_disjoint; try symmetry; eauto. s. i. des.
      exploit compose_rtc_step2; eauto. s. i. des.
      exploit Configuration.opt_step_future; eauto. s. i. des.
      exploit Configuration.opt_step_disjoint; eauto. s. i. des.
      exploit compose_opt_step2; eauto. i. des.
      esplits; eauto.
      right. apply CIH; auto.
      { symmetry. auto. }
      eapply sim_future; eauto.
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
      * repeat (etrans; eauto).
Qed.
