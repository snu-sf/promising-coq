Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
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
    (forall tid lang th (TH: IdentMap.find tid (Threads.compose ths1 ths2) = Some (existT _ lang th)),
        (P tid lang th):Prop) <->
    (forall tid lang th (TH: IdentMap.find tid ths1 = Some (existT _ lang th)),
        (P tid lang th):Prop) /\
    (forall tid lang th (TH: IdentMap.find tid ths2 = Some (existT _ lang th)),
        (P tid lang th):Prop).
  Proof.
    econs; i.
    - splits.
      + intros tid lang th TH.
        eapply H; eauto.
        rewrite Threads.compose_spec. rewrite TH. auto.
      + rewrite compose_comm in H; auto.
        intros tid lang th TH.
        eapply H; eauto.
        rewrite Threads.compose_spec. rewrite TH. auto.
    - des.
      rewrite Threads.compose_spec in TH.
      unfold Threads.compose_option in TH.
      destruct (IdentMap.find tid ths1) eqn:SRC; inv TH.
      + eapply H; eauto.
      + eapply H0; eauto.
  Qed.

  Lemma compose_is_terminal:
    Threads.is_terminal (Threads.compose ths1 ths2) <->
    Threads.is_terminal ths1 /\ Threads.is_terminal ths2.
  Proof. apply compose_forall. Qed.

  Lemma compose_le mem:
    Threads.le (Threads.compose ths1 ths2) mem <->
    Threads.le ths1 mem /\ Threads.le ths2 mem.
  Proof. apply compose_forall. Qed.

  Lemma compose_consistent mem:
    Configuration.consistent (Configuration.mk (Threads.compose ths1 ths2) mem) <->
    Configuration.consistent (Configuration.mk ths1 mem) /\
    Configuration.consistent (Configuration.mk ths2 mem).
  Proof. apply compose_forall. Qed.

  Lemma compose_step
        e mem ths' mem'
        (STEP: Configuration.step
                 e
                 (Configuration.mk (Threads.compose ths1 ths2) mem)
                 (Configuration.mk ths' mem')):
    (exists ths1',
        <<NEXT: ths' = Threads.compose ths1' ths2>> /\
        <<STEP: Configuration.step
                  e
                  (Configuration.mk ths1 mem)
                  (Configuration.mk ths1' mem')>>) \/
    (exists ths2',
        <<NEXT: ths' = Threads.compose ths1 ths2'>> /\
        <<STEP: Configuration.step
                  e
                  (Configuration.mk ths2 mem)
                  (Configuration.mk ths2' mem')>>).
  Proof.
  Admitted.

  Lemma compose_step1
        e mem ths1' mem'
        (STEP: Configuration.step
                 e
                 (Configuration.mk ths1 mem)
                 (Configuration.mk ths1' mem')):
    <<DISJOINT: Threads.disjoint ths1' ths2>> /\
    <<STEP: Configuration.step
              e
              (Configuration.mk (Threads.compose ths1 ths2) mem)
              (Configuration.mk (Threads.compose ths1' ths2) mem')>>.
  Proof.
  Admitted.
End Compose.

Lemma disjoint_comm
      ths1 ths2
      (DISJOINT: Threads.disjoint ths1 ths2):
  Threads.disjoint ths2 ths1.
Proof.
  inv DISJOINT. econs; i.
  - eapply THREAD; eauto.
  - apply Memory.disjoint_comm. eapply MEMORY; eauto.
Qed.

Lemma compose_step2
      ths1 ths2
      (DISJOINT: Threads.disjoint ths1 ths2)
      e mem ths2' mem'
      (STEP: Configuration.step
               e
               (Configuration.mk ths2 mem)
               (Configuration.mk ths2' mem')):
  <<DISJOINT: Threads.disjoint ths1 ths2'>> /\
  <<STEP: Configuration.step
            e
            (Configuration.mk (Threads.compose ths1 ths2) mem)
            (Configuration.mk (Threads.compose ths1 ths2') mem')>>.
Proof.
  exploit compose_step1; [|apply STEP|].
  { apply disjoint_comm. eauto. }
  i. des. splits.
  { apply disjoint_comm. eauto. }
  rewrite (@compose_comm ths1 ths2); auto.
  rewrite (@compose_comm ths1 ths2'); auto.
  apply disjoint_comm. eauto.
Qed.

Lemma sim_compose
      ths1_src ths2_src mem_k_src
      ths1_tgt ths2_tgt mem_k_tgt
      (DISJOINT_SRC: Threads.disjoint ths1_src ths2_src)
      (DISJOINT_TGT: Threads.disjoint ths1_tgt ths2_tgt)
      (SIM1: sim ths1_src mem_k_src ths1_tgt mem_k_tgt)
      (SIM2: sim ths2_src mem_k_src ths2_tgt mem_k_tgt):
  sim (Threads.compose ths1_src ths2_src) mem_k_src
      (Threads.compose ths1_tgt ths2_tgt) mem_k_tgt.
Proof.
  revert
    ths1_src ths2_src mem_k_src
    ths1_tgt ths2_tgt mem_k_tgt
    DISJOINT_SRC DISJOINT_TGT
    SIM1 SIM2.
  pcofix CIH. i. pfold. ii.
  apply compose_le in LOCAL_SRC; auto.
  apply compose_le in LOCAL_TGT; auto.
  splits.
  - i. des.
    punfold SIM1. exploit SIM1; eauto. i. des.
    apply compose_is_terminal in TERMINAL_TGT; auto. des.
    exploit TERMINAL; eauto. i. des.
    punfold SIM2. exploit SIM2; eauto.
    { admit. (* other threads' le *) }
    { admit. (* future *) }
    i. des.
    exploit TERMINAL0; eauto. i. des.
    eexists _, _. splits; [|eauto|].
    + admit. (* steps *)
    + apply compose_is_terminal.
      * admit. (* disjoint *)
      * split. apply TERMINAL_SRC. apply TERMINAL_SRC0.
  - i. apply compose_consistent in CONSISTENT_TGT; auto. des.
    apply compose_consistent; auto. splits.
    + punfold SIM1. exploit SIM1; eauto. i. des.
      apply CONSISTENT. auto.
    + punfold SIM2. exploit SIM2; eauto. i. des.
      apply CONSISTENT. auto.
  - i. apply compose_step in STEP_TGT. des; subst.
    + punfold SIM1. exploit SIM1; eauto. i. des.
      exploit STEP0; eauto. i. des; [|done].
      eexists _, _, _, _. splits.
      * admit. (* steps *)
      * apply compose_step1; [|eauto].
        admit. (* disjoint *)
      * eauto.
      * right. apply CIH; [| |eauto|].
        { admit. (* disjoint *) }
        { admit. (* disjoint *) }
        { admit. (* sim future *) }
    + punfold SIM2. exploit SIM2; eauto. i. des.
      exploit STEP0; eauto. i. des; [|done].
      eexists _, _, _, _. splits.
      * admit. (* steps *)
      * apply compose_step2; [|eauto].
        admit. (* disjoint *)
      * eauto.
      * right. apply CIH; [| |eauto|].
        { admit. (* disjoint *) }
        { admit. (* disjoint *) }
        { admit. (* sim future *) }
Admitted.
