Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.

Require Import Axioms.
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
      + i. eapply H; eauto.
        rewrite Threads.compose_spec. rewrite TH. auto.
      + i. eapply H; eauto.
        rewrite compose_comm.
        rewrite Threads.compose_spec. rewrite TH. auto.
    - des.
      rewrite Threads.compose_spec in TH.
      unfold Threads.compose_option in TH.
      destruct (IdentMap.find tid ths1) eqn:SRC; inv TH.
      + eapply H; eauto.
      + eapply H0; eauto.
  Qed.

  Lemma compose_forall_rev P:
    (forall tid lang th (TH: IdentMap.find tid ths1 = Some (existT _ lang th)),
        (P tid lang th):Prop) ->
    (forall tid lang th (TH: IdentMap.find tid ths2 = Some (existT _ lang th)),
        (P tid lang th):Prop) ->
    (forall tid lang th (TH: IdentMap.find tid (Threads.compose ths1 ths2) = Some (existT _ lang th)),
        (P tid lang th):Prop).
  Proof.
    i. apply compose_forall; auto.
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
    <<CONSISTENT1: Configuration.consistent (Configuration.mk ths1 mem)>> /\
    <<CONSISTENT2: Configuration.consistent (Configuration.mk ths2 mem)>>.
  Proof.
    econs; intro X.
    - inv X. splits.
      + econs; s.
        * admit. (* threads consistency *)
        * apply compose_le. auto.
        * eapply compose_forall in VALID. des. auto.
      + econs; s.
        * admit. (* threads consistency *)
        * apply compose_le. auto.
        * eapply compose_forall in VALID. des. auto.
    - des. inv CONSISTENT1. inv CONSISTENT2. ss. econs; s.
      + admit. (* threads consistency *)
      + apply compose_le. splits; eauto.
      + eapply (@compose_forall_rev _ VALID VALID0); eauto.
  Admitted.
End Compose.

Lemma compose_step
      ths1 ths2
      e mem ths' mem'
      (DISJOINT: Threads.disjoint ths1 ths2)
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
  inv STEP. ss.
  rewrite Threads.compose_spec in TID.
  unfold Threads.compose_option in TID.
  destruct (IdentMap.find tid ths1) eqn:TH1,
           (IdentMap.find tid ths2) eqn:TH2; inv TID.
  - exfalso. inv DISJOINT. eapply THREAD; eauto.
  - left. exists (IdentMap.add tid (existT _ lang th3) ths1). splits; [|econs; eauto].
    apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    destruct (IdentMap.Facts.eq_dec tid y); auto.
  - right. exists (IdentMap.add tid (existT _ lang th3) ths2). splits; [|econs; eauto].
    apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    destruct (IdentMap.Facts.eq_dec tid y); auto.
    subst. unfold Threads.compose_option. rewrite TH1. auto.
Qed.

Lemma compose_step1
      ths1 ths2
      e mem ths1' mem'
      (STEP: Configuration.step
               e
               (Configuration.mk ths1 mem)
               (Configuration.mk ths1' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 mem)):
  <<STEP: Configuration.step
            e
            (Configuration.mk (Threads.compose ths1 ths2) mem)
            (Configuration.mk (Threads.compose ths1' ths2) mem')>> /\
  <<DISJOINT': Threads.disjoint ths1' ths2>> /\
  <<CONSISTENT2': Configuration.consistent (Configuration.mk ths2 mem')>>.
Proof.
  exploit Configuration.disjoint_step; eauto. s. i. des.
  splits; eauto. inv STEP. ss.
  replace (Threads.compose (IdentMap.add tid (existT _ lang th3) ths1) ths2)
  with (IdentMap.add tid (existT _ lang th3) (Threads.compose ths1 ths2)).
  - econs; eauto.
    s. rewrite Threads.compose_spec. unfold Threads.compose_option.
    rewrite TID. auto.
  - apply IdentMap.eq_leibniz. ii.
    rewrite ? IdentMap.Facts.add_o.
    rewrite ? Threads.compose_spec.
    rewrite ? IdentMap.Facts.add_o.
    destruct (IdentMap.Facts.eq_dec tid y); auto.
Qed.

Lemma compose_step2
      ths1 ths2
      e mem ths2' mem'
      (STEP: Configuration.step
               e
               (Configuration.mk ths2 mem)
               (Configuration.mk ths2' mem'))
      (DISJOINT: Threads.disjoint ths1 ths2)
      (CONSISTENT1: Configuration.consistent (Configuration.mk ths1 mem))
      (CONSISTENT2: Configuration.consistent (Configuration.mk ths2 mem)):
  <<STEP: Configuration.step
            e
            (Configuration.mk (Threads.compose ths1 ths2) mem)
            (Configuration.mk (Threads.compose ths1 ths2') mem')>> /\
  <<DISJOINT': Threads.disjoint ths1 ths2'>> /\
  <<CONSISTENT1': Configuration.consistent (Configuration.mk ths1 mem')>>.
Proof.
  exploit Configuration.disjoint_step; try symmetry; eauto. s. i. des.
  exploit compose_step1; try apply STEP; try apply CONSISTENT1; eauto.
  { symmetry. auto. }
  i. des. splits; eauto.
  - rewrite (@compose_comm ths1 ths2); auto.
    rewrite (@compose_comm ths1 ths2'); auto.
    symmetry. auto.
  - symmetry. auto.
Qed.

Lemma compose_rtc_step1
      c1 c2 ths
      (STEPS: rtc (Configuration.step None) c1 c2)
      (DISJOINT: Threads.disjoint c1.(Configuration.threads) ths)
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT: Configuration.consistent (Configuration.mk ths c1.(Configuration.memory))):
  <<STEPS: rtc (Configuration.step None)
               (Configuration.mk (Threads.compose c1.(Configuration.threads) ths) c1.(Configuration.memory))
               (Configuration.mk (Threads.compose c2.(Configuration.threads) ths) c2.(Configuration.memory))>> /\
  <<DISJOINT': Threads.disjoint c2.(Configuration.threads) ths>> /\
  <<CONSISTENT': Configuration.consistent (Configuration.mk ths c2.(Configuration.memory))>>.
Proof.
  revert CONSISTENT1 CONSISTENT. induction STEPS; auto. i.
  exploit Configuration.consistent_step; eauto. i. des.
  exploit Configuration.disjoint_step; eauto. i. des.
  destruct x, y. exploit compose_step1; eauto. s. i. des.
  exploit IHSTEPS; eauto. s. i. des.
  splits; eauto.
  econs; eauto.
Qed.

Lemma compose_rtc_step2
      c1 c2 ths
      (STEPS: rtc (Configuration.step None) c1 c2)
      (DISJOINT: Threads.disjoint ths c1.(Configuration.threads))
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT: Configuration.consistent (Configuration.mk ths c1.(Configuration.memory))):
  <<STEPS: rtc (Configuration.step None)
               (Configuration.mk (Threads.compose ths c1.(Configuration.threads)) c1.(Configuration.memory))
               (Configuration.mk (Threads.compose ths c2.(Configuration.threads)) c2.(Configuration.memory))>> /\
  <<DISJOINT': Threads.disjoint ths c2.(Configuration.threads)>> /\
  <<CONSISTENT': Configuration.consistent (Configuration.mk ths c2.(Configuration.memory))>>.
Proof.
  revert CONSISTENT1 CONSISTENT. induction STEPS; auto. i.
  exploit Configuration.consistent_step; eauto. i. des.
  exploit Configuration.disjoint_step; try symmetry; eauto. i. des.
  destruct x, y. exploit compose_step2; eauto. s. i. des.
  exploit IHSTEPS; try symmetry; eauto. s. i. des.
  splits; eauto.
  econs; eauto.
Qed.

Lemma sim_future
      ths_src mem_k1_src mem_k2_src
      ths_tgt mem_k1_tgt mem_k2_tgt
      (SIM: sim ths_src mem_k1_src ths_tgt mem_k1_tgt)
      (FUTURE_SRC: Memory.future mem_k1_src mem_k2_src)
      (FUTURE_TGT: Memory.future mem_k1_tgt mem_k2_tgt):
  sim ths_src mem_k2_src ths_tgt mem_k2_tgt.
Proof.
  revert ths_src mem_k1_src mem_k2_src
         ths_tgt mem_k1_tgt mem_k2_tgt
         SIM FUTURE_SRC FUTURE_TGT.
  pcofix CIH. i. punfold SIM. pfold. ii.
  exploit SIM; eauto.
  { etransitivity; eauto. }
  { etransitivity; eauto. }
  i. des. splits.
  - apply TERMINAL.
  - apply CONSISTENT.
  - i. exploit STEP; eauto. i. des; [|done].
    eexists _, _, _, _. splits; eauto.
    right. eapply CIH; eauto.
    + reflexivity.
    + reflexivity.
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
  apply compose_consistent in CONSISTENT_SRC; auto.
  apply compose_consistent in CONSISTENT_TGT; auto.
  des. splits; i.
  - punfold SIM1. exploit SIM1; eauto. i. des.
    apply compose_is_terminal in TERMINAL_TGT; auto. des.
    exploit TERMINAL; eauto. i. des.
    exploit Configuration.consistent_rtc_step; eauto. s. i. des.
    exploit Configuration.disjoint_rtc_step; eauto. s. i. des.
    exploit compose_rtc_step1; eauto. s. i. des.
    punfold SIM2. exploit SIM2; eauto.
    { etransitivity; eauto. }
    i. des.
    exploit TERMINAL0; eauto. i. des.
    exploit Configuration.consistent_rtc_step; eauto. s. i. des.
    exploit Configuration.disjoint_rtc_step; try symmetry; eauto. s. i. des.
    exploit compose_rtc_step2; eauto. s. i. des.
    eexists _, _. splits; [|eauto|].
    + eapply rtc_trans; eauto.
    + apply compose_is_terminal; auto.
  - i. apply compose_consistent in CONSISTENT_TGT; auto. des.
    apply compose_consistent; auto.
  - i. apply compose_step in STEP_TGT; auto. des; subst.
    + exploit Configuration.consistent_step; eauto. s. i. des.
      exploit Configuration.disjoint_step; eauto. s. i. des.
      punfold SIM1. exploit SIM1; eauto. i. des.
      exploit STEP0; eauto. i. des; [|done].
      exploit Configuration.consistent_rtc_step; eauto. s. i. des.
      exploit Configuration.disjoint_rtc_step; eauto. s. i. des.
      exploit compose_rtc_step1; eauto. s. i. des.
      exploit Configuration.consistent_step; eauto. s. i. des.
      exploit Configuration.disjoint_step; eauto. s. i. des.
      exploit compose_step1; eauto. i. des.
      eexists _, _, _, _. splits; eauto.
      right. apply CIH; auto.
      eapply sim_future; eauto; repeat (etransitivity; eauto). 
    + exploit Configuration.consistent_step; eauto. s. i. des.
      exploit Configuration.disjoint_step; try symmetry; eauto. s. i. des.
      punfold SIM2. exploit SIM2; eauto. i. des.
      exploit STEP0; eauto. i. des; [|done].
      exploit Configuration.consistent_rtc_step; eauto. s. i. des.
      exploit Configuration.disjoint_rtc_step; try symmetry; eauto. s. i. des.
      exploit compose_rtc_step2; eauto. s. i. des.
      exploit Configuration.consistent_step; eauto. s. i. des.
      exploit Configuration.disjoint_step; eauto. s. i. des.
      exploit compose_step2; eauto. i. des.
      eexists _, _, _, _. splits; eauto.
      right. apply CIH; auto.
      { symmetry. auto. }
      eapply sim_future; eauto; repeat (etransitivity; eauto).
Qed.
