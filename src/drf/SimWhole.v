Require Import Program.
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

Require Import SimMemory.
Require Import SimPromises.
Require Import Behavior.

Set Implicit Arguments.


Section SimWhole.
  Variable (step_src step_tgt: forall (e:option Event.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop).

  Definition SIM_WHOLE := forall (c1_src c1_tgt:Configuration.t), Prop.

  Inductive _sim_whole
            (sim_whole: SIM_WHOLE)
            (c1_src c1_tgt:Configuration.t): Prop :=
  | _sim_whole_intro
      (TERMINAL:
         forall (TERMINAL_TGT: Threads.is_terminal (Configuration.threads c1_tgt)),
         exists c2_src,
           <<STEPS: rtc (union (step_src None)) c1_src c2_src>> /\
           <<TERMINAL_SRC: Threads.is_terminal (Configuration.threads c2_src)>>)
      (STEP:
         forall e tid_tgt c3_tgt
           (STEP_TGT: step_tgt e tid_tgt c1_tgt c3_tgt),
         exists tid_src c2_src c3_src,
           <<STEPS_SRC: rtc (union (step_src None)) c1_src c2_src>> /\
           <<STEP_SRC: opt step_src e tid_src c2_src c3_src>> /\
           <<SIM: sim_whole c3_src c3_tgt>>)
  .

  Lemma _sim_whole_mon: monotone2 _sim_whole.
  Proof.
    ii. inv IN. econs; eauto. i.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  #[local]
  Hint Resolve _sim_whole_mon: paco.

  Definition sim_whole: SIM_WHOLE := paco2 _sim_whole bot2.
End SimWhole.
#[export]
Hint Resolve _sim_whole_mon: paco.


Lemma sim_whole_adequacy
      step_src step_tgt
      c_src c_tgt
      (SIM: sim_whole step_src step_tgt c_src c_tgt):
  behaviors step_tgt c_tgt <1= behaviors step_src c_src.
Proof.
  s. i.
  revert c_src SIM.
  dependent induction PR; i.
  - punfold SIM. inv SIM. exploit TERMINAL0; eauto. i. des.
    eapply rtc_tau_step_behavior; eauto. econs 1. eauto.
  - punfold SIM. inv SIM. exploit STEP0; eauto. i. des. inv SIM; ss.
    eapply rtc_tau_step_behavior; eauto.
    inv STEP_SRC. econs 2; eauto.
  - punfold SIM. inv SIM. exploit STEP0; eauto. i. des. inv SIM; ss.
    eapply rtc_tau_step_behavior; eauto.
    inv STEP_SRC; eauto. econs 3; eauto.
Qed.
