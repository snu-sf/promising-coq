Require Import Omega.
Require Import RelationClasses.
Require Import Bool.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import MemoryRel.
Require Import OrdStep.

Set Implicit Arguments.

(* TODO: add the condition for race-freedom *)
Inductive sim (c:Configuration.t): Prop :=
| sim_intro
    s
    (STEPS: rtc (union interleaving_step) (Configuration.init s) c)
.

Lemma sim_init s: sim (Configuration.init s).
Proof. econs. eauto. Qed.

Lemma sim_progress
      c1 c2
      e tid
      (SIM: sim c1)
      (STEP: ord_step Ordering.acqrel e tid c1 c2):
  sim c2.
Proof.
  destruct (ThreadEvent.is_accessing e) as [[loc ts]|] eqn:ACCESSING; cycle 1.
  { inv SIM. econs. eapply rtc_n1; eauto. econs.
    instantiate (1 := (_, _)). econs; eauto.
    unfold interleaving. ss. rewrite ACCESSING. ss.
  }
  destruct (Time.le_lt_dec (Memory.max_ts loc c2.(Configuration.memory)) ts).
  { inv SIM. econs. eapply rtc_n1; eauto. econs.
    instantiate (1 := (_, _)). econs; eauto.
    unfold interleaving. ss. rewrite ACCESSING.
    destruct (Time.le_lt_dec (Memory.max_ts loc (Configuration.memory c2)) ts); ss.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  }
  admit. (* from "we can find the first event, say alpha_k, writing to x at timestamp t ..." *)
Admitted.
