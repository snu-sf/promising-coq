Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Definition pi_machine_event (e:ThreadEvent.t) (threads:Threads.t): Prop :=
  match e with
  | ThreadEvent.read loc ts val ord => ~ Threads.is_promised loc ts threads
  | _ => True
  end.

Inductive pi_step (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| pi_step_intro
    e lang st1 lc1 st2 lc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.memory)) (Thread.mk _ st2 lc2 memory2))
    (READINFO: pi_machine_event e c1.(Configuration.threads)):
    pi_step tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)) memory2)
.

Inductive pi_step_except (tid_except:Ident.t) (c1 c2:Configuration.t): Prop :=
| pi_step_except_intro
    tid
    (PI_STEP: pi_step tid c1 c2)
    (TID: tid <> tid_except)
.

Definition pi_consistent (c1:Configuration.t): Prop :=
  forall tid c2
    (TID: IdentMap.find tid c1.(Configuration.threads) <> None)
    (STEPS: rtc (pi_step_except tid) c1 c2),
  exists c3 lang st3 lc3,
    <<STEPS: rtc (pi_step tid) c2 c3>> /\
    <<THREAD: IdentMap.find tid c3.(Configuration.threads) = Some (existT _ lang st3, lc3)>> /\
    <<PROMISES: lc3.(Local.promises) = Memory.bot>>.

Lemma pi_step_find
      tid1 tid2 c1 c2
      (STEP: pi_step tid1 c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c2.(Configuration.threads) = IdentMap.find tid2 c1.(Configuration.threads).
Proof.
  inv STEP. s. rewrite IdentMap.Facts.add_neq_o; auto.
Qed.

Lemma rtc_pi_step_find
      tid1 tid2 c1 c2
      (STEP: rtc (pi_step tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c2.(Configuration.threads) = IdentMap.find tid2 c1.(Configuration.threads).
Proof.
  induction STEP; auto. erewrite IHSTEP, pi_step_find; eauto.
Qed.

Lemma pi_consistent_step_pi_step
      c1 c2
      e tid
      (PI_CONSISTENT: pi_consistent c1)
      (STEP: Configuration.step e tid c1 c2):
  rtc (pi_step tid) c1 c2.
Proof.
Admitted.

Lemma pi_consistent_pi_step_pi_consistent
      c1 c2
      tid
      (PI_CONSISTENT: pi_consistent c1)
      (STEP: rtc (pi_step tid) c1 c2):
  pi_consistent c2.
Proof.
  ii. destruct (Ident.eq_dec tid tid0).
  - subst tid0.
    admit.
  - eapply PI_CONSISTENT.
    + erewrite <- rtc_pi_step_find; eauto.
    + etrans; [|eauto]. eapply rtc_implies; [|apply STEP]. econs; eauto.
Admitted.
