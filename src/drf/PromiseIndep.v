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


Inductive pi_thread_step lang: forall (e:option Event.t) (readinfo:option (Loc.t * Time.t)) (e1 e2:Thread.t lang), Prop :=
| pi_step_promise
    e1 e2
    (STEP: Thread.promise_step e1 e2):
    pi_thread_step None None e1 e2
| pi_step_program
    e readinfo e1 e2
    (STEP: Thread.program_step e readinfo e1 e2):
    pi_thread_step e readinfo e1 e2
.

Inductive pi_step (tid:Ident.t) (e:option Event.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| pi_step_intro
    readinfo lang st1 lc1 e2 st3 lc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (Thread.step None) (Thread.mk _ st1 lc1 c1.(Configuration.memory)) e2)
    (STEP: pi_thread_step e readinfo e2 (Thread.mk _ st3 lc3 memory3))
    (READINFO: forall loc ts (READINFO: readinfo = Some (loc, ts)), ~ Threads.is_promised loc ts c1.(Configuration.threads)):
    pi_step tid e c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) memory3)
.

Inductive pi_step_except (tid_except:Ident.t) (c1 c2:Configuration.t): Prop :=
| pi_step_neq_intro
    tid e
    (PI_STEP: pi_step tid e c1 c2)
    (TID: tid <> tid_except)
.

Definition pi_consistent (c1:Configuration.t): Prop :=
  forall tid c2
    (TID: IdentMap.find tid c1.(Configuration.threads) <> None)
    (STEPS: rtc (pi_step_except tid) c1 c2),
  exists c3 lang st3 lc3,
    <<STEPS: rtc (pi_step tid None) c2 c3>> /\
    <<PROMISES: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st3, lc3)>>.
