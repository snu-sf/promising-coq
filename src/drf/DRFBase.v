Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.


Definition option_app {A} (a b: option A) : option A :=
  if a then a else b.

Lemma option_map_map 
      A B C (f: B -> C) (g: A -> B) (a: option A):
  option_map f (option_map g a) = option_map (fun x => f (g x)) a.
Proof.
  destruct a; eauto.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Definition ThreadEvent_is_promising (e: ThreadEvent.t) : option (Loc.t * Time.t) :=
  match e with
  | ThreadEvent.promise loc from to v rel kind => Some (loc, to)
  | _ => None
  end.





Inductive step_union {A} {E} (step: E -> A -> A -> Prop) (c1 c2: A) : Prop :=
| step_evt_intro e
    (USTEP: step e c1 c2)
.
Hint Constructors step_union.

Inductive with_pre {A} {E} (step: E -> A -> A -> Prop) bs : option (A*E) ->  A -> Prop :=
| swp_base:
  with_pre step bs None bs
| swp_step
    pre ms e es
    (PSTEPS: with_pre step bs pre ms)
    (PSTEP: step e ms es):
  with_pre step bs (Some(ms,e)) es
.
Hint Constructors with_pre.

Lemma with_pre_rtc_step_union
      A E (step: E -> A -> A -> Prop) c1 c2 pre
      (STEPS: with_pre step c1 pre c2):
  rtc (step_union step) c1 c2.
Proof.
  ginduction STEPS; s; i; subst; eauto.
  i. etrans; eauto.
  econs 2; [|reflexivity]. eauto.
Qed.

Lemma rtc_step_union_with_pre
      A E (step: E -> A -> A -> Prop) c1 c2
      (STEPS: rtc (step_union step) c1 c2):
  exists pre,
  with_pre step c1 pre c2.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEPS.
  induction STEPS.
  { exists None. eauto. }
  des. inv H. exists (Some(y,e)). s. eauto.
Qed.

Lemma with_pre_implies
      E A (step step': E -> A -> A -> Prop) c1 c2 pre
      (IMPL: forall e c1 c2 (STEP: step e c1 c2), step' e c1 c2)
      (STEPS: with_pre step c1 pre c2):
  with_pre step' c1 pre c2.
Proof.
  induction STEPS; eauto.
Qed.

Lemma with_pre_trans 
      A E (step: E -> A -> A -> Prop) c1 c2 c3 pre1 pre2
      (STEPS1: with_pre step c1 pre1 c2)
      (STEPS2: with_pre step c2 pre2 c3):
  with_pre step c1 (option_app pre2 pre1) c3.
Proof.
  ginduction STEPS2; s; i; des; subst; eauto.
Qed.
