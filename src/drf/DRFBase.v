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
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.


Definition option_app {A} (a b: option A) : option A :=
  if a then a else b.

Lemma strengthen
      (A B: Prop)
      (H: A /\ (A -> B)):
  A /\ B.
Proof. intuition. Qed.

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



Definition mem_sub (cmp: Loc.t -> Time.t -> option View.t -> option View.t -> Prop) (m1 m2: Memory.t) : Prop :=
  forall loc ts from val rel1
    (IN: Memory.get loc ts m1 = Some (from, Message.mk val rel1)),
  exists rel2,
  <<IN: Memory.get loc ts m2 = Some (from, Message.mk val rel2)>> /\
  <<CMP: cmp loc ts rel1 rel2>>.

Definition loctmeq (l: Loc.t) (t: Time.t) (r1 r2: option View.t) : Prop := r1 = r2.
Hint Unfold loctmeq.

Lemma local_simul_fence
      com prm prm' sc ordr ordw com' sc'
      (LOCAL: Local.fence_step (Local.mk com prm) sc ordr ordw (Local.mk com' prm') sc'):
  Local.fence_step (Local.mk com Memory.bot) sc ordr ordw (Local.mk com' Memory.bot) sc'.
Proof.
  inv LOCAL. econs; eauto.
  s. i. apply Memory.bot_nonsynch.
Qed.

Lemma local_simul_write
      cmp com com' sc sc' mS mT mT' loc from to val relr relw ord kind prm prm'
      (SUB: mem_sub cmp mS mT)
      (DISJOINT: Memory.disjoint mS prm)
      (WRITE: Local.write_step (Local.mk com prm) sc mT loc from to val relr relw ord (Local.mk com' prm') sc' mT' kind):
  exists mS',
  Local.write_step (Local.mk com Memory.bot) sc mS loc from to val relr relw ord (Local.mk com' Memory.bot) sc' mS' Memory.op_kind_add.
Proof.
  set (relw' := relw).
  assert (RELW_WF: View.opt_wf relw').
  { inv WRITE. inv WRITE0. inv PROMISE.
    - inv MEM. inv ADD. auto.
    - inv MEM. inv SPLIT. auto.
    - inv MEM. inv LOWER. auto.
  }
  inv WRITE.
  hexploit (@Memory.add_exists Memory.bot loc from to val relw'); eauto.
  { i. rewrite Memory.bot_get in *. congr. }
  { eapply MemoryFacts.write_time_lt. eauto. }
  i. des.
  hexploit (@Memory.add_exists mS loc from to val relw'); eauto.
  { i. destruct msg2.
    inv WRITE0. inv PROMISE.
    - exploit SUB; eauto. i. des.
      inv MEM. inv ADD. eauto.
    - exploit Memory.split_get0; try exact PROMISES; eauto. s. i. des.
      inv DISJOINT. exploit DISJOINT0; eauto. i. des.
      symmetry in x. eapply Interval.le_disjoint; eauto. econs; [refl|].
      inv MEM. inv SPLIT. left. auto.
    - exploit Memory.lower_get0; try exact PROMISES; eauto. s. i.
      symmetry. eapply DISJOINT; eauto.
  }
  { eapply MemoryFacts.write_time_lt. eauto. }
  i. des.
  hexploit (@Memory.remove_exists mem2 loc from to val relw'); eauto.
  { erewrite Memory.add_o; eauto. condtac; ss. des; congr. }
  i. des.
  replace mem1 with Memory.bot in H1; cycle 1.
  { apply Memory.ext. i.
    erewrite (@Memory.remove_o mem1); eauto. erewrite (@Memory.add_o mem2); eauto.
    condtac; ss. des. subst. apply Memory.bot_get.
  }
  esplits. econs; eauto.
  - econs; eauto. econs; eauto.
    inv WRITE0. by inv PROMISE.
  - s. i. splits; ss. apply Memory.bot_nonsynch_loc.
Qed.
