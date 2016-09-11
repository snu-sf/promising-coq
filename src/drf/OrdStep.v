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
Require Import TView.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


(* TODO: position *)
Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.


Inductive ord_thread_step (ord:Ordering.t) (lang:Language.t) (e:ThreadEvent.program_t): forall (e1 e2:Thread.t lang), Prop :=
| ra_thread_step_intro
    st1 lc1 sc1 mem1
    st2 lc2 sc2 mem2
    (STATE: lang.(Language.step) (ThreadEvent.get_program_event (ThreadEvent.lift ord e)) st1 st2)
    (LOCAL: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
    ord_thread_step ord e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
.
Hint Constructors ord_thread_step.

Inductive ord_step (ord:Ordering.t) (e:ThreadEvent.program_t) (tid:Ident.t): forall (c1 c2:Configuration.t), Prop :=
| ord_step_intro
    c1 lang st1 lc1 st2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: ord_thread_step ord e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2)):
    ord_step ord e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)) sc2 memory2)
.

(* TODO: position *)
Definition ThreadEvent_is_accessing (e:ThreadEvent.t): option (Loc.t * Time.t) :=
  match e with
  | ThreadEvent.read loc ts _ _ _ => Some (loc, ts)
  | ThreadEvent.write loc _ ts _ _ _ => Some (loc, ts)
  | ThreadEvent.update loc _ ts _ _ _ _ _ _ => Some (loc, ts)
  | _ => None
  end.

Definition interleaving (e:ThreadEvent.t) (c2:Configuration.t): bool :=
  match ThreadEvent_is_accessing e with
  | None => true
  | Some (loc, ts) =>
    Time.le_lt_dec (Memory.max_ts loc c2.(Configuration.memory)) ts
  end.

Inductive interleaving_step (etid:ThreadEvent.program_t * Ident.t) (c1 c2:Configuration.t): Prop :=
| interleaving_step_intro
    (STEP: ord_step Ordering.acqrel etid.(fst) etid.(snd) c1 c2)
    (INTERLEAVING: interleaving etid.(fst) c2)
.

Lemma ord_step_threads1
      ord e tid c1 c2
      (STEP: ord_step ord e tid c1 c2):
  exists th1, IdentMap.find tid c1.(Configuration.threads) = Some th1.
Proof. inv STEP. eauto. Qed.

Lemma ord_step_threads2
      ord e tid c1 c2
      (STEP: ord_step ord e tid c1 c2):
  exists th2, IdentMap.find tid c2.(Configuration.threads) = Some th2.
Proof. inv STEP. s. rewrite IdentMap.gss. eauto. Qed.

Lemma interleaving_step_threads1
      etid c1 c2
      (STEP: interleaving_step etid c1 c2):
  exists th1, IdentMap.find etid.(snd) c1.(Configuration.threads) = Some th1.
Proof. inv STEP. eapply ord_step_threads1. eauto. Qed.

Lemma interleaving_step_threads2
      etid c1 c2
      (STEP: interleaving_step etid c1 c2):
  exists th2, IdentMap.find etid.(snd) c2.(Configuration.threads) = Some th2.
Proof. inv STEP. eapply ord_step_threads2. eauto. Qed.
