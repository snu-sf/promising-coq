Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Require Import MemoryRel.
Require Import SmallStep.
Require Import PromiseConsistent.
Require Import ReorderPromiseSame.
Require Import ReorderPromiseDiff.

Set Implicit Arguments.


Lemma reorder_promise_small_step
      c0
      tid1 e1 c1
      tid2 e2 c2
      loc to
      (WF: Configuration.wf c0)
      (STEP1: small_step true tid1 e1 c0 c1)
      (STEP2: small_step false tid2 e2 c1 c2)
      (E1: ThreadEvent.is_promising e1 = Some (loc, to))
      (NOTLN: ThreadEvent.is_lower_none e1 = false)
      (E2: forall val released ord, ThreadEvent.is_reading e2 <> Some (loc, to, val, released, ord))
      (PCONS: promise_consistent_th tid1 c2):
  (exists e2',
      <<TEQ: tid1 = tid2>> /\
      <<STEP: small_step true tid2 e2' c0 c2>> /\
      <<EVENT: ThreadEvent.get_non_promise e2' = ThreadEvent.get_non_promise e2>>) \/
  (exists e2' c1' e1' l t,
      <<STEP1: small_step false tid2 e2' c0 c1'>> /\
      <<STEP2: small_step true tid1 e1' c1' c2>> /\
      <<PROMISING: ThreadEvent.is_promising e1' = Some (l, t)>> /\
      <<EVENT: ThreadEvent.get_non_promise e2' = ThreadEvent.get_non_promise e2>>).
Proof.
  destruct (Ident.eq_dec tid1 tid2).
  - subst. inv STEP1. inv STEP2. ss.
    rewrite IdentMap.gss in TID0. inv TID0. apply inj_pair2 in H1. subst.
    clear PFREE. destruct pf0; ss. inv STEP; [|by inv STEP1; inv E1].
    destruct pf.
    { inv STEP1. by destruct kind, released. }
    r in PCONS; ss. rewrite IdentMap.gss in PCONS.
    exploit (@reorder_nonpf_pf lang0 e1 e2); eauto; try by eapply WF; eauto.
    i. des.
    + left. esplits; eauto. econs; eauto. rewrite IdentMap.add_add_eq; eauto.
    + right. assert (X:=STEP3). inv X.
      esplits.
      * econs; try apply STEP2; eauto.
      * econs; s; rewrite ?IdentMap.gss, ?IdentMap.add_add_eq; eauto.
      * s; eauto.
      * eauto.

  - right. inv STEP1. inv STEP2. ss. clear PFREE. des; try done.
    rewrite IdentMap.gso in TID0; auto.
    inv STEP; [|by inv STEP1; inv E1].
    inv STEP0.
    { inv STEP. inv STEP1. 
      exploit reorder_promise_promise_diff; eauto; try eapply WF; eauto.
      { i. apply promise_pf_inv in PFREE0. des; subst. econs. }
      i; des. esplits; eauto using Thread.promise_step_intro.
      econs; s; rewrite ?IdentMap.gso; eauto using Thread.promise_step_intro.
      rewrite IdentMap.add_add; eauto.
    }
    inv STEP1. ss. inv E1.
    exploit reorder_promise_program_diff; eauto;
      (try by eapply WF; eauto). i. des.
    esplits.
    + eauto.
    + econs; s; rewrite ?IdentMap.gso; [| |econs; econs|..]; eauto.
      rewrite IdentMap.add_add; auto.
    + s. eauto.
    + eauto.
Qed.
