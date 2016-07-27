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

Require Import DRFBase.
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
      (E2: ThreadEvent.is_promising e2 = None)
      (E12: forall val released ord, ThreadEvent.is_reading e2 <> Some (loc, to, val, released, ord))
      (PCONS: promise_consistent_th tid1 c2):
  exists c1',
    <<STEP1: small_step false tid2 e2 c0 c1'>> /\
    <<STEP2: __guard__
               ((tid1, c1') = (tid2, c2) \/
                exists e1' l t,
                  <<STEP2: small_step true tid1 e1' c1' c2>> /\
                  <<PROMISING: ThreadEvent.is_promising e1' = Some (l, t)>>)>>.
Proof.
  destruct (Ident.eq_dec tid1 tid2).
  - subst. inv STEP1. inv STEP2. ss.
    rewrite IdentMap.gss in TID0. inv TID0. apply inj_pair2 in H1. subst.
    inv STEP; [|by inv STEP1; inv E1].
    inv STEP0; [by inv STEP; inv PFREE0|].
    exploit reorder_promise_program; eauto; s.
    { eapply PCONS. ss. rewrite IdentMap.gss. eauto. }
    { eapply WF. eauto. }
    { eapply WF. }
    { eapply WF. }
    i. des. destruct th1'. esplits.
    + econs; eauto.
    + unguardH STEP2. des.
      * left. inv STEP2. rewrite IdentMap.add_add_eq. auto.
      * right. inversion STEP2. subst. esplits. econs; ss.
        { rewrite IdentMap.gss. eauto. }
        { econs; eauto. }
        { rewrite ? IdentMap.add_add_eq. auto. }
        { s. eauto. }
  - inv STEP1. inv STEP2. ss.
    rewrite IdentMap.gso in TID0; auto.
    inv STEP; [|by inv STEP1; inv E1].
    inv STEP0; [by inv STEP; inv PFREE0|].
    inv STEP1. ss. inv E1.
    exploit reorder_promise_program_diff; eauto;
      (try by eapply WF; eauto). i. des.
    esplits.
    + econs; eauto.
    + right. esplits. econs; eauto.
      * s. rewrite IdentMap.gso; eauto.
      * econs 1. econs; eauto.
      * rewrite IdentMap.add_add; auto.
      * s. eauto.
Qed.
