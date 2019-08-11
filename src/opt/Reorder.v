From PromisingLib Require Import Basic.
Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import ReorderStep.
Require Import ReorderLoad.
Require Import ReorderStore.
Require Import ReorderUpdate.
Require Import ReorderFence.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Inductive reorder: forall (i1 i2:Instr.t), Prop :=
| reorder_intro_load
    r1 l1 o1 i2
    (REORDER: reorder_load r1 l1 o1 i2):
    reorder (Instr.load r1 l1 o1) i2
| reorder_intro_store
    l1 v1 o1 i2
    (REORDER: reorder_store l1 v1 o1 i2):
    reorder (Instr.store l1 v1 o1) i2
| reorder_intro_update
    l1 v1 rmw1 or1 ow1 i2
    (REORDER: reorder_update l1 v1 rmw1 or1 ow1 i2):
    reorder (Instr.update l1 v1 rmw1 or1 ow1) i2
| reorder_intro_fence
    or1 ow1 i2
    (REORDER: reorder_fence or1 ow1 i2):
    reorder (Instr.fence or1 ow1) i2
.

Lemma reorder_sim_stmts
      i1 i2 (REORDER: reorder i1 i2):
  sim_stmts eq
            [Stmt.instr i2; Stmt.instr i1]
            [Stmt.instr i1; Stmt.instr i2]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply SC; eauto.
    + econs 1.
    + auto.
    + left. eapply paco9_mon; [apply sim_load_sim_thread|]; ss.
      econs; eauto.
      eapply Local.read_step_future; eauto.
  - (* update-load *)
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply SC; eauto.
    + econs 1.
    + auto.
    + left. eapply paco9_mon; [apply sim_update_sim_thread|]; ss.
      econs; [eauto|..]; s; eauto.
      eapply Local.read_step_future; eauto.
  - (* store *)
    exploit Local.write_step_future; eauto; try by viewtac. i. des.
    hexploit sim_local_write; try exact LOCAL1; try exact SC;
      try exact WF_SRC; try refl; viewtac. i. des.
    exploit write_promise_fulfill; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_store_sim_thread|done].
      econs; eauto.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write; try apply LOCAL2; try apply LOCAL0; try apply SC; eauto; try refl; try by viewtac. i. des.
    exploit write_promise_fulfill; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit reorder_read_promise; try exact STEP_SRC; try exact STEP1; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_fulfill; try exact STEP2; try exact LOCAL4; try exact REL1;
      try exact WF3; try refl; eauto; try by viewtac. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_update_sim_thread|done].
      econs; [eauto|..]; s; eauto. 
      * etrans; eauto.
      * etrans; eauto.
  - (* fence *)
    exploit sim_local_fence; try apply SC; eauto; try refl. i. des.
    esplits.
    + eauto.
    + econs 1.
    + auto.
    + etrans; [|eauto]. inv STEP_SRC. apply TViewFacts.write_fence_sc_incr.
    + auto.
    + left. eapply paco9_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
Grab Existential Variables.
{ econs 2. }
{ econs. econs 3. }
Qed.
