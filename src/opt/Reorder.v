Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import ReorderBase.
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
    l1 v1 rmw1 o1 i2
    (REORDER: reorder_update l1 v1 rmw1 o1 i2):
    reorder (Instr.update l1 v1 rmw1 o1) i2
| reorder_intro_fence
    o1 i2
    (REORDER: reorder_fence o1 i2):
    reorder (Instr.fence o1) i2
.

Lemma reorder_sim_stmts
      i1 i2 (REORDER: reorder i1 i2):
  sim_stmts eq
            [Stmt.instr Instr.skip; Stmt.instr i2; Stmt.instr i1]
            [Stmt.instr i1; Stmt.instr i2]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { admit. }
  { i. eexists _, _, _. splits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
  }
  i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
  inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    econs. econs 1; eauto.
  - (* load *)
    exploit sim_local_read; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs. econs 6.
      { econs. econs. }
      { s. apply Local.fence_relaxed. apply WF_SRC. }
    + left. eapply paco7_mon; [apply sim_load_sim_thread|]; ss.
      econs; eauto.
  - (* store *)
    exploit sim_local_write; eauto. i. des.
    inv STEP_SRC.
    + eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 6.
        { econs. econs. }
        { s. apply Local.fence_relaxed. apply WF_SRC. }
      * left. eapply paco7_mon; [apply sim_store_sim_thread|]; ss.
        econs; eauto.
    + eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 6.
        { econs. econs. }
        { s. apply Local.fence_relaxed. apply WF_SRC. }
      * econs. econs 1; eauto.
      * eauto.
      * left. eapply paco7_mon; [apply sim_store_sim_thread|]; ss.
        econs; eauto.
  - (* update *)
    exploit sim_local_read; eauto. i. des.
    exploit sim_local_write; eauto.
    { eapply Local.read_step_future; eauto. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    inv STEP_SRC0.
    + eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 6.
        { econs. econs. }
        { s. apply Local.fence_relaxed. apply WF_SRC. }
      * left. eapply paco7_mon; [apply sim_update_sim_thread|]; ss.
        econs; eauto.
    + exploit reorder_read_promise; try apply STEP_SRC; try apply x0; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 6.
        { econs. econs. }
        { s. apply Local.fence_relaxed. apply WF_SRC. }
      * econs. econs 1; eauto.
      * eauto.
      * left. eapply paco7_mon; [apply sim_update_sim_thread|]; ss.
        econs; eauto.
  - (* fence *)
    exploit sim_local_fence; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs. econs 6.
      { econs. econs. }
      { s. apply Local.fence_relaxed. apply WF_SRC. }
    + left. eapply paco7_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
Admitted.
