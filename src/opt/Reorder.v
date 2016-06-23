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
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import Progress.
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
  { exploit sim_local_future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. committac.
      + apply Memory.sim_max_timemap; eauto. committac.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. committac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. committac.
  }
  { esplits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
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
  - (* store *)
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_write; try apply SC; eauto; try refl; committac. i. des.
    exploit Local.write_step_future; eauto. i. des.
    inv STEP_SRC. inv WRITE.
    exploit Memory.promise_future; try apply PROMISE; try apply WF_SRC; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs. econs. eauto.
      eapply promise_closed_capability; try apply PROMISE; try apply WF_SRC; eauto; committac.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_store_sim_thread|done].
      econs; eauto; (try by etrans; eauto).
      * hexploit Memory.promise_get2; eauto. i.
        assert (ORD1': ~ Ordering.le Ordering.acqrel ord).
        { by inv REORDER0; destruct ord; inv ORD1. }
        refine (Local.step_write_intro _ _ _ _ _ _); eauto; [|congr].
        econs; eauto. econs.
        { apply Memory.get_lower. auto. }
        { apply Memory.get_lower. eauto. }
      * econs; try apply WF_SRC; eauto.
        s. eapply Commit.future_closed; eauto. apply WF_SRC.
      * eapply Memory.future_closed_timemap; eauto.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write; try apply LOCAL2; try apply LOCAL0; try apply SC; eauto.
    { inv STEP_SRC. eapply MEM_SRC. eauto. }
    { inv STEP_SRC. eapply MEM_SRC. eauto. }
    { inv LOCAL1. eapply MEM_TGT. eauto. }
    i. des.
    exploit Local.write_step_future; eauto. i. des.
    inv STEP_SRC0. inv WRITE.
    exploit reorder_read_promise; try apply STEP_SRC; eauto.
    { econs. eauto.
      eapply promise_closed_capability; try apply PROMISE; try apply x1; eauto.
      inv STEP_SRC. eapply MEM_SRC. eauto.
    }
    i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs. eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_update_sim_thread|done].
      econs; auto.
      * eauto.
      * eauto.
      * admit.
      * eauto.
      * etrans; eauto.
  - (* fence *)
    exploit sim_local_fence; try apply SC; eauto; try refl. i. des.
    esplits.
    + eauto.
    + econs 1.
    + auto.
    + etrans; [|eauto]. inv STEP_SRC. apply CommitFacts.write_fence_sc_incr.
    + auto.
    + left. eapply paco9_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
Admitted.
