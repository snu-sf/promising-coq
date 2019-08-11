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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.
Require Import MergeStep.
Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Lemma assign_sim_thread:
  forall v1 r2
    rs_src rs_tgt lc_src lc_tgt sc0_src sc0_tgt mem0_src mem0_tgt
    (RS: rs_src = RegFun.add r2 (RegFile.eval_value rs_tgt v1) rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt),
    sim_thread
      (sim_terminal eq)
      (State.mk rs_src []) lc_src sc0_src mem0_src
      (State.mk rs_tgt [Stmt.instr (Instr.assign r2 (Instr.expr_val v1))]) lc_tgt sc0_tgt mem0_tgt.
Proof.
  pcofix CIH. i. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    esplits; try apply SC; eauto.
    + econs 1.
    + auto.
    + left. eapply paco9_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
Qed.

Lemma merge_load_load_sim_stmts
      l o
      r1
      r2:
  sim_stmts eq
            [Stmt.instr (Instr.load r1 l o); Stmt.instr (Instr.load r2 l o)]
            [Stmt.instr (Instr.load r1 l o); Stmt.instr (Instr.assign r2 (Instr.expr_val (Value.reg r1)))]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    exploit sim_local_read; try exact LOCAL0; eauto; try refl. i. des.
    exploit merge_read_read; try exact STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon.
      * apply assign_sim_thread; eauto. s. rewrite RegFun.add_spec_eq. auto.
      * i. inv PR.
Qed.

Lemma merge_store_load_sim_stmts
      l
      v1 o1
      r2 o2
      (O: Ordering.le Ordering.seqcst o2 -> Ordering.le Ordering.seqcst o1):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.load r2 l o2)]
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* store *)
    hexploit sim_local_write; try exact LOCAL1; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_read1; try exact STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon.
      * apply assign_sim_thread; auto.
      * i. inv PR.
Qed.

Lemma merge_store_store_sim_stmts
      l o
      v1
      v2:
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.store l v2 o)]
            [Stmt.instr (Instr.store l v2 o)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write_None; try exact STEP_SRC; eauto; try by viewtac. i. des.
    + esplits.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply sim_stmts_nil; eauto. etrans; eauto. }
        { ii. inv PR. }
    + inv STEP1.
      esplits.
      * econs 2; eauto. econs. econs. econs 2.
        econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply sim_stmts_nil; eauto. etrans; eauto. }
        { ii. inv PR. }
Qed.

Lemma merge_store_update_sim_stmts
      l o
      v1
      r2 or2
      (ORD: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst o):
   sim_stmts eq
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.update r2 l (Instr.fetch_add (Value.const 0)) or2 o)]
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write; try exact STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
    + esplits.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read1; try exact STEP2; eauto. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      esplits.
      * econs 2; eauto. econs. econs. econs 2. econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read1; try apply STEP2; eauto. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
Qed.

Lemma merge_update_load_sim_stmts
      l
      r1 v1 or ow
      r2 or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.load r2 l or2)]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit merge_write_read2; try apply LOCAL2; eauto.
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto; try by viewtac. i. des.
    hexploit sim_local_write; try apply SC; try apply LOCAL2; eauto; try refl. i. des.
    exploit Local.write_step_future; try apply STEP_SRC; eauto; try by viewtac. i. des.
    exploit sim_local_read; try exact x0; eauto; try refl. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon.
      * apply assign_sim_thread; auto. s. rewrite RegFun.add_spec_eq. inv RMW. auto.
      * i. inv PR.
Qed.

Lemma merge_update_update_sim_stmts
      l or ow
      r1 v1
      r2 or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.update r2 l (Instr.fetch_add 0) or2 ow)]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    exploit Time.middle_spec; eauto.
    { inv LOCAL2. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
    exploit merge_write_write; try exact STEP_SRC0; eauto.
    { inv STEP_SRC. eapply MEM_SRC. eauto. }
    i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      exploit reorder_read_promise_diff; try exact STEP_SRC; try exact STEP1; eauto.
      { inv LOCAL2. exploit MemoryFacts.write_time_lt; eauto. ii. inv H.
        eapply Time.lt_strorder. eauto.
      }
      i. des.
      esplits.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 4]; try exact STEP4; try exact STEP_SRC0; eauto.
          - econs. econs. s. eauto.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { inv RMW. eapply merge_write_read2; try exact STEP2; viewtac.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply assign_sim_thread; eauto.
          - s. unfold RegFun.find. unfold RegFun.add at 4. condtac; [|congr]. auto.
          - etrans; eauto.
        }
        { i. inv PR. }
    + inv STEP1.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * econs 2; eauto.
        econs. econs. econs 2. econs; [|econs 4]; try exact STEP_SRC; try exact STEP2; eauto.
        { econs. econs. s. eauto. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { inv RMW. eapply merge_write_read2; try exact STEP2; viewtac.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco9_mon.
        { apply assign_sim_thread; eauto.
          - s. unfold RegFun.find. unfold RegFun.add at 4. condtac; [|congr]. auto.
          - etrans; eauto.
        }
        { i. inv PR. }
Qed.

Lemma merge_fence_fence_sim_stmts
      ordr ordw:
  sim_stmts eq
            [Stmt.instr (Instr.fence ordr ordw); Stmt.instr (Instr.fence ordr ordw)]
            [Stmt.instr (Instr.fence ordr ordw)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
        try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit sim_local_fence; try exact LOCAL0; try exact SC; eauto; try refl. i. des.
    exploit merge_fence_fence; try exact STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon.
      * apply sim_stmts_nil; eauto. etrans; eauto.
      * ii. inv PR.
Qed.
