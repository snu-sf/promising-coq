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

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_update r1 l1 rmw1 o1: forall (i2:Instr.t), Prop :=
| reorder_update_load
    r2 l2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.release)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_update r1 l1 rmw1 o1 (Instr.load r2 l2 o2)
| reorder_update_store
    l2 v2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 o1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_update r1 l1 rmw1 o1 (Instr.store l2 v2 o2)
| reorder_update_update
    r2 l2 rmw2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.release)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 o1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 o2))):
    reorder_update r1 l1 rmw1 o1 (Instr.update r2 l2 rmw2 o2)
.

Inductive sim_update: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                        (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_update_intro
    r1 l1 from1 to1 vr1 vret1 vw1 releasedr1 releasedw1 rmw1 o1 i2
    rs th1_src th1_tgt th2_src th3_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_update r1 l1 rmw1 o1 i2)
    (RMW: RegFile.eval_rmw rs rmw1 vr1 = (vret1, vw1))
    (READ: Local.read_step th1_src mem_k_src l1 from1 vr1 releasedr1 o1 th2_src)
    (FULFILL: Local.fulfill_step th2_src mem_k_src l1 from1 to1 vw1 releasedw1 o1 th3_src)
    (RELEASED: Snapshot.le releasedr1 releasedw1)
    (LOCAL: sim_local th3_src th1_tgt):
    sim_update
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.update r1 l1 rmw1 o1)]) th1_src mem_k_src
      (State.mk (RegFun.add r1 vret1 rs) [Stmt.instr i2]) th1_tgt mem_k_tgt
.

Lemma sim_update_sim_thread:
  sim_update <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - admit.
    (* future; https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L100 *)
  - admit.
  - inv PR. i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    exploit Local.future_read_step; try apply READ; eauto. i.
    exploit Local.future_fulfill_step; try apply FULFILL; eauto. i.
    inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
    + (* promise *)
      exploit sim_local_promise; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_promise; try apply x3; try apply STEP_SRC; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_promise; try apply x0; try apply STEP1; eauto. i. des.
      exploit sim_local_fulfill; try apply LOCAL3; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.promise_step_future; eauto.
      }
      { eapply Local.promise_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 1; eauto.
      * right. apply CIH. econs; try apply STEP3; try apply STEP_SRC0; eauto.
        etransitivity; eauto. etransitivity; eauto.
    + (* load *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_read; try apply x3; try apply STEP_SRC; eauto.
      { destruct o1; ss. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
      exploit sim_local_fulfill; try apply SIM0; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 3; eauto. econs. econs.
      * econs. econs 5; eauto.
        { econs. econs. erewrite RegFile.eq_except_rmw; eauto.
          - admit.
          - apply RegFile.eq_except_singleton.
        }
        { s. econs 1. eauto. }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        { apply RegFun.add_add. admit. }
        { etransitivity; eauto. etransitivity; eauto. }
    + (* store *)
      exploit sim_local_write; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_write; try apply x3; try apply STEP_SRC; eauto.
      { destruct o1; ss. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_write; try apply x0; try apply STEP1; eauto.
      { destruct o1; ss. }
      i. des.
      exploit sim_local_fulfill; try apply SIM0; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.write_step_future; eauto.
      }
      { eapply Local.write_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 4; eauto. econs.
        erewrite <- RegFile.eq_except_value; eauto.
        { econs. }
        { admit. }
      * econs. econs 5; eauto.
        { econs. econs. eauto. }
        { s. econs 1. eauto. }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        etransitivity; eauto. etransitivity; eauto.
    + (* update *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_fulfill_read; try apply x3; try apply STEP_SRC; eauto.
      { destruct o1; ss. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
      exploit sim_local_fulfill; try apply STEP2; try apply SIM0; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      rewrite SIM, LOCAL0 in LOCAL3.
      exploit sim_local_write; eauto.
      { eapply Local.fulfill_step_future; eauto.
        eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_write; try apply STEP_SRC0; try apply STEP_SRC1; eauto.
      { destruct o1; ss. }
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      exploit reorder_read_write; try apply STEP3; try apply STEP4; eauto.
      { destruct o1; ss. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit sim_local_fulfill; try apply STEP5; try apply SIM2; try reflexivity; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.write_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.write_step_future; eauto.
        eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 5; eauto. econs. econs.
        erewrite <- RegFile.eq_except_rmw; eauto.
        { admit. }
        { apply RegFile.eq_except_singleton. }
      * econs. econs 5; try apply STEP7; try apply STEP_SRC2; eauto.
        { econs. econs.
          erewrite RegFile.eq_except_rmw; eauto.
          - admit.
          - apply RegFile.eq_except_singleton.
        }
        { econs 1. eauto. }
      * eauto.
      * left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        { apply RegFun.add_add. admit. }
        { etransitivity; eauto. etransitivity; eauto. }
Admitted.
