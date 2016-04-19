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
Require Import Thread.
Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)

Inductive reorder: forall (i1 i2:Instr.t), Prop :=
| reorder_load_store
    r1 l1 o1
    l2 v2 o2
    (LOC: l1 <> l2)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1)) (Instr.regs_of (Instr.store l2 v2 o2)))
    (ORDERING1: ~ Ordering.le Ordering.acquire o1)
    (ORDERING1: ~ Ordering.le Ordering.release o2):
    reorder (Instr.load r1 l1 o1) (Instr.store l2 v2 o2)
.

Inductive sim_reorder_store (i1:Instr.t) (l2:Loc.t) (v2:Value.t) (o2:Ordering.t):
  forall (th_src:Thread.t lang) (mem_k_src:Memory.t)
    (th_tgt:Thread.t lang) (mem_k_tgt:Memory.t), Prop :=
| sim_reorder_phase0
    rs
    commit_src commit_tgt
    local
    mem_k_src mem_k_tgt
    (COMMIT: Commit.le commit_src commit_tgt):
    sim_reorder_store
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs [Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) commit_src local)
      mem_k_src
      (Thread.mk lang (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr i1]) commit_tgt local)
      mem_k_tgt
| sim_reorder_phase1
    rs
    commit_src commit_tgt
    local_src local_tgt
    mem_k_src mem_k_tgt
    from to msg
    (COMMIT1: Commit.le commit_src commit_tgt)
    (COMMIT2: Snapshot.writable commit_src.(Commit.current) l2 to)
    (LT: Time.lt from to)
    (LOCAL: MemInv.sem (Memory.singleton l2 msg LT) local_src local_tgt):
    sim_reorder_store
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs [Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) commit_src local_src)
      mem_k_src
      (Thread.mk lang (State.mk rs [Stmt.instr i1]) commit_tgt local_tgt)
      mem_k_tgt
| sim_reorder_phase2
    rs
    commit_src commit_tgt
    local
    mem_k_src mem_k_tgt
    (COMMIT: Commit.le commit_src commit_tgt):
    sim_reorder_store
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs []) commit_src local)
      mem_k_src
      (Thread.mk lang (State.mk rs []) commit_tgt local)
      mem_k_tgt
.

Lemma sim_reorder_store_sim_stmts
      i1 l2 v2 o2
      (REORDER: reorder i1 (Instr.store l2 v2 o2)):
  sim_reorder_store i1 l2 v2 o2 <4= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
    eexists _, _. splits; eauto. econs; ss.
  - i. inv PR; ss.
    + eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
    + memtac. inv FUTURE_SRC0. memtac.
      exploit Memory.splits_join_inv; try apply SPLITS; eauto.
      i. des. subst. clear SPLITS.
      rewrite <- Memory.join_assoc in JOIN. symmetry in JOIN.
      exploit Memory.join2_splits; try apply JOIN; memtac.
      { splits; memtac.
        symmetry. eapply Memory.splits_disjoint; [|eauto].
        symmetry. eapply Memory.splits_disjoint; [|eauto].
        auto.
      }
      i. des. subst. clear JOIN SPLITSA.
      inv LOCAL. inv MEMORY. memtac.
      rewrite <- Memory.join_assoc in SPLITS.
      apply Memory.splits_join_inv2 in SPLITS; (repeat (splits; memtac)).
      exists (Memory.join (Memory.join local_tgt ohs1) ohs2). splits.
      * econs. rewrite Memory.join_assoc.
        apply Memory.splits_join; memtac.
        { rewrite <- Memory.join_assoc.
          apply Memory.splits_join; memtac. rewrite SPLITS.
          apply Memory.splits_join; memtac.
        }
        { splits; memtac.
          symmetry. eapply Memory.splits_disjoint_inv; [|eauto].
          memtac. splits; memtac.
          symmetry. eapply Memory.splits_disjoint_inv; [|eauto].
          memtac.
        }
      * rewrite <- Memory.join_assoc. econs; memtac.
        splits; memtac.
      * econs; try reflexivity. econs; memtac.
        splits; memtac.
        symmetry. eapply Memory.splits_disjoint_inv; [|eauto].
        memtac. splits; memtac.
        symmetry. eapply Memory.splits_disjoint_inv; [|eauto].
        memtac.
    + eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
  - i. inv PR; ss.
    + eexists _, _. splits; eauto.
    + subst. inv LOCAL. clear LE_TGT DISJOINT.
      rewrite Memory.join_comm, Memory.bot_join in LE_SRC.
      rewrite Memory.join_comm, Memory.bot_join.
      admit. (* phase 1; bot *)
    + eexists _, _. splits; eauto.
  - i. inv PR; ss.
    + (* phase 0 *)
      inv STEP_TGT.
      * admit. (* tgt i2 *)
      * inv STEP. ss. destruct th3_tgt. ss. subst.
        exploit MemInv.add; try apply MEM; eauto.
        { rewrite <- Memory.bot_join at 1. econs. memtac. }
        i. des. inv INV2. rewrite Memory.bot_join in *.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 2. econs; s; eauto. }
        { right. apply CIH. econs 1. auto. }
      * inv STATE. inv INSTR.
    + (* phase 1 *)
      inv STEP_TGT.
      * admit. (* tgt i1 *)
      * inv STEP. ss. destruct th3_tgt. ss. subst.
        exploit MemInv.add; try apply MEM; eauto.
        i. des. eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 2. econs; s; try reflexivity; eauto. }
        { right. apply CIH. econs 2; eauto.
          etransitivity; eauto.
        }
      * inv STATE. inv INSTR. inv REORDER.
    + (* phase 2 *)
      inv STEP_TGT.
      * inv STEP; inv STATE.
      * inv STEP. ss. destruct th3_tgt. ss. subst.
        exploit MemInv.add; try apply MEM; eauto.
        { rewrite <- Memory.bot_join at 1. econs. memtac. }
        i. des. inv INV2. rewrite Memory.bot_join in *.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 2. econs; s; eauto. }
        { right. apply CIH. econs 3. auto. }
      * inv STATE.
Admitted.

Lemma reorder_sim_stmts
      i1 i2 (REORDER: reorder i1 i2):
  sim_stmts eq
            [Stmt.instr i1; Stmt.instr i2]
            [Stmt.instr i2; Stmt.instr i1]
            eq.
Proof.
  ii. destruct i2; try by inv REORDER.
  - (* store *)
    eapply sim_reorder_store_sim_stmts; eauto.
    subst. econs 1. auto.
Qed.
