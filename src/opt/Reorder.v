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

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)

Inductive reorder: forall (i1 i2:Instr.t), Prop :=
| reorder_load_store
    r1 l1
    l2 v2
    (LOC: l1 <> l2)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 Ordering.relaxed))
                               (Instr.regs_of (Instr.store l2 v2 Ordering.relaxed))):
    reorder (Instr.load r1 l1 Ordering.relaxed) (Instr.store l2 v2 Ordering.relaxed)
.

Inductive sim_reorder (i1:Instr.t) (l2:Loc.t) (v2:Value.t) (o2:Ordering.t):
  forall (th_src:Thread.t lang) (mem_k_src:Memory.t)
    (th_tgt:Thread.t lang) (mem_k_tgt:Memory.t), Prop :=
| sim_reorder_phase0
    rs
    commit_src commit_tgt
    promise
    mem_k_src mem_k_tgt
    (COMMIT: Commit.le commit_src commit_tgt):
    sim_reorder
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs [Stmt.instr Instr.nop; Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) commit_src promise)
      mem_k_src
      (Thread.mk lang (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr i1]) commit_tgt promise)
      mem_k_tgt
| sim_reorder_phase1
    rs
    commit_src commit_tgt commit_imm
    promise_src promise_tgt
    mem_k_src mem_k_tgt
    from to released
    (COMMIT1: Commit.write commit_src l2 to released Ordering.relaxed commit_imm)
    (COMMIT2: Commit.le commit_imm commit_tgt)
    (LT: Time.lt from to)
    (PROMISE: MemInv.sem (Memory.singleton l2 (Message.mk (RegFile.eval_value rs v2) released) LT) promise_src promise_tgt):
    sim_reorder
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs [Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) commit_src promise_src)
      mem_k_src
      (Thread.mk lang (State.mk rs [Stmt.instr i1]) commit_tgt promise_tgt)
      mem_k_tgt
| sim_reorder_phase2
    rs
    commit_src commit_tgt
    promise
    mem_k_src mem_k_tgt
    (COMMIT: Commit.le commit_src commit_tgt):
    sim_reorder
      i1 l2 v2 o2
      (Thread.mk lang (State.mk rs []) commit_src promise)
      mem_k_src
      (Thread.mk lang (State.mk rs []) commit_tgt promise)
      mem_k_tgt
.

Lemma sim_reorder_sim_stmts
      i1 l2 v2 o2
      (REORDER: reorder i1 (Instr.store l2 v2 o2)):
  sim_reorder i1 l2 v2 o2 <4= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
    eexists _, _. splits; eauto. econs; ss.
  - i.
    assert (F: Memory.future mem1_tgt mem2_src).
    { etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto. }
    inv PR; ss.
    + i. eexists. splits; try reflexivity; eauto.
      inv WF_SRC0. inv WF_TGT. econs; ss. eapply Commit.future_wf; eauto.
    + i. eexists. splits; try reflexivity; eauto.
      inv WF_SRC0. inv WF_TGT. econs; ss.
      * eapply Commit.future_wf; eauto.
      * rewrite <- PROMISE0. inv PROMISE. apply Memory.le_join_l. memtac.
    + i. eexists. splits; try reflexivity; eauto.
      inv WF_SRC0. inv WF_TGT. econs; ss. eapply Commit.future_wf; eauto.
  - i. inv PR; ss.
    + eexists _, _. splits; eauto.
    + inv REORDER.
      exploit MemInv.confirm_src; try apply MEMORY; eauto.
      { econs.
        - rewrite Memory.join_comm, Memory.bot_join. eauto.
        - memtac.
      }
      i. des. apply MemInv.sem_bot_inv in INV. subst.
      exploit (CommitFacts.wf_get l1); try apply WF_SRC; eauto.
      s. i. des. destruct msg.
      exploit Memory.confirm_get; eauto. i.
      exploit Memory.le_get; try apply WF_SRC; eauto. i.
      exploit (@CommitFacts.read_min_spec l1); try apply x0; eauto.
      { econs. unfold Times.get, LocFun.find. reflexivity.  }
      { apply WF_SRC. }
      i. des.
      exploit (@CommitFacts.write_min_spec l2); try apply MEMORY_SRC; eauto.
      { instantiate (1 := Ordering.relaxed). ss. }
      { eapply Snapshot.le_on_writable; eauto. apply COMMIT1. }
      { ss. inv COMMIT1. etransitivity; [apply MONOTONE|apply RELEASED]. }
      { inv MEMORY_SRC. exploit WF0; eauto. }
      i. des. simpl in WRITE.
      eexists _, _. splits.
      * econs 2; [|econs 2; [|econs 1]].
        { econs. s. instantiate (1 := (_, _)).
          econs 1; s; eauto.
          - econs. econs.
          - inv CONFIRM. rewrite Memory.join_comm, Memory.bot_join.
            match goal with
            | [|- ?x = None] => destruct x eqn:X; auto
            end.
            apply Memory.singleton_get_inv in X. des. congruence.
        }
        { econs. s. econs 2; s; eauto.
          - econs. econs.
          - econs 1; ss.
            erewrite RegFile.eq_except_value; eauto.
            apply RegFile.eq_except_singleton.
        }
      * eauto.
      * s. eauto.
    + eexists _, _. splits; eauto.
  - i. inv STEP_TGT; [|inv STATE; inv INSTR; inv PR; inv REORDER].
    inv STEP.
    + (* read, phase 2 *)
      inv STATE. destruct x2. ss. subst. inv INSTR. inv REORDER. inv PR.
      exploit MemInv.confirm_src; try apply MEMORY; eauto.
      { econs.
        - rewrite Memory.join_comm, Memory.bot_join. eauto.
        - memtac.
      }
      i. des. apply MemInv.sem_bot_inv in INV. subst.
      exploit Memory.splits_get; eauto.
      { inv MEMORY. eauto. }
      intro GET_SRC.
      exploit Memory.confirm_get; eauto. i.
      exploit Memory.le_get; try apply WF_SRC; eauto. i.
      exploit CommitFacts.read_min_spec; try apply GET_SRC; eauto.
      { eapply Snapshot.readable_mon; [|apply COMMIT].
        etransitivity; [|apply COMMIT2]. apply COMMIT1.
      }
      { apply WF_SRC. }
      i. des.
      exploit CommitFacts.write_min_spec; try apply MEMORY_SRC; eauto.
      { instantiate (1 := Ordering.relaxed). ss. }
      { eapply Snapshot.le_on_writable; eauto. apply COMMIT1. }
      { ss. inv COMMIT1. etransitivity; [apply MONOTONE|apply RELEASED]. }
      { inv MEMORY_SRC. exploit WF0; eauto. }
      i. des.
      eexists _, _, _, _. splits.
      { econs 2; [|econs 1].
        econs 1. s. econs 1; s; eauto.
        - econs. econs.
        - inv CONFIRM.
          match goal with
          | [|- ?m = None] => destruct m eqn:X; auto
          end.
          apply Memory.join_get in X; ss. des; [congruence|].
          apply Memory.singleton_get_inv in X. des. subst. congruence.
      }
      { econs 1. s. econs 2; s; eauto.
        - econs. econs.
        - econs 1; ss. erewrite RegFile.eq_except_value; eauto.
          apply RegFile.eq_except_singleton.
      }
      { auto. }
      { right. apply CIH. econs 3.
        exploit CommitFacts.write_min_min; try apply COMMIT1; eauto. i.
        exploit CommitFacts.read_min_min; try apply COMMIT; eauto. i.
        inv x4. inv x5. inv CURRENT1. inv CURRENT2. ss. econs; s.
        - econs; ss.
          + etransitivity; [|eauto].
            apply Times.incr_mon. etransitivity; [|apply COMMIT2]. apply COMMIT1.
          + etransitivity; eauto. etransitivity; eauto. apply COMMIT2.
        - i. etransitivity; eauto. etransitivity; eauto. apply COMMIT2.
        - etransitivity; eauto.
          apply Snapshot.join_spec.
          + apply Snapshot.join_l.
          + etransitivity; [|apply Snapshot.join_r].
            etransitivity; [|apply COMMIT2]. apply COMMIT1.
      }
    + (* write, phase 1 *)
      inv STATE. destruct x2. ss. subst. inv INSTR. inv REORDER. inv PR.
      inv MEMORY0.
      * exploit MemInv.confirm; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply MemInv.sem_bot. }
        s. i. des.
        eexists _, _, _, _. splits; eauto.
        { econs 1. s. econs 5; s.
          - econs. econs.
          - reflexivity.
          - apply WF_SRC.
        }
        { inv CONFIRM; ss. right. apply CIH. econs 2; eauto.
          - eauto. eapply CommitFacts.write_mon; eauto.
          - reflexivity.
          - econs. memtac.
        }
      * exploit MemInv.add; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply MemInv.sem_bot. }
        s. i. des. rewrite Memory.join_comm, Memory.bot_join in INV2.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 1. s. econs 5; s.
          - econs. econs.
          - reflexivity.
          - apply WF_SRC.
        }
        { econs 1. econs 6; eauto.
          inv WF_TGT. eapply Commit.future_wf; eauto.
          etransitivity; eauto. inv MEMORY. apply Memory.splits_future. auto.
        }
        { auto. }
        ss. right. apply CIH. econs 2; eauto. reflexivity.
    + inv STATE; destruct x2; ss; subst; try inv INSTR; inv PR; inv REORDER.
    + inv STATE; destruct x2; ss; subst; try inv INSTR; inv PR; inv REORDER.
    + inv STATE; destruct x2; ss; subst; try inv INSTR; inv PR; inv REORDER.
    + inv PR; ss.
      * exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply MemInv.sem_bot. }
        s. i. des. apply MemInv.sem_bot_inv in INV2. subst.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 1. econs 6; s; eauto.
          inv WF_TGT. eapply Commit.future_wf; eauto.
          etransitivity; eauto. inv MEMORY. apply Memory.splits_future. auto.
        }
        { right. apply CIH. econs 1. auto. }
      * exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        s. i. des.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 1.
          econs 6; s; try reflexivity; eauto.
          inv WF_SRC. eapply Commit.future_wf; eauto.
        }
        { right. apply CIH. econs 2; eauto. etransitivity; eauto. }
      * exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply MemInv.sem_bot. }
        s. i. des. apply MemInv.sem_bot_inv in INV2. subst.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _). econs 1. econs 6; s; eauto.
          inv WF_TGT. eapply Commit.future_wf; eauto.
          etransitivity; eauto. inv MEMORY. apply Memory.splits_future. auto.
        }
        { right. apply CIH. econs 3. auto. }
Qed.

Lemma reorder_sim_stmts
      i1 i2 (REORDER: reorder i1 i2):
  sim_stmts eq
            [Stmt.instr Instr.nop; Stmt.instr i1; Stmt.instr i2]
            [Stmt.instr i2; Stmt.instr i1]
            eq.
Proof.
  ii. destruct i2; try by inv REORDER.
  - (* store *)
    eapply sim_reorder_sim_stmts; eauto.
    subst. econs 1. auto.
Qed.
