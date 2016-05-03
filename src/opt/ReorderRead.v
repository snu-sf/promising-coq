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

Inductive sim_read (loc:Loc.t) (val:Const.t) (ord:Ordering.t) (th_src th_tgt:Local.t) (mem_k_src mem_k_tgt:Memory.t): Prop :=
| sim_read_intro
    commit2_src to released
    (COMMIT1: Commit.read th_src.(Local.commit) loc to released ord commit2_src)
    (COMMIT2: Commit.le commit2_src th_tgt.(Local.commit))
    (PROMISE: MemInv.sem Memory.bot th_src.(Local.promise) th_tgt.(Local.promise))
    (GET1: Memory.get loc to mem_k_src = Some (Message.mk val released))
    (GET2: Memory.get loc to th_src.(Local.promise) = None)
.

Lemma sim_read_future
      loc val ord th_src th_tgt mem1_src mem1_tgt mem2_src mem2_tgt
      (SIM: sim_read loc val ord th_src th_tgt mem1_src mem1_tgt)
      (MEM_SRC: Memory.future mem1_src mem2_src)
      (MEM_TGT: Memory.future mem1_tgt mem2_tgt):
  sim_read loc val ord th_src th_tgt mem2_src mem2_tgt.
Proof.
  inv SIM. econs; eauto.
  eapply Memory.future_get; eauto.
Qed.

Lemma sim_read_begin
      loc to val released ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.read_step th1_tgt mem1_tgt loc to val released ord th2_tgt):
  sim_read loc val ord th1_src th2_tgt mem1_src mem1_tgt.
Proof.
  inv STEP_TGT. econs; eauto.
  - eapply CommitFacts.read_mon; eauto. apply LOCAL1.
  - reflexivity.
  - apply LOCAL1.
  - eapply Memory.splits_get; eauto. apply MEMORY1.
  - inv LOCAL1. apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
Qed.

Lemma sim_read_end
      loc val ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      (LOCAL1: sim_read loc val ord th1_src th1_tgt mem1_src mem1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt):
  exists to released th2_src,
    <<STEP_SRC: Local.read_step th1_src mem1_src loc to val released ord th2_src>> /\
    <<LOCAL2: sim_local th2_src th1_tgt>>.
Proof.
  inv LOCAL1.
  exploit CommitFacts.read_min_spec; eauto.
  { apply COMMIT1. }
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  i. des.
  eexists _, _, _. splits.
  - econs; eauto.
  - econs; ss. rewrite <- COMMIT2.
    eapply CommitFacts.read_min_min; eauto.
Qed.

Lemma sim_read_promise
      loc val ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOCAL1: sim_read loc val ord th1_src th1_tgt mem1_src mem1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.promise_step th1_tgt mem1_tgt th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.promise_step th1_src mem1_src th2_src mem2_src>> /\
    <<LOCAL2: sim_read loc val ord th2_src th2_tgt mem2_src mem2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit MemInv.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  i. des.
  eexists _, _. splits; eauto.
  - econs; eauto.
    + reflexivity.
    + eapply Commit.future_wf; eauto. apply WF1_SRC.
  - econs; s; eauto.
    + etransitivity; eauto.
    + eapply Memory.future_get; eauto.
    + admit. (* promise get None *)
Admitted.

Lemma sim_read_read
      loc1 val1 ord1
      loc2 ts2 val2 released2 ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.release)
      (LOCAL1: sim_read loc1 val1 ord1 th1_src th1_tgt mem1_src mem1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.read_step th1_tgt mem1_tgt loc2 ts2 val2 released2 ord2 th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.read_step th1_src mem1_src loc2 ts2 val2 released2 ord2 th2_src>> /\
    <<LOCAL2: sim_read loc1 val1 ord1 th2_src th2_tgt mem1_src mem1_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit Memory.splits_get; try apply GET; eauto.
  { apply MEMORY1. }
  intro GET2_SRC.
  exploit CommitFacts.read_min_spec; try apply GET2_SRC; eauto.
  { inv COMMIT. eapply Snapshot.readable_mon; eauto.
    etransitivity; [|apply COMMIT2]. apply COMMIT1.
  }
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  i. des.
  exploit CommitFacts.read_min_spec.
  { eapply Snapshot.le_on_readable; eauto. apply COMMIT1. }
  { apply WF1_SRC. }
  { eauto. }
  { eauto. }
  i. des.
  eexists. splits; eauto.
  - econs; eauto.
    apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
  - econs; eauto. s.
    admit. (* Commit.le *)
Admitted.

Lemma sim_read_write
      loc1 val1 ord1
      loc2 from2 to2 val2 released2 ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.sc ord2 -> Ordering.le Ordering.sc ord1 -> False)
      (LOCAL1: sim_read loc1 val1 ord1 th1_src th1_tgt mem1_src mem1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.write_step th1_tgt mem1_tgt loc2 from2 to2 val2 released2 ord2 th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.write_step th1_src mem1_src loc2 from2 to2 val2 released2 ord2 th2_src mem2_src>> /\
    <<LOCAL2: sim_read loc1 val1 ord1 th2_src th2_tgt mem2_src mem2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
Admitted.

Lemma sim_read_fence
      loc1 val1 ord1
      ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      (ORD2: Ordering.le ord2 Ordering.release)
      (LOCAL1: sim_read loc1 val1 ord1 th1_src th1_tgt mem1_src mem1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.fence_step th1_tgt mem1_tgt ord2 th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.fence_step th1_src mem1_src ord2 th2_src>> /\
    <<LOCAL2: sim_read loc1 val1 ord1 th2_src th2_tgt mem1_src mem1_tgt>>.
Proof.
Admitted.

Inductive reorder r2 l2 o2: forall (i1:Instr.t), Prop :=
| reorder_load
    r1 l1 o1
    (ORD1: Ordering.le o1 Ordering.release)
    (LOC: l2 <> l1)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder r2 l2 o2 (Instr.load r1 l1 o1)
| reorder_store
    l1 v1 o1
    (ORD: Ordering.le Ordering.sc o1 -> Ordering.le Ordering.sc o2 -> False)
    (LOC: l2 <> l1)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder r2 l2 o2 (Instr.store l1 v1 o1)
| reorder_update
    r1 l1 rmw1 o1
    (ORD1: Ordering.le o1 Ordering.release)
    (LOC: l2 <> l1)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder r2 l2 o2 (Instr.update r1 l1 rmw1 o1)
| reorder_fence
    o1
    (ORD1: Ordering.le o1 Ordering.release):
    reorder r2 l2 o2 (Instr.fence o1)
.

Inductive sim: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                 (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_begin
    i1 r2 l2 o2
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (REORDER: reorder r2 l2 o2 i1)
    (LOCAL: sim_local th_src th_tgt):
    sim
      (State.mk rs [Stmt.instr Instr.skip; Stmt.instr i1; Stmt.instr (Instr.load r2 l2 o2)]) th_src mem_k_src
      (State.mk rs [Stmt.instr (Instr.load r2 l2 o2); Stmt.instr i1]) th_tgt mem_k_tgt
| sim_end
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (LOCAL: sim_local th_src th_tgt):
    sim
      (State.mk rs []) th_src mem_k_src
      (State.mk rs []) th_tgt mem_k_tgt
| sim_intermediate
    i1 r2 l2 o2 v2
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (REORDER: reorder r2 l2 o2 i1)
    (LOCAL: sim_read l2 v2 o2 th_src th_tgt mem_k_src mem_k_tgt):
    sim
      (State.mk rs [Stmt.instr i1; Stmt.instr (Instr.load r2 l2 o2)]) th_src mem_k_src
      (State.mk (RegFun.add r2 v2 rs) [Stmt.instr i1]) th_tgt mem_k_tgt
.

Lemma sim_reorder_sim_stmts:
  sim <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
    eexists _, _, _. splits; eauto. econs; ss.
  - admit.
    (* future; https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L100 *)
  - i. inv PR.
    + inv LOCAL. apply MemInv.sem_bot_inv in PROMISE.
      eexists _, _, _. splits; eauto. etransitivity; eauto.
    + inv LOCAL. apply MemInv.sem_bot_inv in PROMISE.
      eexists _, _, _. splits; eauto. etransitivity; eauto.
    + inv LOCAL. apply MemInv.sem_bot_inv in PROMISE.
      eexists _, _, _. splits; eauto.
      rewrite PROMISE. auto.
  - i. inv PR; ss.
    + (* begin *)
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs. econs 1. eauto. }
        right. apply CIH. econs 1; ss.
      * (* load *)
        exploit sim_read_begin; eauto. i.
        eexists _, _, _, _, _, _. splits; try apply MEMORY; eauto.
        { econs. econs 6; ss.
          - econs. econs.
          - apply Local.fence_relaxed. ss.
        }
        right. apply CIH. econs 3; eauto.        
    + (* end *)
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
      exploit sim_local_promise; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      { econs. econs 1. eauto. }
      right. apply CIH. econs 2; ss.
    + (* intermediate *)
      exploit sim_read_future; eauto. i.
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inversion REORDER); subst; ss.
      * (* promise *)
        exploit sim_read_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs. econs 1. eauto. }
        right. apply CIH. econs 3; ss.
      * (* read *)
        exploit sim_read_read; eauto. i. des.
        exploit sim_read_end; eauto.
        { eapply Local.read_step_future; eauto. }
        { eapply Local.read_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 3; eauto. econs. econs.
        }
        { econs. econs 3; eauto. econs. econs. }
        { eauto. }
        right. apply CIH. rewrite IdentFun.add_add.
        { econs 2; eauto. }
        { admit. (* disjoint <> *) }
      * (* write *)
        exploit sim_read_write; eauto. i. des.
        exploit sim_read_end; eauto.
        { eapply Local.write_step_future; eauto. }
        { eapply Local.write_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 4; s; eauto.
          econs. erewrite RegFile.eq_except_value; eauto.
          - econs.
          - admit.
          - apply RegFile.eq_except_singleton.
        }
        { econs. econs 3; eauto. econs. econs. }
        { eauto. }
        right. apply CIH. econs 2; eauto.
      * (* update *)
        exploit sim_read_read; eauto. i. des.
        exploit sim_read_write; eauto.
        { destruct ord; ss. }
        { eapply Local.read_step_future; eauto. }
        { eapply Local.read_step_future; eauto. }
        i. des.
        exploit sim_read_end; eauto.
        { eapply Local.write_step_future; eauto.
          eapply Local.read_step_future; eauto.
        }
        { eapply Local.write_step_future; eauto.
          eapply Local.read_step_future; eauto.
        }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 5; s; eauto.
          econs. econs.
          erewrite <- RegFile.eq_except_rmw; eauto.
          - admit. (* reg disjoint *)
          - apply RegFile.eq_except_singleton.
        }
        { econs. econs 3; eauto. econs. econs. }
        { eauto. }
        right. apply CIH. rewrite IdentFun.add_add.
        { econs 2; eauto. }
        { admit. (* disjoint <> *) }
      * (* fence *)
        exploit sim_read_fence; eauto. i. des.
        exploit sim_read_end; eauto.
        { eapply Local.fence_step_future; eauto. }
        { eapply Local.fence_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 6; eauto. econs. econs.
        }
        { econs. econs 3; eauto. econs. econs. }
        { eauto. }
        right. apply CIH. econs 2; eauto.
Admitted.

Lemma reorder_sim_stmts
      i1 r2 v2 o2 (REORDER: reorder r2 v2 o2 i1):
  sim_stmts eq
            [Stmt.instr Instr.skip; Stmt.instr i1; Stmt.instr (Instr.load r2 v2 o2)]
            [Stmt.instr (Instr.load r2 v2 o2); Stmt.instr i1]
            eq.
Proof.
  ii. subst.
  eapply sim_reorder_sim_stmts; eauto. econs 1; auto.
Qed.
