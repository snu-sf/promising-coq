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

Inductive sim_write (loc:Loc.t) (val:Const.t) (ord:Ordering.t) (th_src th_tgt:Local.t): Prop :=
| sim_write_intro
    commit2_src from to released
    (COMMIT1: Commit.write th_src.(Local.commit) loc to released ord commit2_src)
    (COMMIT2: Commit.le commit2_src th_tgt.(Local.commit))
    (LT: Time.lt from to)
    (PROMISE: MemInv.sem (Memory.singleton loc (Message.mk val released) LT) th_src.(Local.promise) th_tgt.(Local.promise))
.

Lemma sim_write_begin
      loc val ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.memory_step th1_tgt mem1_tgt (MemEvent.write loc val ord) th2_tgt mem2_tgt):
  (<<LOCAL2: sim_write loc val ord th1_src th2_tgt>> /\
   <<MEMORY2: sim_memory mem1_src mem2_tgt>>) \/
  (exists th2_src mem2_src,
      <<STEP_SRC: Local.promise_step th1_src mem1_src th2_src mem2_src>> /\
      <<LOCAL2: sim_write loc val ord th2_src th2_tgt>> /\
      <<MEMORY2: sim_memory mem2_src mem2_tgt>>).
Proof.
  inv STEP_TGT. inv MEMORY.
  - left. splits; auto.
    inversion LOCAL1. apply MemInv.sem_bot_inv in PROMISE.
    destruct th1_src, th1_tgt. ss. subst.
    inv CONFIRM.
    econs; s.
    + eapply CommitFacts.write_mon; eauto.
    + reflexivity.
    + econs. memtac.
  - right. inv ADD.
    exploit MemInv.promise; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { apply LOCAL1. }
    i. des.
    apply MemInv.sem_bot_inv in INV2. subst.
    exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
    { apply WF1_SRC. }
    { apply WF1_SRC. }
    i. des.
    eexists _, _. splits.
    + econs; try apply PROMISE_SRC; eauto.
      * reflexivity.
      * eapply Commit.future_wf; eauto. apply WF1_SRC.
    + inversion LOCAL1. apply MemInv.sem_bot_inv in PROMISE0.
      destruct th1_src, th1_tgt. ss. subst.
      inv CONFIRM.
      econs; s.
      * eapply CommitFacts.write_mon; eauto.
      * reflexivity.
      * econs. memtac.
    + auto.
Qed.

Lemma sim_write_end
      loc val ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      (ORD: Ordering.le ord Ordering.relaxed)
      (LOCAL1: sim_write loc val ord th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.memory_step th1_src mem1_src (MemEvent.write loc val ord) th2_src mem2_src>> /\
    <<LOCAL2: sim_local th2_src th1_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem1_tgt>>.
Proof.
  destruct (Ordering.le Ordering.release ord) eqn:ORD2.
  { destruct ord; ss. }
  inv LOCAL1. inversion COMMIT1.
  exploit Memory.le_get.
  { apply WF1_SRC. }
  { inv PROMISE. eapply Memory.le_get.
    - apply Memory.le_join_r. memtac.
    - apply Memory.singleton_get.
  }
  intro GET_SRC.
  exploit CommitFacts.write_min_spec; eauto.
  { instantiate (1 := ord). unfold CommitFacts.write_min.
    rewrite ORD2. ss. etransitivity; [apply MONOTONE|apply RELEASED].
  }
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  { inv WF1_SRC. inv MEMORY. exploit WF; eauto. }
  i. des.
  eexists _, _. splits; eauto.
  - econs; eauto. econs 1.
    + inv PROMISE. econs; ss.
    + rewrite ORD2. ss.
  - econs; ss.
    + rewrite <- COMMIT2. eapply CommitFacts.write_min_min. eauto.
    + apply MemInv.sem_bot.
Qed.

Lemma sim_local_promise
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.promise_step th1_tgt mem1_tgt th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.promise_step th1_src mem1_src th2_src mem2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>> /\
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
  - econs; try apply PROMISE_SRC.
    + reflexivity.
    + eapply Commit.future_wf; [|eauto]. apply WF1_SRC.
  - econs; s; eauto. etransitivity; eauto.
Qed.

Lemma sim_write_promise
      loc val ord
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (ORD: Ordering.le ord Ordering.relaxed)
      (LOCAL1: sim_write loc val ord th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.promise_step th1_tgt mem1_tgt th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.promise_step th1_src mem1_src th2_src mem2_src>> /\
    <<LOCAL2: sim_write loc val ord th2_src th2_tgt>> /\
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
  - econs; s; eauto. etransitivity; eauto.
Qed.

Lemma sim_write_read
      loc1 val1 ord1
      loc2 val2 ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (LOCAL1: sim_write loc1 val1 ord1 th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.memory_step th1_tgt mem1_tgt (MemEvent.read loc2 val2 ord2) th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.memory_step th1_src mem1_src (MemEvent.read loc2 val2 ord2) th2_src mem2_src>> /\
    <<LOCAL2: sim_write loc1 val1 ord1 th2_src th2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit Memory.le_get.
  { apply WF1_SRC. }
  { inv PROMISE. eapply Memory.le_get.
    - apply Memory.le_join_r. memtac.
    - apply Memory.singleton_get.
  }
  intro GET1_SRC.
  exploit Memory.splits_get; try apply GET; eauto.
  { inv MEMORY1. eauto. }
  intro GET2_SRC.
  exploit CommitFacts.read_min_spec; try apply GET2_SRC; eauto.
  { inv COMMIT. eapply Snapshot.readable_mon; eauto.
    etransitivity; [|apply COMMIT2]. apply COMMIT1.
  }
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  i. des.
  destruct (Ordering.le Ordering.release ord1) eqn:ORD1'.
  { destruct ord1; ss. }
  assert (RELEASED_SRC: Memory.wf_snapshot released mem1_src).
  { inv WF1_SRC. inv MEMORY. exploit WF0; try apply GET1_SRC; eauto. }
  exploit CommitFacts.write_min_spec; try apply RELEASED_SRC; eauto.
  { eapply Snapshot.le_on_writable; eauto. apply COMMIT1. }
  { instantiate (1 := ord1).
    unfold CommitFacts.write_min. rewrite ORD1'. ss.
    inv COMMIT1. etransitivity; [apply MONOTONE|apply RELEASED].
  }
  { apply WF1_SRC. }
  i. des.
  eexists _, _. splits; eauto.
  - econs; eauto. inv PROMISE.
    match goal with
    | [|- ?x = None] => destruct x eqn:X; auto
    end.
    apply Memory.join_get in X; memtac; try congruence.
    apply Memory.singleton_get_inv in X. des. congruence.
  - econs; s; eauto.
    exploit CommitFacts.write_min_min; try apply COMMIT1; eauto. i.
    exploit CommitFacts.read_min_min; try apply COMMIT; eauto. i.
    inv x0. inv x1. inv CURRENT1. inv CURRENT2. econs.
    + econs; ss.
      * etransitivity; [|eauto].
        apply Times.incr_mon. etransitivity; [|apply COMMIT2]. apply COMMIT1.
      * etransitivity; eauto. etransitivity; eauto. apply COMMIT2.
    + i. etransitivity; eauto.
      unfold CommitFacts.write_min. rewrite ORD1'. ss.
      etransitivity; eauto; [|apply COMMIT2]. apply COMMIT1.
    + etransitivity; eauto.
      apply Snapshot.join_spec.
      * apply Snapshot.join_l.
      * etransitivity; [|apply Snapshot.join_r].
        etransitivity; [|apply COMMIT2]. apply COMMIT1.
Qed.

Lemma sim_write_write
      loc1 val1 ord1
      loc2 val2 ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (LOCAL1: sim_write loc1 val1 ord1 th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.memory_step th1_tgt mem1_tgt (MemEvent.write loc2 val2 ord2) th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.memory_step th1_src mem1_src (MemEvent.write loc2 val2 ord2) th2_src mem2_src>> /\
    <<LOCAL2: sim_write loc1 val1 ord1 th2_src th2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
Admitted.

Lemma sim_write_update
      loc1 val1 ord1
      loc2 val21 val22 ord2
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.release)
      (LOCAL1: sim_write loc1 val1 ord1 th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.memory_step th1_tgt mem1_tgt (MemEvent.update loc2 val21 val22 ord2) th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.memory_step th1_src mem1_src (MemEvent.update loc2 val21 val22 ord2) th2_src mem2_src>> /\
    <<LOCAL2: sim_write loc1 val1 ord1 th2_src th2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
Admitted.

Inductive reorder l2 v2 o2: forall (i1:Instr.t), Prop :=
| reorder_load
    r1 l1 o1
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l2 <> l1)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                               (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder l2 v2 o2 (Instr.load r1 l1 o1)
| reorder_store
    l1 v1 o1
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l2 <> l1)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                               (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder l2 v2 o2 (Instr.store l1 v1 o1)
| reorder_update
    r1 l1 rmw1 o1
    (ORD1: Ordering.le o1 Ordering.release)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l2 <> l1)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 o1))
                               (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder l2 v2 o2 (Instr.update r1 l1 rmw1 o1)
.

Inductive sim: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                 (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_begin
    i1 l2 v2 o2
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (REORDER: reorder l2 v2 o2 i1)
    (LOCAL: sim_local th_src th_tgt):
    sim
      (State.mk rs [Stmt.instr Instr.skip; Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) th_src mem_k_src
      (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr i1]) th_tgt mem_k_tgt
| sim_end
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (LOCAL: sim_local th_src th_tgt):
    sim
      (State.mk rs []) th_src mem_k_src
      (State.mk rs []) th_tgt mem_k_tgt
| sim_intermediate
    i1 l2 v2 o2
    rs th_src th_tgt
    mem_k_src mem_k_tgt
    (REORDER: reorder l2 v2 o2 i1)
    (LOCAL: sim_write l2 (RegFile.eval_value rs v2) o2 th_src th_tgt):
    sim
      (State.mk rs [Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]) th_src mem_k_src
      (State.mk rs [Stmt.instr i1]) th_tgt mem_k_tgt
.

Lemma Memory_write_bot
      mem1 loc from to msg ord promise2 mem2
      (WRITE: Memory.write Memory.bot mem1 loc from to msg ord promise2 mem2):
  promise2 = Memory.bot.
Proof.
Admitted.

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
    + inv REORDER.
      * assert (STEP: exists val th2_tgt mem2_tgt,
                   Local.memory_step x4 mem1_tgt (MemEvent.read l1 val o1) th2_tgt mem2_tgt).
        { admit.
          (* https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L116 *)
        }
        des.
        exploit sim_write_read; try apply LOCAL; try apply STEP; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _. splits.
        { econs 2; [|econs 2; [|econs 1]].
          - econs 3; eauto. econs. econs.
          - econs 3; eauto. econs.
            erewrite <- RegFile.eq_except_value; eauto.
            + econs.
            + apply RegFile.eq_except_singleton.
        }
        inv LOCAL0. apply MemInv.sem_bot_inv in PROMISE.
        etransitivity; eauto.
        inv STEP. ss.
      * assert (STEP: exists th2_tgt mem2_tgt,
                   Local.memory_step x4 mem1_tgt (MemEvent.write l1 (RegFile.eval_value rs v1) o1) th2_tgt mem2_tgt).
        { admit. }
        des.
        exploit sim_write_write; try apply LOCAL; try apply STEP; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _. splits.
        { econs 2; [|econs 2; [|econs 1]].
          - econs 3; eauto. econs. econs.
          - econs 3; eauto. econs. econs.
        }
        inv LOCAL0. apply MemInv.sem_bot_inv in PROMISE.
        etransitivity; eauto.
        inv STEP. ss.
        rewrite PROMISE_TGT in *. eapply Memory_write_bot. eauto.
      * assert (STEP: exists old new th2_tgt mem2_tgt,
           <<STEP: Local.memory_step x4 mem1_tgt (MemEvent.update l1 old new o1) th2_tgt mem2_tgt>> /\
           <<RMW: RegFile.eval_rmw rs rmw1 old new>>).
        { admit. }
        des.
        exploit sim_write_update; try apply LOCAL; try apply STEP0; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _. splits.
        { econs 2; [|econs 2; [|econs 1]].
          - econs 3; eauto. econs. econs. auto.
          - econs 3; eauto. econs.
            erewrite <- RegFile.eq_except_value; eauto.
            + econs.
            + admit. (* regfile disjoint *)
        }
        inv LOCAL0. apply MemInv.sem_bot_inv in PROMISE.
        etransitivity; eauto.
        inv STEP0. ss.
        rewrite PROMISE_TGT in *. eapply Memory_write_bot. eauto.
  - i. inv PR; ss.
    + (* begin *)
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
      * exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs. econs 1. eauto. }
        right. apply CIH. econs 1; ss.
      * exploit sim_write_begin; eauto. i. des.
        { eexists _, _, _, _, _, _. splits; try apply MEMORY2; eauto.
          { econs. econs 3; ss.
            - econs. econs.
            - apply Local.fence_relaxed. ss.
          }
          right. apply CIH. econs 3; eauto.
        }
        { eexists _, _, _, _, _, _. splits; try apply MEMORY2.
          { econs 2; [|econs 1].
            econs 3; ss.
            - econs. econs.
            - apply Local.fence_relaxed. ss.
          }
          { econs. econs 1; eauto. }
          right. apply CIH. econs 3; eauto.
        }
    + (* end *)
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
      exploit sim_local_promise; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      { econs. econs 1. eauto. }
      right. apply CIH. econs 2; ss.
    + (* intermediate *)
      inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inversion REORDER); subst; ss.
      * exploit sim_write_promise; eauto.
        { inv REORDER; ss. }
        i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs. econs 1. eauto. }
        right. apply CIH. econs 3; ss.
      * exploit sim_write_read; try apply LOCAL; try apply STEP0; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 3; eauto. econs. econs.
        }
        { econs. econs 3; eauto. econs.
          erewrite <- RegFile.eq_except_value; eauto.
          - econs.
          - apply RegFile.eq_except_singleton.
        }
        { eauto. }
        right. apply CIH. econs 2; eauto.
      * exploit sim_write_write; try apply LOCAL; try apply STEP; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 3; eauto. econs. econs.
        }
        { econs. econs 3; eauto. econs. econs. }
        { eauto. }
        right. apply CIH. econs 2; eauto.
      * exploit sim_write_update; try apply LOCAL; try apply STEP0; eauto. i. des.
        exploit sim_write_end; eauto.
        { eapply Local.memory_step_future; eauto. }
        { eapply Local.memory_step_future; eauto. }
        i. des.
        eexists _, _, _, _, _, _. splits.
        { econs 2; [|econs 1].
          econs 3; eauto. econs. econs. auto.
        }
        { econs. econs 3; eauto. econs.
          erewrite <- RegFile.eq_except_value; eauto.
          - econs.
          - admit. (* regfile disjoint *)
        }
        { eauto. }
        right. apply CIH. econs 2; eauto.
Admitted.

Lemma reorder_sim_stmts
      i1 l2 v2 o2 (REORDER: reorder l2 v2 o2 i1):
  sim_stmts eq
            [Stmt.instr Instr.skip; Stmt.instr i1; Stmt.instr (Instr.store l2 v2 o2)]
            [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr i1]
            eq.
Proof.
  ii. subst.
  eapply sim_reorder_sim_stmts; eauto. econs 1; auto.
Qed.
