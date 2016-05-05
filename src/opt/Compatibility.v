Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful7.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Simulation.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

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

Lemma sim_local_silent
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.silent_step th1_tgt mem1_tgt th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.silent_step th1_src mem1_src th2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  eexists. splits.
  - econs.
    + etransitivity; eauto.
    + eapply Commit.future_wf; eauto.
      apply Memory.splits_future. apply MEMORY1.
  - econs; eauto. s. reflexivity.
Qed.

Lemma sim_local_read
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      loc ts val released ord
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.read_step th1_tgt mem1_tgt loc ts val released ord th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.read_step th1_src mem1_src loc ts val released ord th2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit Memory.splits_get; try apply MEMORY1; eauto. i.
  exploit MemInv.sem_bot_inv; eauto. i.
  eexists. splits.
  - econs; eauto.
    + eapply CommitFacts.read_mon; eauto.
    + eapply Commit.future_wf; eauto.
      apply Memory.splits_future. apply MEMORY1.
    + rewrite x1. auto.
  - econs; eauto. s. reflexivity.
Qed.

Lemma sim_local_fulfill
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      loc from to val released ord
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.fulfill_step th1_tgt mem1_tgt loc from to val released ord th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.fulfill_step th1_src mem1_src loc from to val released ord th2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit MemInv.fulfill; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  eexists. splits; eauto.
  - econs; eauto.
    + eapply CommitFacts.write_mon; eauto.
    + eapply Commit.future_wf; eauto.
      apply Memory.splits_future. apply MEMORY1.
    + apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
  - econs; eauto. s. reflexivity.
Qed.

Lemma sim_local_write
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt mem2_tgt
      loc from to val released ord
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.write_step th1_tgt mem1_tgt loc from to val released ord th2_tgt mem2_tgt):
  exists th2_src mem2_src,
    <<STEP_SRC: Local.write_step th1_src mem1_src loc from to val released ord th2_src mem2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>> /\
    <<MEMORY2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv STEP_TGT.
  - exploit sim_local_fulfill; eauto. i. des.
    eexists _, _. splits; eauto. econs 1. eauto.
  - inv LOCAL1. inv ADD.
    exploit Memory.promise_future; eauto.
    { apply WF1_TGT. }
    { apply WF1_TGT. }
    i. des.
    exploit MemInv.promise; try apply MEMORY1; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    i. des.
    exploit MemInv.fulfill; try apply SIM2; eauto. i. des.
    eexists _, _. splits; eauto.
    + econs 2. econs; eauto.
      * eapply CommitFacts.write_mon; eauto.
      * eapply Commit.future_wf; eauto.
        apply Memory.splits_future. apply SIM2.
      * apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
    + econs; eauto. s. reflexivity.
Qed.

Lemma sim_local_fence
      th1_src mem1_src
      th1_tgt mem1_tgt
      th2_tgt
      ord
      (LOCAL1: sim_local th1_src th1_tgt)
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf th1_src mem1_src)
      (WF1_TGT: Local.wf th1_tgt mem1_tgt)
      (STEP_TGT: Local.fence_step th1_tgt mem1_tgt ord th2_tgt):
  exists th2_src,
    <<STEP_SRC: Local.fence_step th1_src mem1_src ord th2_src>> /\
    <<LOCAL2: sim_local th2_src th2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  eexists. splits.
  - econs.
    + eapply CommitFacts.fence_mon; eauto.
    + eapply Commit.future_wf; eauto.
      apply Memory.splits_future. apply MEMORY1.
    + apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
  - econs; eauto. s. reflexivity.
Qed.

Definition SIM_REGS := forall (rs_src rs_tgt:RegFile.t), Prop.

Inductive sim_terminal
          (sim_regs:SIM_REGS)
          (st_src:lang.(Language.state)) (st_tgt:lang.(Language.state)): Prop :=
| sim_terminal_intro
    (REGS: sim_regs st_src.(State.regs) st_tgt.(State.regs))
.

Definition sim_expr
           (sim_regs:SIM_REGS)
           e_src e_tgt :=
  forall rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
    RegFile.eval_expr rs_src e_src = RegFile.eval_expr rs_tgt e_tgt.

Definition _sim_stmts
           (sim_thread:SIM_THREAD lang lang)
           (sim_regs0:SIM_REGS)
           (stmts_src stmts_tgt:list Stmt.t)
           (sim_regs1:SIM_REGS): Prop :=
  forall rs_src rs_tgt th_src th_tgt mem_k_src mem_k_tgt
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local th_src th_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (State.mk rs_src stmts_src) th_src mem_k_src
      (State.mk rs_tgt stmts_tgt) th_tgt mem_k_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <7= s2):
  _sim_stmts s1 <4= _sim_stmts s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma lang_step_seq
      stmts rs1 stmts1 rs2 stmts2 e
      (STEP: State.step (State.mk rs1 stmts1) e
                        (State.mk rs2 stmts2)):
  State.step (State.mk rs1 (stmts1 ++ stmts)) e
             (State.mk rs2 (stmts2 ++ stmts)).
Proof.
  inv STEP.
  - econs 1. auto.
  - s. rewrite <- app_assoc. econs 2.
  - s. rewrite <- app_assoc. econs 3.
Qed.

Lemma lang_step_deseq
      stmts rs1 stmt1 stmts1 rs2 stmts2 e
      (STEP: State.step (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) e
                        (State.mk rs2 stmts2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
    State.step (State.mk rs1 (stmt1 :: stmts1)) e
               (State.mk rs2 stmts2').
Proof.
  inv STEP.
  - eexists. splits; eauto. econs 1. auto.
  - eexists. rewrite app_assoc. splits; eauto. econs 2.
  - eexists. rewrite app_comm_cons, app_assoc. splits; eauto. econs 3.
Qed.

Lemma internal_step_seq
      stmts
      rs1 stmts1 th1 mem1
      rs2 stmts2 th2 mem2
      (STEP: Thread.internal_step
               (Thread.mk lang (State.mk rs1 stmts1) th1 mem1)
               (Thread.mk lang (State.mk rs2 stmts2) th2 mem2)):
  Thread.internal_step
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) th1 mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) th2 mem2).
Proof.
  inv STEP; ss.
  - econs 1; s; eauto.
  - econs 2; s; eauto. apply lang_step_seq. auto.
  - econs 3; s; eauto. apply lang_step_seq. auto.
  - econs 4; s; eauto. apply lang_step_seq. auto.
  - econs 5; s; eauto. apply lang_step_seq. auto.
  - econs 6; s; eauto. apply lang_step_seq. auto.
Qed.

Lemma step_seq
      stmts e
      rs1 stmts1 th1 mem1
      rs2 stmts2 th2 mem2
      (STEP: Thread.step
               (Thread.mk lang (State.mk rs1 stmts1) th1 mem1) e
               (Thread.mk lang (State.mk rs2 stmts2) th2 mem2)):
  Thread.step
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) th1 mem1) e
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) th2 mem2).
Proof.
  inv STEP; ss.
  - econs 1. apply internal_step_seq. auto.
  - econs 2. inv STEP0. econs; ss. apply lang_step_seq. auto.
Qed.

Lemma thread_step_deseq
      stmts e
      rs1 stmt1 stmts1 th1 mem1
      rs2 stmts2 th2 mem2
      (STEP: Thread.step
               (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) th1 mem1) e
               (Thread.mk lang (State.mk rs2 stmts2) th2 mem2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step
    (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) th1 mem1) e
    (Thread.mk lang (State.mk rs2 stmts2') th2 mem2).
Proof.
  inv STEP.
  - inv STEP0; ss.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 1. econs 1; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 2; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 3; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 4; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 5; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 6; s; eauto.
  - inv STEP0. ss.
    apply lang_step_deseq in STATE. des. subst.
    eexists. splits; eauto.
    econs 2. econs; s; eauto.
Qed.

Lemma sim_rtc
      A B
      (sim:A -> B -> Prop)
      (rA:A -> A -> Prop)
      (rB:B -> B -> Prop)
      (SIM:
         forall a1 a2 b1 (RA: rA a1 a2) (SIM1: sim a1 b1),
         exists b2, rB b1 b2 /\ sim a2 b2)
      a1 a2 b1
      (RA: rtc rA a1 a2) (SIM1: sim a1 b1):
  exists b2, rtc rB b1 b2 /\ sim a2 b2.
Proof.
  revert b1 SIM1. induction RA; i.
  - eexists. splits; eauto.
  - exploit SIM; eauto. i. des.
    exploit IHRA; eauto. i. des.
    eexists. splits; [|eauto].
    econs; eauto.
Qed.

Inductive sim_seq (s:list Stmt.t): forall (lhs rhs:Thread.t lang), Prop :=
| sim_seq_intro
    rs stmts th mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) th mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) th mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 th1 mem1
      rs2 stmts2 th2 mem2
      (STEP: rtc (@Thread.internal_step lang)
                 (Thread.mk lang (State.mk rs1 stmts1) th1 mem1)
                 (Thread.mk lang (State.mk rs2 stmts2) th2 mem2)):
  rtc (@Thread.internal_step lang)
      (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) th1 mem1)
      (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) th2 mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. destruct a2. destruct state. destruct thread.
    generalize (internal_step_seq stmts RA). i.
    eexists. splits; eauto. econs; eauto.
  - econs; ss.
  - i. des. inv x1. auto.
Qed.

Inductive ctx (sim_thread:SIM_THREAD lang lang): SIM_THREAD lang lang :=
| ctx_incl
    sim_terminal
    st1 th1 mem_k_src st2 th2 mem_k_tgt
    (SIM: sim_thread sim_terminal st1 th1 mem_k_src st2 th2 mem_k_tgt):
    ctx sim_thread sim_terminal st1 th1 mem_k_src st2 th2 mem_k_tgt
| ctx_nil
    (sim_regs:SIM_REGS)
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    th_src th_tgt
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local th_src th_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src []) th_src mem_k_src
        (State.mk rs_tgt []) th_tgt mem_k_tgt
| ctx_instr
    instr regs
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    th_src th_tgt
    (REGS: RegSet.disjoint regs (Instr.regs_of instr))
    (RS: RegFile.eq_except regs rs_src rs_tgt)
    (LOCAL: sim_local th_src th_tgt):
    ctx sim_thread
        (sim_terminal (RegFile.eq_except regs))
        (State.mk rs_src [Stmt.instr instr]) th_src mem_k_src
        (State.mk rs_tgt [Stmt.instr instr]) th_tgt mem_k_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src th_src mem_k_src
    stmts1_tgt stmts2_tgt rs_tgt th_tgt mem_k_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (State.mk rs_src stmts1_src) th_src mem_k_src
                      (State.mk rs_tgt stmts1_tgt) th_tgt mem_k_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (State.mk rs_src (stmts1_src ++ stmts2_src)) th_src mem_k_src
        (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) th_tgt mem_k_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src mem_k_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt mem_k_tgt
    th_src th_tgt
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local th_src th_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) th_src mem_k_src
        (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) th_tgt mem_k_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src mem_k_src
    cond_tgt stmts_tgt rs_tgt mem_k_tgt
    th_src th_tgt
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local th_src th_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) th_src mem_k_src
        (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) th_tgt mem_k_tgt
.
Hint Constructors ctx.

Lemma ctx_mon: monotone7 ctx.
Proof.
  ii. inv IN.
  - econs 1. auto.
  - econs 2; auto.
  - econs 3; eauto; eapply _sim_stmts_mon; eauto.
  - econs 4; eauto; eapply _sim_stmts_mon; eauto.
  - econs 5; eauto; eapply _sim_stmts_mon; eauto.
  - econs 6; eauto; eapply _sim_stmts_mon; eauto.
Qed.
Hint Resolve ctx_mon.

Lemma ctx_weak_respectful: weak_respectful7 (@_sim_thread lang lang) ctx.
Proof.
  econs; auto. i. destruct PR.
  - (* incl *)
    eapply _sim_thread_mon; eauto.
    apply rclo7_incl.
  - (* nil *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISE.
    destruct th_src, th_tgt. ss. subst.
    splits; s; i.
    { inv TERMINAL_TGT. ss. eexists _, _, _. splits; eauto; ss. }
    { eexists. splits; try reflexivity; eauto.
      - etransitivity; eauto. apply Memory.splits_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. apply MEMORY.
    }
    { ss. subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; [|by inv STEP; inv STATE].
    inv STEP; ss; try by inv STATE.
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs 1. econs 1. s. eauto.
    + apply rclo7_step. apply ctx_nil; auto.
  - (* instr *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISE.
    destruct th_src, th_tgt. ss. subst.
    splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      - etransitivity; eauto. apply Memory.splits_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. apply MEMORY.
    }
    { ss. subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { apply rclo7_step. apply ctx_instr; auto. }
      * (* silent *)
        inv STATE.
        exploit sim_local_silent; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2; eauto. s. econs. eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* read *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 3; eauto. s. econs. eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* write *)
        inv STATE.
        exploit sim_local_write; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 4; eauto. s. econs. eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* update *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit sim_local_write; eauto.
        { eapply Local.read_step_future; eauto. }
        { eapply Local.read_step_future; eauto. }
        i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 5; eauto. s. econs. eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* fence *)
        inv STATE.
        exploit sim_local_fence; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 6; eauto. econs. eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
    + (* external *)
      inv STEP. inv STATE. ss.
      exploit sim_local_silent; eauto. i. des.
      exploit RegFile.eq_except_instr; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs 2. econs; eauto. econs. eauto.
      * apply rclo7_step. apply ctx_nil; auto.
  - (* seq *)
    ii. ss.
    exploit GF; eauto. s. i. des.
    splits; s; i.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
      destruct th2_src. ss. subst.
      destruct st2_src. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_internal_step_future; eauto. s. i. des.
      inv TERMINAL0. ss. subst.
      exploit SIM2; eauto. intro TH2.
      exploit GF; eauto. s. i. des.
      exploit TERMINAL0; try by econs. i. des.
      destruct st2_src, th2_src. inv TERMINAL_SRC. ss. subst.
      eexists _, _, _. splits; [|eauto| |eauto|eauto].
      + etransitivity; [|eauto].
        eapply rtc_internal_step_seq in STEPS. eauto.
      + econs.
    }
    { eapply FUTURE; eauto. }
    { subst. exploit PROMISE; eauto. i. des.
      destruct th_tgt, st2_src, th2_src. ss. subst.
      eexists _, _, _. splits; [|eauto].
      - eapply rtc_internal_step_seq. apply STEPS.
      - ss.
    }
    destruct stmts1_tgt.
    + exploit TERMINAL; try by econs. i. des.
      inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i. subst.
      destruct st2_src, th2_src. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_internal_step_future; eauto. s. i. des.
      inv TERMINAL0. ss. subst.
      exploit SIM2; eauto. intro TH2.
      exploit GF; eauto. s. i. des.
      exploit STEP0; eauto. i. des.
      eexists _, _, _, _, _, _. splits; [|eauto|eauto|].
      * eapply rtc_internal_step_seq in STEPS.
        etransitivity; [apply STEPS|eauto].
      * apply rclo7_incl. auto.
    + destruct st3_tgt, th3_tgt.
      exploit thread_step_deseq; eauto. i. des. ss. subst.
      exploit STEP; eauto. i. des.
      destruct st2_src, th2_src. destruct st3_src, th3_src.
      eexists _, _, _, _, _, _. splits; [| |eauto|].
      * eapply rtc_internal_step_seq. eauto.
      * eapply step_seq. eauto.
      * apply rclo7_step. eapply ctx_seq; eauto.
        { apply rclo7_incl. eauto. }
        { eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
  - (* ite *)
    ii.
    inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
    destruct th_src, th_tgt. ss. subst.
    splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      - etransitivity; eauto. apply Memory.splits_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. apply MEMORY.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; try inv STATE; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { apply rclo7_step. eapply ctx_ite; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * (* ite *)
        inv LOCAL0. ss.
        eexists _, _, _, _, _, _. splits; try apply MEMORY; eauto.
        { econs 1. econs 2. econs; eauto. s. econs; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          apply Memory.splits_future. apply MEMORY.
        }
        { s. rewrite ? app_nil_r.
          exploit COND; eauto. intro C. rewrite C.
          destruct (RegFile.eval_expr rs_tgt cond_tgt).
          - apply rclo7_incl. apply LE. apply SIM1; ss.
          - apply rclo7_incl. apply LE. apply SIM2; ss.
        }
    + inv STEP. inv STATE.
  - (* dowhile *)
    ii.
    inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
    destruct th_src, th_tgt. ss. subst.
    splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      - etransitivity; eauto. apply Memory.splits_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. apply MEMORY.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; try inv STATE; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { apply rclo7_step. apply ctx_dowhile; auto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * (* dowhile *)
        inv LOCAL0. ss.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2. econs; eauto. s. econs; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          apply Memory.splits_future. apply MEMORY.
        }
        { apply rclo7_step. eapply ctx_seq.
          { apply rclo7_incl. apply LE. apply SIM; ss. }
          ii. apply rclo7_step. eapply ctx_ite; eauto.
          - ii. apply rclo7_step. eapply ctx_dowhile; eauto.
            eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - ii. apply rclo7_base; auto.
        }
    + inv STEP. inv STATE.
Qed.

Definition sim_stmts := @_sim_stmts (@sim_thread lang lang).

Lemma sim_stmts_frame
      sim_regs0 sim_regs1
      sim_regs2 sim_regs3
      stmts_src stmts_tgt
      (SIM01: sim_regs0 <2= sim_regs1)
      (SIM23: sim_regs2 <2= sim_regs3)
      (SIM: sim_stmts sim_regs1 stmts_src stmts_tgt sim_regs2):
  sim_stmts sim_regs0 stmts_src stmts_tgt sim_regs3.
Proof.
  ii. eapply sim_thread_mon; [|eauto].
  i. inv PR. econs; eauto.
Qed.

Lemma sim_stmts_nil sim_regs:
  sim_stmts sim_regs [] [] sim_regs.
Proof.
  ii. pupto7_init. pupto7 ctx_weak_respectful.
Qed.

Lemma sim_stmts_instr
      instr regs
      (REGS: RegSet.disjoint regs (Instr.regs_of instr)):
  sim_stmts (RegFile.eq_except regs) [Stmt.instr instr] [Stmt.instr instr] (RegFile.eq_except regs).
Proof.
  ii. pupto7_init. pupto7 ctx_weak_respectful.
Qed.

Lemma sim_stmts_seq
      sim_regs0 sim_regs1 sim_regs2
      stmts1_src stmts2_src
      stmts1_tgt stmts2_tgt
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs1 stmts2_src stmts2_tgt sim_regs2):
  sim_stmts sim_regs0 (stmts1_src ++ stmts2_src) (stmts1_tgt ++ stmts2_tgt) sim_regs2.
Proof.
  ii. pupto7_init. pupto7 ctx_weak_respectful.
  econs 4.
  - pupto7_final. apply SIM1; auto.
  - ii. pupto7_final. apply SIM2; auto.
Qed.

Lemma sim_stmts_ite
      sim_regs0 sim_regs1
      cond_src stmts1_src stmts2_src
      cond_tgt stmts1_tgt stmts2_tgt
      (COND: sim_expr sim_regs0 cond_src cond_tgt)
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs0 stmts2_src stmts2_tgt sim_regs1):
  sim_stmts sim_regs0 [Stmt.ite cond_src stmts1_src stmts2_src] [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt] sim_regs1.
Proof.
  ii. pupto7_init. pupto7 ctx_weak_respectful.
  econs 5; eauto.
  - ii. pupto7_final. apply SIM1; auto.
  - ii. pupto7_final. apply SIM2; auto.
Qed.

Lemma sim_stmts_dowhile
      sim_regs
      cond_src stmts_src
      cond_tgt stmts_tgt
      (COND: sim_expr sim_regs cond_src cond_tgt)
      (SIM: sim_stmts sim_regs stmts_src stmts_tgt sim_regs):
  sim_stmts sim_regs [Stmt.dowhile stmts_src cond_src] [Stmt.dowhile stmts_tgt cond_tgt] sim_regs.
Proof.
  ii. pupto7_init. pupto7 ctx_weak_respectful.
  econs 6; eauto. ii. pupto7_final. apply SIM; auto.
Qed.
