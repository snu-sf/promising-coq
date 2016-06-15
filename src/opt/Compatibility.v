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

Lemma sim_local_memory_bot
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot):
  lc_src.(Local.promises) = Memory.bot.
Proof.
  inv SIM. eapply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
Qed.

Lemma sim_local_cell_bot
      loc lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) loc = Cell.bot):
  lc_src.(Local.promises) loc = Cell.bot.
Proof.
  inv SIM. eapply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
Qed.

Lemma sim_local_future
      inv
      lc_src mem1_src mem2_src
      lc_tgt mem1_tgt
      (INV1: MemInv.sem inv lc_src.(Local.promises) lc_tgt.(Local.promises))
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (FUTURE_SRC: Memory.future mem1_src mem2_src)
      (WF1_SRC: Local.wf lc_src mem1_src)
      (WF1_TGT: Local.wf lc_tgt mem1_tgt)
      (WF2_SRC: Local.wf lc_src mem2_src)
      (MEM2_SRC: Memory.closed mem2_src):
  exists mem2_tgt,
    <<MEM2: Memory.sim mem2_tgt mem2_src>> /\
    <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
    <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
    <<MEM2_TGT: Memory.closed mem2_tgt>>.
Proof.
  eexists. splits.
  - reflexivity.
  - etrans; eauto. apply Memory.sim_future. apply MEM1.
  - econs.
    + apply WF1_TGT.
    + eapply Commit.future_closed; try apply WF1_TGT; eauto.
      etrans; eauto. apply Memory.sim_future. apply MEM1.
    + etrans. apply INV1. apply WF2_SRC.
  - auto.
Qed.

Lemma sim_local_promise
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val released kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to val released lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to val released lc2_src mem2_src kind>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<MEM2: Memory.sim mem2_tgt mem2_src>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit MemInv.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit Memory.promise_future; try apply PROMISES_SRC; eauto.
  { apply WF1_SRC. }
  i. des.
  eexists _, _. splits; s; eauto.
  - econs; try apply PROMISES_SRC.
    + refl.
    + apply WF1_SRC.
    + eapply Commit.future_closed; [|eauto]. apply WF1_SRC.
  - econs; s; eauto. etrans; eauto.
Qed.

Lemma sim_local_strengthen
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val released1 released2
      (STEP_TGT: Local.strengthen_step lc1_tgt mem1_tgt loc from to val released1 released2 lc2_tgt mem2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.strengthen_step lc1_src mem1_src loc from to val released1 released2 lc2_src mem2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<MEM2: Memory.sim mem2_tgt mem2_src>>.
Proof.
Admitted.

Lemma sim_local_silent
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      (STEP_TGT: Local.silent_step lc1_tgt mem1_tgt lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src,
    <<STEP_SRC: Local.silent_step lc1_src mem1_src lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  eexists. splits; eauto.
  - econs.
    + etrans; eauto.
    + auto.
    + eapply Commit.future_closed; eauto.
      apply Memory.sim_future. apply MEM1.
  - econs; eauto. s. refl.
Qed.

Lemma sim_local_read
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released ord
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released ord lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src,
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released ord lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit Memory.sim_get; try apply MEM1; eauto. i. des.
  eexists. splits; eauto.
  - econs; eauto.
    + etrans; eauto.
    + eapply CommitFacts.read_mon1; eauto.
    + eapply Commit.future_closed; eauto.
      apply Memory.sim_future. apply MEM1.
  - econs; eauto. s. refl.
Qed.

Lemma sim_local_fulfill
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc from to val releasedc releasedm ord
      (STEP_TGT: Local.fulfill_step lc1_tgt mem1_tgt loc from to val releasedc releasedm ord lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src,
    <<STEP_SRC: Local.fulfill_step lc1_src mem1_src loc from to val releasedc releasedm ord lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit MemInv.fulfill; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  eexists. splits; eauto.
  - econs; eauto.
    + eapply CommitFacts.write_mon1; eauto.
    + eapply Commit.future_closed; eauto.
      apply Memory.sim_future. apply MEM1.
    + eapply Memory.future_closed_capability; eauto.
      apply Memory.sim_future. apply MEM1.
  - econs; eauto. s. refl.
Qed.

Lemma sim_local_write
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val releasedc releasedm ord kind_tgt
      (STEP_TGT: Local.write_step lc1_tgt mem1_tgt loc from to val releasedc releasedm ord lc2_tgt mem2_tgt kind_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src kind_src,
    <<STEP_SRC: Local.write_step lc1_src mem1_src loc from to val releasedc releasedm ord lc2_src mem2_src kind_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<MEM2: Memory.sim mem2_tgt mem2_src>>.
Proof.
  inv STEP_TGT.
  - exploit sim_local_fulfill; eauto. i. des.
    eexists _, _, _. splits; eauto. econs 1; eauto.
    i. eapply sim_local_cell_bot; eauto.
  - exploit sim_local_promise; eauto. i. des.
    exploit sim_local_fulfill; eauto.
    { eapply Local.promise_step_future; eauto. }
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists _, _, _. splits; eauto. econs 2; eauto.
    i. eapply sim_local_cell_bot; eauto.
Qed.

Lemma sim_local_fence
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      ordr ordw
      (STEP_TGT: Local.fence_step lc1_tgt mem1_tgt ordr ordw lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src,
    <<STEP_SRC: Local.fence_step lc1_src mem1_src ordr ordw lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv STEP_TGT.
  eexists. splits; eauto.
  - econs.
    + eapply CommitFacts.read_fence_mon1; eauto. apply LOCAL1.
    + eapply CommitFacts.write_fence_mon1; eauto. refl.
    + i. eapply sim_local_memory_bot; eauto.
    + eapply Commit.future_closed; eauto.
      apply Memory.sim_future. apply MEM1.
  - econs; try apply LOCAL1; eauto. s. refl.
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
  forall rs_src rs_tgt lc_src lc_tgt mem_k_src mem_k_tgt
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (State.mk rs_src stmts_src) lc_src mem_k_src
      (State.mk rs_tgt stmts_tgt) lc_tgt mem_k_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <7= s2):
  _sim_stmts s1 <4= _sim_stmts s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma lang_step_seq
      stmts rs1 stmts1 rs2 stmts2 e
      (STEP: State.step e
                        (State.mk rs1 stmts1)
                        (State.mk rs2 stmts2)):
  State.step e
             (State.mk rs1 (stmts1 ++ stmts))
             (State.mk rs2 (stmts2 ++ stmts)).
Proof.
  inv STEP.
  - econs 1. auto.
  - s. rewrite <- app_assoc. econs 2.
  - s. rewrite <- app_assoc. econs 3.
Qed.

Lemma lang_step_deseq
      stmts rs1 stmt1 stmts1 rs2 stmts2 e
      (STEP: State.step e
                        (State.mk rs1 (stmt1 :: stmts1 ++ stmts))
                        (State.mk rs2 stmts2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
    State.step e
               (State.mk rs1 (stmt1 :: stmts1))
               (State.mk rs2 stmts2').
Proof.
  inv STEP.
  - eexists. splits; eauto. econs 1. auto.
  - eexists. rewrite app_assoc. splits; eauto. econs 2.
  - eexists. rewrite app_comm_cons, app_assoc. splits; eauto. econs 3.
Qed.

Lemma program_step_seq
      stmts e
      rs1 stmts1 lc1 mem1
      rs2 stmts2 lc2 mem2
      (STEP: Thread.program_step
               e
               (Thread.mk lang (State.mk rs1 stmts1) lc1 mem1)
               (Thread.mk lang (State.mk rs2 stmts2) lc2 mem2)):
  Thread.program_step
    e
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 mem2).
Proof.
  inv STEP; ss.
  - econs 1; s; eauto. apply lang_step_seq. auto.
  - econs 2; s; eauto. apply lang_step_seq. auto.
  - econs 3; s; eauto. apply lang_step_seq. auto.
  - econs 4; s; eauto. apply lang_step_seq. auto.
  - econs 5; s; eauto. apply lang_step_seq. auto.
  - econs 6; s; eauto. apply lang_step_seq. auto.
Qed.

Lemma step_seq
      stmts e
      rs1 stmts1 lc1 mem1
      rs2 stmts2 lc2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 stmts1) lc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 mem2)):
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 mem1)
              (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 mem2).
Proof.
  inv STEP; ss.
  - econs 1. inv STEP0.
    + econs 1; ss. eauto.
    + econs 2; ss.
  - econs 2. apply program_step_seq. eauto.
Qed.

Lemma thread_step_deseq
      stmts e
      rs1 stmt1 stmts1 lc1 mem1
      rs2 stmts2 lc2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) lc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 mem2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) lc1 mem1)
              (Thread.mk lang (State.mk rs2 stmts2') lc2 mem2).
Proof.
  inv STEP.
  - inv STEP0; ss.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 1. econs 1. s. eauto.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 1. econs 2. s. eauto.
  - inv STEP0; ss.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 1; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 2; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 3; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 4; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 5; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 2. econs 6; s; eauto.
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
    rs stmts lc mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) lc mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) lc mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 lc1 mem1
      rs2 stmts2 lc2 mem2
      (STEP: rtc (@Thread.tau_step lang)
                 (Thread.mk lang (State.mk rs1 stmts1) lc1 mem1)
                 (Thread.mk lang (State.mk rs2 stmts2) lc2 mem2)):
  rtc (@Thread.tau_step lang)
      (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 mem1)
      (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. destruct a2. destruct state. destruct local. inv RA.
    generalize (step_seq stmts STEP0). i.
    eexists. splits; [|econs; eauto].
    eapply Thread.step_tau; eauto.
  - econs; ss.
  - i. des. inv x1. auto.
Qed.

Inductive ctx (sim_thread:SIM_THREAD lang lang): SIM_THREAD lang lang :=
| ctx_incl
    sim_terminal
    st1 lc1 mem_k_src st2 lc2 mem_k_tgt
    (SIM: sim_thread sim_terminal st1 lc1 mem_k_src st2 lc2 mem_k_tgt):
    ctx sim_thread sim_terminal st1 lc1 mem_k_src st2 lc2 mem_k_tgt
| ctx_nil
    (sim_regs:SIM_REGS)
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    lc_src lc_tgt
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src []) lc_src mem_k_src
        (State.mk rs_tgt []) lc_tgt mem_k_tgt
| ctx_instr
    instr regs
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    lc_src lc_tgt
    (REGS: RegSet.disjoint regs (Instr.regs_of instr))
    (RS: RegFile.eq_except regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt):
    ctx sim_thread
        (sim_terminal (RegFile.eq_except regs))
        (State.mk rs_src [Stmt.instr instr]) lc_src mem_k_src
        (State.mk rs_tgt [Stmt.instr instr]) lc_tgt mem_k_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src lc_src mem_k_src
    stmts1_tgt stmts2_tgt rs_tgt lc_tgt mem_k_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (State.mk rs_src stmts1_src) lc_src mem_k_src
                      (State.mk rs_tgt stmts1_tgt) lc_tgt mem_k_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (State.mk rs_src (stmts1_src ++ stmts2_src)) lc_src mem_k_src
        (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) lc_tgt mem_k_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src mem_k_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt mem_k_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) lc_src mem_k_src
        (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) lc_tgt mem_k_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src mem_k_src
    cond_tgt stmts_tgt rs_tgt mem_k_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) lc_src mem_k_src
        (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) lc_tgt mem_k_tgt
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
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISES.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. ss. eexists _, _, _. splits; eauto; ss. }
    { eexists. splits; try refl; eauto.
      - etrans; eauto. apply Memory.sim_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_closed; eauto.
        etransitivity; eauto.
        apply Memory.sim_future. apply MEMORY.
    }
    { subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; try by inv STEP; inv STATE.
    inv STEP; ss.
    + exploit sim_local_promise; eauto. i. des.
      eexists _, _, _, _, _, _, _. splits; eauto.
      * econs 1. econs 1. s. eauto.
      * eauto.
      * apply rclo7_step. apply ctx_nil; auto.
    + exploit sim_local_strengthen; eauto. i. des.
      eexists _, _, _, _, _, _, _. splits; eauto.
      * econs 1. econs 2. s. eauto.
      * eauto.
      * apply rclo7_step. apply ctx_nil; auto.
  - (* instr *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISES.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try refl; eauto.
      - etrans; eauto. apply Memory.sim_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_closed; eauto.
        etransitivity; eauto.
        apply Memory.sim_future. apply MEMORY.
    }
    { ss. subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_instr; auto. }
      * (* strengthen *)
        exploit sim_local_strengthen; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2. s. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_instr; auto. }
    + inv STEP; ss.
      * (* silent *)
        inv STATE.
        exploit sim_local_silent; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 1; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* read *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 2; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* write *)
        inv STATE.
        exploit sim_local_write; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 3; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* update *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit sim_local_write; eauto.
        { eapply Local.read_step_future; eauto. }
        { eapply Local.read_step_future; eauto. }
        i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 4; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* fence *)
        inv STATE.
        exploit sim_local_fence; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 5; eauto. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
      * (* syscall *)
        inv STATE.
        exploit sim_local_fence; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 2. econs 6; eauto. econs. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_nil; auto. }
  - (* seq *)
    ii. ss.
    exploit GF; eauto. s. i. des.
    splits; s; ii.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
      destruct lc2_src. ss. subst.
      destruct st2_src. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_step_future; eauto. s. i. des.
      inv TERMINAL0. ss. subst.
      exploit SIM2; eauto. intro LC2.
      exploit GF; eauto. s. i. des.
      exploit TERMINAL0; try by econs. i. des.
      destruct st2_src, lc2_src. inv TERMINAL_SRC. ss. subst.
      eexists _, _, _. splits; [|eauto| |eauto|eauto].
      + etrans; [|eauto].
        eapply rtc_internal_step_seq in STEPS. eauto.
      + econs.
    }
    { eapply FUTURE; eauto. }
    { exploit PROMISES; eauto. i. des.
      destruct lc_tgt, st2_src, lc2_src. ss. subst.
      eexists _, _, _. splits; [|eauto].
      - eapply rtc_internal_step_seq. apply STEPS.
      - ss.
    }
    destruct stmts1_tgt.
    + exploit TERMINAL; try by econs. i. des.
      inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i. subst.
      destruct st2_src, lc2_src. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_step_future; eauto. s. i. des.
      inv TERMINAL0. ss. subst.
      exploit SIM2; eauto. intro LC2.
      exploit GF; eauto. s. i. des.
      exploit STEP0; eauto. i. des.
      eexists _, _, _, _, _, _, _. splits; [|eauto|eauto|eauto|].
      * eapply rtc_internal_step_seq in STEPS.
        etrans; [apply STEPS|eauto].
      * apply rclo7_incl. auto.
    + destruct st3_tgt, lc3_tgt.
      exploit thread_step_deseq; eauto. i. des. ss. subst.
      exploit STEP; eauto. i. des.
      destruct st2_src, lc2_src. destruct st3_src, lc3_src.
      eexists _, _, _, _, _, _, _. splits; [| |eauto|eauto|].
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
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try refl; eauto.
      - etrans; eauto. apply Memory.sim_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_closed; eauto.
        etransitivity; eauto.
        apply Memory.sim_future. apply MEMORY.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { eauto. }
        { apply rclo7_step. eapply ctx_ite; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * (* strengthen *)
        exploit sim_local_strengthen; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2. s. eauto. }
        { eauto. }
        { apply rclo7_step. eapply ctx_ite; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
    + (* ite *)
      inv STEP; inv STATE; ss.
      inv LOCAL0. ss.
      eexists _, _, _, _, _, _, _. splits; try apply MEMORY; eauto.
      { econs 2. econs 1. econs; eauto. s. econs; eauto.
        - apply WF_TGT.
        - eapply Commit.future_closed; try apply WF_TGT; eauto.
          apply Memory.sim_future. apply MEMORY.
      }
      { eauto. }
      { s. rewrite ? app_nil_r.
        exploit COND; eauto. intro C. rewrite C.
        destruct (RegFile.eval_expr rs_tgt cond_tgt).
        - apply rclo7_incl. apply LE. apply SIM1; ss.
        - apply rclo7_incl. apply LE. apply SIM2; ss.
      }
  - (* dowhile *)
    ii.
    inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try refl; eauto.
      - etrans; eauto. apply Memory.sim_future. apply MEMORY.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_closed; eauto.
        etransitivity; eauto.
        apply Memory.sim_future. apply MEMORY.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss.
      * (* promise *)
        exploit sim_local_promise; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. s. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_dowhile; auto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * (* strengthen *)
        exploit sim_local_strengthen; eauto. i. des.
        eexists _, _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2. s. eauto. }
        { eauto. }
        { apply rclo7_step. apply ctx_dowhile; auto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
    + (* dowhile *)
      inv STEP; inv STATE; ss.
      inv LOCAL0. ss.
      eexists _, _, _, _, _, _, _. splits; eauto.
      { econs 2. econs 1. econs; eauto. s. econs; eauto.
        - apply WF_TGT.
        - eapply Commit.future_closed; try apply WF_TGT; eauto.
          apply Memory.sim_future. apply MEMORY.
      }
      { eauto. }
      { apply rclo7_step. eapply ctx_seq.
        { apply rclo7_incl. apply LE. apply SIM; ss. }
        ii. apply rclo7_step. eapply ctx_ite; eauto.
        - ii. apply rclo7_step. eapply ctx_dowhile; eauto.
          eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        - ii. apply rclo7_base; auto.
      }
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
