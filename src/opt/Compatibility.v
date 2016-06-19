Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful9.

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

Lemma sim_local_cell_bot
      loc lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) loc = Cell.bot):
  lc_src.(Local.promises) loc = Cell.bot.
Proof.
  inv SIM. eapply MemInv.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
Qed.

Lemma sim_local_memory_bot
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot):
  lc_src.(Local.promises) = Memory.bot.
Proof.
  inv SIM. eapply MemInv.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
Qed.

Lemma sim_local_future
      inv
      lc_src mem1_src mem2_src
      lc_tgt mem1_tgt
      (INV1: MemInv.sem inv lc_src.(Local.promises) lc_tgt.(Local.promises))
      (LE1: Memory.le lc_tgt.(Local.promises) lc_src.(Local.promises))
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
  esplits.
  - reflexivity.
  - etrans; eauto. apply Memory.sim_future. apply MEM1.
  - econs.
    + apply WF1_TGT.
    + eapply Commit.future_closed; try apply WF1_TGT; eauto.
      etrans; eauto. apply Memory.sim_future. apply MEM1.
    + etrans; eauto. apply WF2_SRC.
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
  exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
  { apply WF1_SRC. }
  i. des.
  esplits; eauto.
  - econs. apply PROMISE_SRC.
  - econs; eauto.
Qed.

Lemma sim_local_read
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists released_src lc2_src,
    <<REL: Capability.le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit Memory.sim_get; try apply MEM1; eauto. i. des.
  esplits; eauto.
  - econs; eauto. admit.
  - econs; eauto. s. admit. (* Commit.read_commit_mon *)
Admitted.

Lemma sim_local_write
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt ord
      (RELM: Capability.le releasedm_src releasedm_tgt)
      (WF_RELM_TGT: Capability.wf releasedm_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt ord lc2_tgt sc2_tgt mem2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src ord lc2_src sc2_src mem2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: Memory.sim mem2_tgt mem2_src>>.
Proof.
  inv STEP_TGT.
  assert (REL:
   Capability.le
     (Capability.join releasedm_src
        (Commit.rel
           (Commit.write_commit (Local.commit lc1_src) sc1_src loc to
              ord) loc))
     (Capability.join releasedm_tgt
        (Commit.rel
           (Commit.write_commit (Local.commit lc1_tgt) sc1_tgt loc to
              ord) loc))).
  { committac.
    - etrans; eauto. committac.
    - rewrite <- Capability.join_r.
      rewrite <- Capability.join_l.
      apply LOCAL1.
    - condtac; committac; try apply WF1_TGT.
      + rewrite <- Capability.join_r.
        rewrite <- Capability.join_r.
        rewrite <- Capability.join_l.
        rewrite <- Capability.join_l.
        apply LOCAL1.
      + condtac; committac.
      + etrans; [|apply TimeMap.join_r].
        etrans; [|apply TimeMap.join_r].
        etrans; [|apply TimeMap.join_l].
        etrans; [|apply TimeMap.join_r].
        unfold TimeMap.singleton, LocFun.add. condtac; [refl|congr].
      + condtac; committac.
        rewrite <- Capability.join_r.
        rewrite <- Capability.join_r.
        rewrite <- Capability.join_r.
        econs; try refl. ss.
  }
  exploit MemInv.write; try apply WRITE; eauto.
  { apply LOCAL1. }
  { apply LOCAL1. }
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des. esplits; eauto.
  - econs; eauto.
    + admit.
    + i. exploit RELEASE; eauto. i. des.
      splits; auto. eapply sim_local_cell_bot; eauto.
  - econs; eauto. s. admit. (* CommitFacts.write_commit_mon *)
Admitted.

Lemma sim_local_fence
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr ordw
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt mem1_tgt ordr ordw lc2_tgt sc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src mem1_src ordr ordw lc2_src sc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto. i. eapply sim_local_memory_bot; eauto.
  - econs; try apply LOCAL1. s. admit. (* CommitFacts.fence_commit_mon *)
Admitted.

Lemma future_read_step lc1 mem1 mem1' loc ts val released ord lc2
      (FUTURE: Memory.future mem1 mem1')
      (STEP: Local.read_step lc1 mem1 loc ts val released ord lc2):
  exists released' lc2',
    <<STEP: Local.read_step lc1 mem1' loc ts val released' ord lc2'>> /\
    <<REL: Capability.le released' released>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP. exploit Memory.future_get; eauto. i. des.
  esplits.
  - econs; eauto. admit.
  - auto.
  - econs; s.
    + admit.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma future_fence_step lc1 sc1 mem1 mem1' ordr ordw lc2 sc2
      (FUTURE: Memory.future mem1 mem1')
      (STEP: Local.fence_step lc1 sc1 mem1 ordr ordw lc2 sc2):
  Local.fence_step lc1 sc1 mem1' ordr ordw lc2 sc2.
Proof.
  inv STEP. econs; eauto.
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
  forall rs_src rs_tgt lc_src lc_tgt sc_k_src sc_k_tgt mem_k_src mem_k_tgt
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (State.mk rs_src stmts_src) lc_src sc_k_src mem_k_src
      (State.mk rs_tgt stmts_tgt) lc_tgt sc_k_tgt mem_k_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <9= s2):
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
  - esplits; eauto. econs 1. auto.
  - eexists. rewrite app_assoc. splits; eauto. econs 2.
  - eexists. rewrite app_comm_cons, app_assoc. splits; eauto. econs 3.
Qed.

Lemma program_step_seq
      stmts e
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.program_step
               e
               (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
               (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  Thread.program_step
    e
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
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
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
              (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  inv STEP.
  - econs 1. inv STEP0. econs. eauto.
  - econs 2. apply program_step_seq. eauto.
Qed.

Lemma thread_step_deseq
      stmts e
      rs1 stmt1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) lc1 sc1 mem1)
                         (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) lc1 sc1 mem1)
              (Thread.mk lang (State.mk rs2 stmts2') lc2 sc2 mem2).
Proof.
  inv STEP.
  - inv STEP0.
    rewrite app_comm_cons.
    esplits; eauto.
    econs 1. econs. eauto.
  - inv STEP0; ss.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
      econs 2. econs 1; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
      econs 2. econs 2; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
      econs 2. econs 3; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
      econs 2. econs 4; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
      econs 2. econs 5; s; eauto.
    + apply lang_step_deseq in STATE. des. subst.
      esplits; eauto.
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
  - esplits; eauto.
  - exploit SIM; eauto. i. des.
    exploit IHRA; eauto. i. des.
    esplits; [|eauto].
    econs; eauto.
Qed.

Inductive sim_seq (s:list Stmt.t): forall (lhs rhs:Thread.t lang), Prop :=
| sim_seq_intro
    rs stmts lc sc mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) lc sc mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) lc sc mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 lc1 sc1 mem1
      rs2 stmts2 lc2 sc2 mem2
      (STEP: rtc (@Thread.tau_step lang)
                 (Thread.mk lang (State.mk rs1 stmts1) lc1 sc1 mem1)
                 (Thread.mk lang (State.mk rs2 stmts2) lc2 sc2 mem2)):
  rtc (@Thread.tau_step lang)
      (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) lc1 sc1 mem1)
      (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) lc2 sc2 mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. destruct a2. destruct state. destruct local. inv RA.
    generalize (step_seq stmts STEP0). i.
    esplits; [|econs; eauto].
    eapply Thread.step_tau; eauto.
  - econs; ss.
  - i. des. inv x1. auto.
Qed.

Inductive ctx (sim_thread:SIM_THREAD lang lang): SIM_THREAD lang lang :=
| ctx_incl
    sim_terminal
    st1 lc1 sc_k_src mem_k_src st2 lc2 sc_k_tgt mem_k_tgt
    (SIM: sim_thread sim_terminal st1 lc1 sc_k_src mem_k_src st2 lc2 sc_k_tgt mem_k_tgt):
    ctx sim_thread sim_terminal st1 lc1 sc_k_src mem_k_src st2 lc2 sc_k_tgt mem_k_tgt
| ctx_nil
    (sim_regs:SIM_REGS)
    rs_src sc_k_src mem_k_src
    rs_tgt sc_k_tgt mem_k_tgt
    lc_src lc_tgt
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src []) lc_src sc_k_src mem_k_src
        (State.mk rs_tgt []) lc_tgt sc_k_tgt mem_k_tgt
| ctx_instr
    instr regs
    rs_src sc_k_src mem_k_src
    rs_tgt sc_k_tgt mem_k_tgt
    lc_src lc_tgt
    (REGS: RegSet.disjoint regs (Instr.regs_of instr))
    (RS: RegFile.eq_except regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt):
    ctx sim_thread
        (sim_terminal (RegFile.eq_except regs))
        (State.mk rs_src [Stmt.instr instr]) lc_src sc_k_src mem_k_src
        (State.mk rs_tgt [Stmt.instr instr]) lc_tgt sc_k_tgt mem_k_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src lc_src sc_k_src mem_k_src
    stmts1_tgt stmts2_tgt rs_tgt lc_tgt sc_k_tgt mem_k_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (State.mk rs_src stmts1_src) lc_src sc_k_src mem_k_src
                      (State.mk rs_tgt stmts1_tgt) lc_tgt sc_k_tgt mem_k_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (State.mk rs_src (stmts1_src ++ stmts2_src)) lc_src sc_k_src mem_k_src
        (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) lc_tgt sc_k_tgt mem_k_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src sc_k_src mem_k_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt sc_k_tgt mem_k_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) lc_src sc_k_src mem_k_src
        (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) lc_tgt sc_k_tgt mem_k_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src sc_k_src mem_k_src
    cond_tgt stmts_tgt rs_tgt sc_k_tgt mem_k_tgt
    lc_src lc_tgt
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) lc_src sc_k_src mem_k_src
        (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) lc_tgt sc_k_tgt mem_k_tgt
.
Hint Constructors ctx.

Lemma ctx_mon: monotone9 ctx.
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

Lemma ctx_weak_respectful: weak_respectful9 (@_sim_thread lang lang) ctx.
Proof.
  econs; auto. i. destruct PR.
  - (* incl *)
    eapply _sim_thread_mon; eauto.
    apply rclo9_incl.
  - (* nil *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISES; auto.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. ss. esplits; eauto; ss. }
    { exploit sim_local_future; try apply LOCAL; eauto. i. des.
      esplits; try apply TimeMap.join_l; try apply TimeMap.join_r; eauto.
      apply Memory.join_closed_timemap.
      - admit. (* future sc should be chosen more carefully *)
      - eapply Memory.future_closed_timemap; eauto.
    }
    { subst. esplits; eauto. }
    inv STEP_TGT; try by inv STEP; inv STATE.
    inv STEP; ss.
    exploit sim_local_promise; eauto. i. des.
    esplits.
    + eauto.
    + econs 1. econs. eauto.
    + eauto.
    + eauto.
    + eauto.
    + apply rclo9_step. apply ctx_nil; auto.
  - (* instr *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISES; auto.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { exploit sim_local_future; try apply LOCAL; eauto. i. des.
      esplits; try apply TimeMap.join_l; try apply TimeMap.join_r; eauto.
      apply Memory.join_closed_timemap.
      - admit. (* future sc should be chosen more carefully *)
      - eapply Memory.future_closed_timemap; eauto.
    }
    { ss. subst. esplits; eauto. }
    inv STEP_TGT; ss.
    + (* promise *)
      inv STEP; ss.
      exploit sim_local_promise; eauto. i. des.
      esplits; try apply SC; eauto.
      { econs 1. econs. eauto. }
      { eauto. }
      { apply rclo9_step. apply ctx_instr; auto. }
    + inv STEP; ss.
      * (* silent *)
        inv STATE.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; try apply SC; eauto.
        { econs 2. econs; eauto. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
      * (* read *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; try apply SC; eauto.
        { econs 2. econs 2; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
      * (* write *)
        inv STATE.
        exploit sim_local_write; try apply LOCAL0; try apply SC; eauto.
        { refl. }
        { apply Capability.bot_wf. }
        i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; eauto.
        { econs 2. econs 3; eauto. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
      * (* update *)
        inv STATE.
        exploit sim_local_read; eauto. i. des.
        exploit sim_local_write; try apply SC; eauto.
        { admit. }
        { eapply Local.read_step_future; eauto. }
        { eapply Local.read_step_future; eauto. }
        i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; eauto.
        { econs 2. econs 4; eauto. s. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
      * (* fence *)
        inv STATE.
        exploit sim_local_fence; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; try apply SC; eauto.
        { econs 2. econs 5; eauto. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
      * (* syscall *)
        inv STATE.
        exploit sim_local_fence; eauto. i. des.
        exploit RegFile.eq_except_instr; eauto. i. des.
        esplits; eauto.
        { econs 2. econs 6; eauto. econs. eauto. }
        { eauto. }
        { apply rclo9_step. apply ctx_nil; auto. }
  - (* seq *)
    ii. ss.
    exploit GF; try apply SIM1; try apply SC; eauto. i. des.
    splits; s; ii.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
      destruct lc2_src. ss. subst.
      destruct st2_src. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_step_future; eauto. s. i. des.
      inv TERMINAL0. ss. subst.
      exploit SIM2; eauto. intro LC2.
      exploit GF; try apply LC2; try apply SC0; eauto. s. i. des.
      exploit TERMINAL0; try by econs. i. des.
      destruct st2_src, lc2_src. inv TERMINAL_SRC. ss. subst.
      esplits; cycle 1; eauto.
      + econs.
      + etrans; [|eauto].
        eapply rtc_internal_step_seq in STEPS. eauto.
    }
    { eapply FUTURE; eauto. }
    { exploit PROMISES; eauto. i. des.
      destruct lc_tgt, st2_src, lc2_src. ss. subst.
      esplits; [|eauto].
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
      exploit GF; try apply SC0; eauto. i. des.
      exploit STEP0; eauto. i. des.
      esplits; cycle 1; eauto.
      * apply rclo9_incl. auto.
      * eapply rtc_internal_step_seq in STEPS.
        etrans; [apply STEPS|eauto].
    + destruct st3_tgt, lc3_tgt.
      exploit thread_step_deseq; eauto. i. des. ss. subst.
      exploit STEP; eauto. i. des.
      destruct st2_src, lc2_src. destruct st3_src, lc3_src.
      esplits; [M|M| | | |]; Mskip eauto.
      * eapply rtc_internal_step_seq. eauto.
      * eapply step_seq. eauto.
      * apply rclo9_step. eapply ctx_seq; eauto.
        { apply rclo9_incl. eauto. }
        { eapply _sim_stmts_mon; try apply rclo9_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
  - (* ite *)
    ii.
    inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { exploit sim_local_future; try apply LOCAL; eauto. i. des.
      esplits; try apply TimeMap.join_l; try apply TimeMap.join_r; eauto.
      apply Memory.join_closed_timemap.
      - admit. (* future sc should be chosen more carefully *)
      - eapply Memory.future_closed_timemap; eauto.
    }
    { ss. subst. esplits; eauto. }
    inv STEP_TGT; ss.
    + (* promise *)
      inv STEP; ss.
      exploit sim_local_promise; eauto. i. des.
      esplits; try apply SC; eauto.
      { econs 1. econs. s. eauto. }
      { eauto. }
      { apply rclo9_step. eapply ctx_ite; eauto.
        - eapply _sim_stmts_mon; try apply rclo9_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        - eapply _sim_stmts_mon; try apply rclo9_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
      }
    + (* ite *)
      inv STEP; inv STATE; ss.
      inv LOCAL. ss.
      esplits; try apply MEMORY; try apply SC; eauto.
      { econs 2. econs 1. econs; eauto. }
      { eauto. }
      { s. rewrite ? app_nil_r.
        exploit COND; eauto. intro C. rewrite C.
        destruct (RegFile.eval_expr rs_tgt cond_tgt).
        - apply rclo9_incl. apply LE. apply SIM1; ss.
        - apply rclo9_incl. apply LE. apply SIM2; ss.
      }
  - (* dowhile *)
    ii.
    inversion LOCAL. exploit MemInv.sem_bot_inv; eauto. i.
    destruct lc_src, lc_tgt. ss. subst.
    splits; s; ii.
    { inv TERMINAL_TGT. }
    { exploit sim_local_future; try apply LOCAL; eauto. i. des.
      esplits; try apply TimeMap.join_l; try apply TimeMap.join_r; eauto.
      apply Memory.join_closed_timemap.
      - admit. (* future sc should be chosen more carefully *)
      - eapply Memory.future_closed_timemap; eauto.
    }
    { ss. subst. esplits; eauto. }
    inv STEP_TGT; ss.
    + (* promise *)
      inv STEP; ss.
      exploit sim_local_promise; eauto. i. des.
      esplits; try apply SC; eauto.
      { econs 1. econs. eauto. }
      { eauto. }
      { apply rclo9_step. apply ctx_dowhile; auto.
        - eapply _sim_stmts_mon; try apply rclo9_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
      }
    + (* dowhile *)
      inv STEP; inv STATE; ss.
      inv LOCAL. ss.
      esplits; try apply SC; eauto.
      { econs 2. econs 1. econs; eauto. }
      { eauto. }
      { apply rclo9_step. eapply ctx_seq.
        { apply rclo9_incl. apply LE. apply SIM; ss. }
        ii. apply rclo9_step. eapply ctx_ite; eauto.
        - ii. apply rclo9_step. eapply ctx_dowhile; eauto.
          eapply _sim_stmts_mon; try apply rclo9_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        - ii. apply rclo9_base; auto.
      }
Admitted.

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
  ii. pupto9_init. pupto9 ctx_weak_respectful.
Qed.

Lemma sim_stmts_instr
      instr regs
      (REGS: RegSet.disjoint regs (Instr.regs_of instr)):
  sim_stmts (RegFile.eq_except regs) [Stmt.instr instr] [Stmt.instr instr] (RegFile.eq_except regs).
Proof.
  ii. pupto9_init. pupto9 ctx_weak_respectful.
Qed.

Lemma sim_stmts_seq
      sim_regs0 sim_regs1 sim_regs2
      stmts1_src stmts2_src
      stmts1_tgt stmts2_tgt
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs1 stmts2_src stmts2_tgt sim_regs2):
  sim_stmts sim_regs0 (stmts1_src ++ stmts2_src) (stmts1_tgt ++ stmts2_tgt) sim_regs2.
Proof.
  ii. pupto9_init. pupto9 ctx_weak_respectful.
  econs 4.
  - pupto9_final. apply SIM1; auto.
  - ii. pupto9_final. apply SIM2; auto.
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
  ii. pupto9_init. pupto9 ctx_weak_respectful.
  econs 5; eauto.
  - ii. pupto9_final. apply SIM1; auto.
  - ii. pupto9_final. apply SIM2; auto.
Qed.

Lemma sim_stmts_dowhile
      sim_regs
      cond_src stmts_src
      cond_tgt stmts_tgt
      (COND: sim_expr sim_regs cond_src cond_tgt)
      (SIM: sim_stmts sim_regs stmts_src stmts_tgt sim_regs):
  sim_stmts sim_regs [Stmt.dowhile stmts_src cond_src] [Stmt.dowhile stmts_tgt cond_tgt] sim_regs.
Proof.
  ii. pupto9_init. pupto9 ctx_weak_respectful.
  econs 6; eauto. ii. pupto9_final. apply SIM; auto.
Qed.
