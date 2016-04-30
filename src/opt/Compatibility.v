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
      - etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; [|by inv STEP; inv STATE].
    inv STEP; ss; try by inv STATE.
    inv STEP0. ss.
    exploit MemInv.promise; try apply MEMORY; eauto.
    { apply WF_SRC. }
    { apply WF_TGT. }
    { apply LOCAL. }
    i. des. apply MemInv.sem_bot_inv in INV2. subst.
    exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
    { inv WF_SRC. auto. }
    { inv WF_SRC. auto. }
    i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs 1. econs 1. s. econs; s; eauto.
      inv WF_TGT. eapply Commit.future_wf; eauto.
      etransitivity; eauto.
      apply Memory.splits_future. inv MEMORY. auto.
    + apply rclo7_step. apply ctx_nil; auto.
      econs; ss. apply MemInv.sem_bot.
  - (* instr *)
    ii.
    inversion LOCAL. apply MemInv.sem_bot_inv in PROMISE.
    destruct th_src, th_tgt. ss. subst.
    splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      - etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
      - inv WF_SRC0. inv WF_TGT. ss. econs; ss.
        eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; inv STEP0; try inv STATE; ss.
      * (* promise *)
        exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply LOCAL. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. econs; s; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          etransitivity; eauto. apply Memory.splits_future. inv MEMORY. eauto.
        }
        { apply rclo7_step. apply ctx_instr; auto.
          econs; ss. apply MemInv.sem_bot.
        }
      * (* silent *)
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2; ss.
          - econs; eauto.
          - econs; eauto.
            eapply Commit.future_wf; try apply WF_TGT; eauto.
            apply Memory.splits_future. inv MEMORY. eauto.
        }
        { apply rclo7_step. apply ctx_nil; auto.
          econs; ss. apply LOCAL.
        }
      * (* read *)
        exploit RegFile.eq_except_instr; eauto. i. des.
        generalize GET. intro X. apply MEMORY in X.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 3; ss.
          - econs. eauto.
          - econs 1; eauto.
            + s. eapply CommitFacts.read_mon; eauto.
            + eapply Commit.future_wf; eauto.
              apply Memory.splits_future. inv MEMORY. auto.
        }
        { apply rclo7_step. apply ctx_nil; auto.
          econs; ss.
          - reflexivity.
          - apply LOCAL.
        }
      * (* write *)
        exploit RegFile.eq_except_instr; eauto. i. des.
        exploit MemInv.write; try apply MEMORY0; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply LOCAL. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 3; ss.
          - econs. eauto.
          - econs 2; eauto.
            + s. eapply CommitFacts.write_mon; eauto.
            + eapply Commit.future_wf; eauto.
              apply Memory.splits_future. inv SIM2. auto.
        }
        { apply rclo7_step. apply ctx_nil; auto. econs; ss.
          - reflexivity.
          - apply MemInv.sem_bot.
        }
      * (* update *)
        exploit RegFile.eq_except_instr; eauto. i. des.
        generalize GET. intro X. apply MEMORY in X.
        exploit MemInv.write; try apply MEMORY0; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        { apply MemInv.sem_bot. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 3; ss.
          - econs. eauto.
          - econs 3; eauto.
            + s. eapply CommitFacts.read_mon; eauto.
            + eapply Commit.future_wf; eauto.
              apply Memory.splits_future. inv SIM2. auto.
        }
        { apply rclo7_step. apply ctx_nil; auto. econs; ss.
          - reflexivity.
          - apply MemInv.sem_bot.
        }
      * (* fence *)
        exploit RegFile.eq_except_instr; eauto. i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 3; ss.
          - econs. eauto.
          - econs 4; eauto.
            + s. eapply CommitFacts.fence_mon; eauto.
            + eapply Commit.future_wf; eauto.
              apply Memory.splits_future. inv MEMORY. auto.
        }
        { apply rclo7_step. apply ctx_nil; auto. econs; ss.
          - reflexivity.
          - apply MemInv.sem_bot.
        }
    + (* external *)
      inv STEP. inv STEP0. inv STATE. ss.
      exploit RegFile.eq_except_instr; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs 2. econs; ss.
        { econs. eauto. }
        { econs; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          apply Memory.splits_future. inv MEMORY. eauto.
        }
      * apply rclo7_step. apply ctx_nil; auto. econs; ss.
        apply MemInv.sem_bot.
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
      - etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; inv STEP0; try inv STATE; ss.
      * (* promise *)
        exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        s. i. des. apply MemInv.sem_bot_inv in INV2. subst.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. econs; s; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          etransitivity; eauto. apply Memory.splits_future. inv MEMORY. eauto.
        }
        { apply rclo7_step. eapply ctx_ite; eauto.
          - econs; ss. apply MemInv.sem_bot.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * (* ite *)
        eexists _, _, _, _, _, _. splits; try apply MEMORY; eauto.
        { econs 1. econs 2. econs; eauto. s. econs; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          apply Memory.splits_future. inv MEMORY. eauto.
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
      - etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
      - inv WF_SRC0. inv WF_TGT. ss.
        econs; ss. eapply Commit.future_wf; eauto.
        etransitivity; eauto.
        apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; inv STEP0; try inv STATE; ss.
      * (* promise *)
        exploit MemInv.promise; try apply MEMORY; eauto.
        { apply WF_SRC. }
        { apply WF_TGT. }
        s. i. des. apply MemInv.sem_bot_inv in INV2. subst.
        exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
        { apply WF_SRC. }
        { apply WF_SRC. }
        i. des.
        eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 1. econs; s; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          etransitivity; eauto. apply Memory.splits_future. inv MEMORY. eauto.
        }
        { apply rclo7_step. apply ctx_dowhile; auto.
          - econs; ss. apply MemInv.sem_bot.
          - eapply _sim_stmts_mon; try apply rclo7_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
      * eexists _, _, _, _, _, _. splits; eauto.
        { econs 1. econs 2. econs; eauto. s. econs; eauto.
          eapply Commit.future_wf; try apply WF_TGT; eauto.
          apply Memory.splits_future. inv MEMORY. eauto.
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
