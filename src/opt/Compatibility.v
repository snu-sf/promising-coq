Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.
Require Import Simulation.
Require Import MemInv.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Definition SIM_REGS := forall (rs_src rs_tgt:RegFile.t), Prop.

Definition eq_except (regs:RegSet.t) (rs_src rs_tgt:RegFile.t): Prop :=
  forall reg (REG: ~ RegSet.mem reg regs), rs_src reg = rs_tgt reg.

Lemma eq_except_nil rs_src rs_tgt:
  rs_src = rs_tgt <-> eq_except RegSet.empty rs_src rs_tgt.
Proof.
  econs; i; subst; auto.
  - econs.
  - extensionality reg. apply H. auto.
Qed.

Lemma eq_except_mon regs1 regs2
      (SUB: RegSet.Subset regs1 regs2):
  eq_except regs1 <2= eq_except regs2.
Proof.
  ii. specialize (PR reg). apply PR. contradict REG.
  apply IdentSet.Facts.mem_iff. apply SUB.
  apply IdentSet.Facts.mem_iff. auto.
Qed.

Lemma eq_except_value
      rs_src rs_tgt regs v
      (REGS: RegSet.disjoint regs (Value.regs_of v))
      (RS: eq_except regs rs_src rs_tgt):
  RegFile.eval_value rs_src v = RegFile.eval_value rs_tgt v.
Proof.
  destruct v; auto. ss. apply RS. ii.
  eapply REGS; eauto.
  apply RegSet.Facts.mem_iff.
  apply RegSet.Facts.singleton_iff. auto.
Qed.

Lemma eq_except_value_list
      rs_src rs_tgt regs vl
      (REGS: RegSet.disjoint regs (Value.regs_of_list vl))
      (RS: eq_except regs rs_src rs_tgt):
  map (RegFile.eval_value rs_src) vl = map (RegFile.eval_value rs_tgt) vl.
Proof.
  revert REGS. induction vl; ss. i. f_equal.
  - eapply eq_except_value; eauto.
    ii. eapply REGS; eauto.
    destruct a; ss.
    apply RegSet.Facts.mem_iff in RHS.
    apply RegSet.Facts.mem_iff.
    apply RegSet.singleton_spec in RHS. subst.
    apply RegSet.add_spec. auto.
  - apply IHvl.
    ii. eapply REGS; eauto.
    destruct a; ss.
    apply RegSet.Facts.mem_iff in RHS.
    apply RegSet.Facts.mem_iff.
    apply RegSet.add_spec. auto.
Qed.

Lemma eq_except_expr
      rs_src rs_tgt regs e
      (REGS: RegSet.disjoint regs (Instr.regs_of_expr e))
      (RS: eq_except regs rs_src rs_tgt):
  RegFile.eval_expr rs_src e = RegFile.eval_expr rs_tgt e.
Proof.
  destruct e; ss.
  - erewrite eq_except_value; eauto.
  - erewrite eq_except_value; eauto.
  - erewrite (eq_except_value op1); eauto.
    + erewrite (eq_except_value op2); eauto.
      ii. eapply REGS; eauto.
      apply RegSet.Facts.mem_iff in RHS.
      apply RegSet.Facts.mem_iff.
      apply RegSet.union_spec. auto.
    + ii. eapply REGS; eauto.
      apply RegSet.Facts.mem_iff in RHS.
      apply RegSet.Facts.mem_iff.
      apply RegSet.union_spec. auto.
Qed.

Lemma eq_except_instr
      rs1_src rs1_tgt rs2_tgt regs instr e
      (TGT: RegFile.eval_instr rs1_tgt instr e rs2_tgt)
      (REGS: RegSet.disjoint regs (Instr.regs_of instr))
      (RS: eq_except regs rs1_src rs1_tgt):
  exists rs2_src,
    <<SRC: RegFile.eval_instr rs1_src instr e rs2_src>> /\
    <<RS: eq_except regs rs2_src rs2_tgt>>.
Proof.
  inv TGT; ss.
  - eexists. splits; [econs|].
    ii. apply RS. auto.
  - eexists. splits; [econs|].
    ii. generalize (RS reg). i.
    unfold RegFun.add, RegFun.find.
    destruct (Reg.eq_dec reg lhs); auto.
    subst. eapply eq_except_expr; eauto.
    ii. eapply REGS; eauto.
    apply RegSet.Facts.mem_iff in RHS.
    apply RegSet.Facts.mem_iff.
    apply RegSet.add_spec. auto.
  - eexists. splits; [econs|].
    ii. specialize (RS reg).
    unfold RegFun.add, RegFun.find.
    destruct (Reg.eq_dec reg lhs); auto.
  - erewrite <- eq_except_value; eauto.
    eexists. splits; [econs|].
    ii. specialize (RS reg).
    unfold RegFun.add, RegFun.find.
    destruct (Reg.eq_dec reg lhs); auto.
  - erewrite <- eq_except_value; eauto.
    + eexists. splits; [econs|].
      ii. specialize (RS reg).
      unfold RegFun.add, RegFun.find.
      destruct (Reg.eq_dec reg lhs); auto.
    + ii. eapply REGS; eauto.
      apply RegSet.Facts.mem_iff in RHS.
      apply RegSet.Facts.mem_iff.
      apply RegSet.add_spec. auto.
  - eexists. splits; [econs|]. auto.
  - erewrite <- eq_except_value_list; eauto.
    + eexists. splits; [econs|].
      ii. specialize (RS reg).
      unfold RegFun.add, RegFun.find.
      destruct (Reg.eq_dec reg lhs); auto.
    + ii. eapply REGS; eauto.
      apply RegSet.Facts.mem_iff in RHS.
      apply RegSet.Facts.mem_iff.
      apply RegSet.add_spec. auto.
Qed.


Inductive sim_terminal
          (sim_regs:SIM_REGS)
          (th_src th_tgt:Thread.t lang): Prop :=
| sim_terminal_intro
    (REGS: sim_regs th_src.(Thread.state).(State.regs) th_tgt.(Thread.state).(State.regs))
    (COMMIT: Commit.le th_src.(Thread.commit) th_tgt.(Thread.commit))
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
  forall rs_src rs_tgt commit_src commit_tgt promise mem_k_src mem_k_tgt
    (RS: sim_regs0 rs_src rs_tgt)
    (COMMIT: Commit.le commit_src commit_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (Thread.mk lang (State.mk rs_src stmts_src) commit_src promise) mem_k_src
      (Thread.mk lang (State.mk rs_tgt stmts_tgt) commit_tgt promise) mem_k_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <5= s2):
  _sim_stmts s1 <4= _sim_stmts s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma step_seq
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

Lemma step_deseq
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
      rs1 stmts1 commit1 promise1 mem1
      rs2 stmts2 commit2 promise2 mem2
      (STEP: Thread.internal_step
               (Thread.mk lang (State.mk rs1 stmts1) commit1 promise1) mem1
               (Thread.mk lang (State.mk rs2 stmts2) commit2 promise2) mem2):
  Thread.internal_step
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 promise1) mem1
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 promise2) mem2.
Proof.
  inv STEP.
  - econs 1; s; eauto. apply step_seq. auto.
  - econs 2; s; eauto. apply step_seq. auto.
  - econs 3; s; eauto. apply step_seq. auto.
  - econs 4; s; eauto. apply step_seq. auto.
  - econs 5; s; eauto. apply step_seq. auto.
  - econs 6; s; eauto.
Qed.

Lemma thread_step_seq
      stmts e
      rs1 stmts1 commit1 promise1 mem1
      rs2 stmts2 commit2 promise2 mem2
      (STEP: Thread.step e
               (Thread.mk lang (State.mk rs1 stmts1) commit1 promise1) mem1
               (Thread.mk lang (State.mk rs2 stmts2) commit2 promise2) mem2):
  Thread.step e
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 promise1) mem1
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 promise2) mem2.
Proof.
  inv STEP.
  - econs 1. eapply internal_step_seq. auto.
  - econs 2; eauto. inv STATE. econs; eauto.
Qed.

Lemma _internal_step_seq
      stmts
      rs1 stmts1 commit1 promise1 mem1
      rs2 stmts2 commit2 promise2 mem2
      (STEP: Thread._internal_step
               (Thread.mk lang (State.mk rs1 stmts1) commit1 promise1, mem1)
               (Thread.mk lang (State.mk rs2 stmts2) commit2 promise2, mem2)):
  Thread._internal_step
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 promise1, mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 promise2, mem2).
Proof.
  inv STEP. econs. ss.
  apply internal_step_seq. auto.
Qed.

Lemma thread_step_deseq
      stmts e
      rs1 stmt1 stmts1 commit1 promise1 mem1
      rs2 stmts2 commit2 promise2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) commit1 promise1) mem1
                         (Thread.mk lang (State.mk rs2 stmts2) commit2 promise2) mem2):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) commit1 promise1) mem1
              (Thread.mk lang (State.mk rs2 stmts2') commit2 promise2) mem2.
Proof.
  inv STEP.
  - inv STEP0; ss.
    + apply step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 1; s; eauto.
    + apply step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 2; s; eauto.
    + apply step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 3; s; eauto.
    + apply step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 4; s; eauto.
    + apply step_deseq in STATE. des. subst.
      eexists. splits; eauto.
      econs 1. econs 5; s; eauto.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 1. econs 6; s; eauto.
  - inv STATE.
    eexists. splits; eauto.
    econs 2; eauto. econs; eauto.
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

Inductive sim_seq (s:list Stmt.t): forall (lhs rhs:Thread.t lang * Memory.t), Prop :=
| sim_seq_intro
    rs stmts commit promise mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) commit promise, mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) commit promise, mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 commit1 promise1 mem1
      rs2 stmts2 commit2 promise2 mem2
      (STEP: rtc (@Thread._internal_step lang)
               (Thread.mk lang (State.mk rs1 stmts1) commit1 promise1, mem1)
               (Thread.mk lang (State.mk rs2 stmts2) commit2 promise2, mem2)):
  rtc (@Thread._internal_step lang)
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 promise1, mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 promise2, mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. inv RA. ss.
    destruct a2. destruct t. destruct state. ss.
    exploit _internal_step_seq; eauto. i.
    eexists. splits; eauto. econs; eauto.
  - econs; eauto.
  - i. des. inv x1. auto.
Unshelve.
  { econs; auto. }
Qed.

Inductive ctx (sim_thread:SIM_THREAD lang lang): SIM_THREAD lang lang :=
| ctx_incl
    sim_terminal
    th1 mem_k_src th2 mem_k_tgt
    (SIM: sim_thread sim_terminal th1 mem_k_src th2 mem_k_tgt):
    ctx sim_thread sim_terminal th1 mem_k_src th2 mem_k_tgt
| ctx_nil
    (sim_regs:SIM_REGS)
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    commit_src commit_tgt promise
    (RS: sim_regs rs_src rs_tgt)
    (COMMIT: Commit.le commit_src commit_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (Thread.mk lang (State.mk rs_src []) commit_src promise) mem_k_src
        (Thread.mk lang (State.mk rs_tgt []) commit_tgt promise) mem_k_tgt
| ctx_instr
    instr regs
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    commit_src commit_tgt
    promise
    (REGS: RegSet.disjoint regs (Instr.regs_of instr))
    (RS: eq_except regs rs_src rs_tgt)
    (COMMIT: Commit.le commit_src commit_tgt):
    ctx sim_thread
        (sim_terminal (eq_except regs))
        (Thread.mk lang (State.mk rs_src [Stmt.instr instr]) commit_src promise) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.instr instr]) commit_tgt promise) mem_k_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src commit_src promise_src mem_k_src
    stmts1_tgt stmts2_tgt rs_tgt commit_tgt promise_tgt mem_k_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (Thread.mk lang (State.mk rs_src stmts1_src) commit_src promise_src) mem_k_src
                      (Thread.mk lang (State.mk rs_tgt stmts1_tgt) commit_tgt promise_tgt) mem_k_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (Thread.mk lang (State.mk rs_src (stmts1_src ++ stmts2_src)) commit_src promise_src) mem_k_src
        (Thread.mk lang (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) commit_tgt promise_tgt) mem_k_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src mem_k_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt mem_k_tgt
    commit_src commit_tgt
    promise
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (COMMIT: Commit.le commit_src commit_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (Thread.mk lang (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) commit_src promise) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) commit_tgt promise) mem_k_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src mem_k_src
    cond_tgt stmts_tgt rs_tgt mem_k_tgt
    commit_src commit_tgt
    promise
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (COMMIT: Commit.le commit_src commit_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (Thread.mk lang (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) commit_src promise) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) commit_tgt promise) mem_k_tgt
.
Hint Constructors ctx.

Lemma ctx_mon: monotone5 ctx.
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

Lemma ctx_weak_respectful: weak_respectful5 (@_sim_thread lang lang) ctx.
Proof.
  econs; auto. i. destruct PR.
  - (* incl *)
    eapply _sim_thread_mon; eauto.
    apply rclo5_incl.
  - (* nil *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. ss. eexists _, _. splits; eauto; econs; ss. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; try inv STATE. ss.
      exploit MemInv.promise; try apply MEMORY; try apply MEM; eauto.
      { apply MemInv.sem_bot. }
      i. des. apply MemInv.sem_bot_inv in INV2. subst.
      eexists _, _, _, _. splits; eauto.
      * instantiate (1 := Thread.mk _ _ _ _).
        econs 1. econs 6; s; eauto.
      * apply rclo5_step. apply ctx_nil; auto.
    + inv STATE.
  - (* instr *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; try inv STATE.
      * exploit eq_except_instr; eauto. i. des.
        generalize MESSAGE. intro X. apply MEMORY in X.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 1; eauto. econs; eauto.
          s. eapply Commit.read_mon; eauto.
        }
        { apply rclo5_step. apply ctx_nil; auto. reflexivity. }
      * exploit eq_except_instr; eauto. i. des.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 2; ss; eauto. econs; eauto.
          s. eapply Commit.write_mon; eauto.
          admit. (* Memory.write *)
        }
        { admit. (* sim_memory *) }
        { apply rclo5_step. apply ctx_nil; auto. reflexivity. }
      * exploit eq_except_instr; eauto. i. des.
        generalize MESSAGE. intro X. apply MEMORY in X.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 3; eauto. econs; eauto.
          s. eapply Commit.read_mon; eauto.
          admit. (* Memory.write *)
        }
        { admit. (* sim_memory *) }
        { apply rclo5_step. apply ctx_nil; auto. reflexivity. }
      * exploit eq_except_instr; eauto. i. des.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 4; eauto. econs; eauto.
          s. eapply Commit.fence_mon; eauto.
        }
        { apply rclo5_step. apply ctx_nil; auto. reflexivity. }
      * exploit eq_except_instr; eauto. i. des.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 5; eauto. econs; eauto. }
        { apply rclo5_step. apply ctx_nil; auto. }
      * exploit MemInv.promise; try apply MEMORY; try apply MEM; eauto.
        { apply MemInv.sem_bot. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _).
          econs 1. econs 6; s; eauto.
        }
        { apply rclo5_step. apply ctx_instr; auto. }
    + inv STATE.
      exploit eq_except_instr; eauto. i. des.
      eexists _, _, _, _. splits; eauto.
      * econs 2; eauto. econs; eauto.
      * apply rclo5_step. apply ctx_nil; auto.
  - (* seq *)
    ii. ss.
    exploit GF; eauto. s. i. des.
    splits; s; i.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      destruct th2_src, state. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_internal_step_future; eauto. s. i. des.
      inv SIM. ss. subst.
      exploit SIM2; eauto. intro TH2.
      exploit GF; eauto. s. i. des.
      exploit TERMINAL0; try by econs. i. des.
      destruct th2_src, state. inv TERMINAL_SRC. ss. subst.
      eexists _, _. splits; [|eauto| | |eauto].
      + etransitivity; [|eauto].
        eapply rtc_internal_step_seq in STEPS. apply STEPS.
      + econs.
      + econs.
    }
    { exploit FUTURE; eauto. }
    { subst. exploit PROMISE; eauto. i. des.
      destruct th2_src, state. ss. subst.
      eexists _, _. splits; [|eauto|eauto].
      + eapply rtc_internal_step_seq. apply STEPS.
      + eauto.
    }
    destruct stmts1_tgt.
    + exploit TERMINAL; try by econs. i. des.
      destruct th2_src, state. inv TERMINAL_SRC. ss. subst.
      exploit Thread.rtc_internal_step_future; eauto. s. i. des.
      inv SIM. ss. subst.
      exploit SIM2; eauto. intro TH2.
      exploit GF; eauto. s. i. des.
      exploit STEP0; eauto. i. des.
      eexists _, _, _, _. splits; [|eauto|eauto|].
      * eapply rtc_internal_step_seq in STEPS.
        etransitivity; [apply STEPS|eauto].
      * apply rclo5_incl. auto.
    + destruct th3_tgt, state.
      exploit thread_step_deseq; eauto. i. des. ss. subst.
      exploit STEP; eauto. i. des.
      destruct th2_src, state. destruct th3_src, state.
      eexists _, _, _, _. splits; [| |eauto|].
      * eapply rtc_internal_step_seq. eauto.
      * eapply thread_step_seq. eauto.
      * apply rclo5_step. eapply ctx_seq; eauto.
        { apply rclo5_incl. eauto. }
        { eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
  - (* ite *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; try inv STATE.
      eexists _, _, _, _. splits; eauto.
      * econs 1. econs 5; eauto. econs.
      * s. rewrite ? app_nil_r.
        exploit COND; eauto. intro C. rewrite C.
        destruct (RegFile.eval_expr rs_tgt cond_tgt).
        { apply rclo5_incl. eauto. }
        { apply rclo5_incl. eauto. }
      * exploit MemInv.promise; try apply MEMORY; try apply MEM; eauto.
        { apply MemInv.sem_bot. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _).
          econs 1. econs 6; s; eauto.
        }
        { apply rclo5_step. eapply ctx_ite; eauto.
          - eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
          - eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
            eapply _sim_stmts_mon; try apply LE; eauto.
        }
    + inv STATE.
  - (* dowhile *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply Memory.splits_future. inv MEMORY. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; try inv STATE.
      eexists _, _, _, _. splits; eauto.
      * econs 1. econs 5; eauto. econs.
      * apply rclo5_step. eapply ctx_seq.
        { apply rclo5_incl. apply LE. eauto. }
        ii. apply rclo5_step. eapply ctx_ite; eauto.
        { ii. apply rclo5_step. eapply ctx_dowhile; eauto.
          eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
        { ii. apply rclo5_base; auto. }
      * exploit MemInv.promise; try apply MEMORY; try apply MEM; eauto.
        { apply MemInv.sem_bot. }
        i. des. apply MemInv.sem_bot_inv in INV2. subst.
        eexists _, _, _, _. splits; eauto.
        { instantiate (1 := Thread.mk _ _ _ _).
          econs 1. econs 6; s; eauto.
        }
        { apply rclo5_step. apply ctx_dowhile; auto.
          eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
    + inv STATE.
Unshelve.
  { admit. }
  { admit. }
  { admit. }
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
  ii. pupto5_init. pupto5 ctx_weak_respectful.
Qed.

Lemma sim_stmts_instr
      instr regs
      (REGS: RegSet.disjoint regs (Instr.regs_of instr)):
  sim_stmts (eq_except regs) [Stmt.instr instr] [Stmt.instr instr] (eq_except regs).
Proof.
  ii. pupto5_init. pupto5 ctx_weak_respectful.
Qed.

Lemma sim_stmts_seq
      sim_regs0 sim_regs1 sim_regs2
      stmts1_src stmts2_src
      stmts1_tgt stmts2_tgt
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs1 stmts2_src stmts2_tgt sim_regs2):
  sim_stmts sim_regs0 (stmts1_src ++ stmts2_src) (stmts1_tgt ++ stmts2_tgt) sim_regs2.
Proof.
  ii. pupto5_init. pupto5 ctx_weak_respectful.
  econs 4.
  - pupto5_final. apply SIM1; auto.
  - ii. pupto5_final. apply SIM2; auto.
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
  ii. pupto5_init. pupto5 ctx_weak_respectful.
  econs 5; eauto.
  - ii. pupto5_final. apply SIM1; auto.
  - ii. pupto5_final. apply SIM2; auto.
Qed.

Lemma sim_stmts_dowhile
      sim_regs
      cond_src stmts_src
      cond_tgt stmts_tgt
      (COND: sim_expr sim_regs cond_src cond_tgt)
      (SIM: sim_stmts sim_regs stmts_src stmts_tgt sim_regs):
  sim_stmts sim_regs [Stmt.dowhile stmts_src cond_src] [Stmt.dowhile stmts_tgt cond_tgt] sim_regs.
Proof.
  ii. pupto5_init. pupto5 ctx_weak_respectful.
  econs 6; eauto. ii. pupto5_final. apply SIM; auto.
Qed.
