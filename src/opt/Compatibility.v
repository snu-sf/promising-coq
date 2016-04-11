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

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Definition SIM_REGS := forall (rs_src rs_tgt:RegFile.t), Prop.

Inductive sim_terminal
          (sim_regs:SIM_REGS)
          (th_src th_tgt:Thread.t lang): Prop :=
| sim_terminal_intro
    (REGS: sim_regs th_src.(Thread.state).(State.regs) th_tgt.(Thread.state).(State.regs))
    (COMMIT: th_src.(Thread.commit) = th_tgt.(Thread.commit))
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
  forall rs_src rs_tgt commit local mem_k_src mem_k_tgt
    (RS: sim_regs0 rs_src rs_tgt),
    sim_thread
      (sim_terminal sim_regs1)
      (Thread.mk lang (State.mk rs_src stmts_src) commit local) mem_k_src
      (Thread.mk lang (State.mk rs_tgt stmts_tgt) commit local) mem_k_tgt.

Lemma _sim_stmts_mon
      s1 s2 (S: s1 <5= s2):
  _sim_stmts s1 <4= _sim_stmts s2.
Proof.
  ii. apply S. apply PR. auto.
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

Lemma thread_step_seq
      stmts e
      rs1 stmts1 commit1 local1 mem1
      rs2 stmts2 commit2 local2 mem2
      (STEP: Thread.step e
               (Thread.mk lang (State.mk rs1 stmts1) commit1 local1) mem1
               (Thread.mk lang (State.mk rs2 stmts2) commit2 local2) mem2):
  Thread.step e
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 local1) mem1
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 local2) mem2.
Proof.
  inv STEP.
  - econs 1. inv STEP0; ss.
    + econs 1; s; eauto. apply step_seq. auto.
    + econs 2; s; eauto. apply step_seq. auto.
    + econs 3; s; eauto. apply step_seq. auto.
    + econs 4; s; eauto. apply step_seq. auto.
    + econs 5; s; eauto. apply step_seq. auto.
  - econs 2. inv STEP0; ss.
    + inv STATE. econs 1; eauto.
    + inv STATE. econs 2; eauto.
  - econs 3; eauto. inv STATE. econs; eauto.
Qed.

Lemma internal_step_seq
      stmts
      rs1 stmts1 commit1 local1 mem1
      rs2 stmts2 commit2 local2 mem2
      (STEP: Thread.internal_step
               (Thread.mk lang (State.mk rs1 stmts1) commit1 local1, mem1)
               (Thread.mk lang (State.mk rs2 stmts2) commit2 local2, mem2)):
  Thread.internal_step
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 local1, mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 local2, mem2).
Proof.
  econs. ss.
  eapply thread_step_seq; eauto.
  inv STEP; eauto.
Qed.

Lemma thread_step_deseq
      stmts e
      rs1 stmt1 stmts1 commit1 local1 mem1
      rs2 stmts2 commit2 local2 mem2
      (STEP: Thread.step e
                         (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1 ++ stmts)) commit1 local1) mem1
                         (Thread.mk lang (State.mk rs2 stmts2) commit2 local2) mem2):
  exists stmts2',
    stmts2 = stmts2' ++ stmts /\
  Thread.step e
              (Thread.mk lang (State.mk rs1 (stmt1 :: stmts1)) commit1 local1) mem1
              (Thread.mk lang (State.mk rs2 stmts2') commit2 local2) mem2.
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
  - inv STEP0; ss; inv STATE.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 2. econs 1; eauto.
    + rewrite app_comm_cons.
      eexists. splits; eauto.
      econs 2. econs 2; eauto.
  - inv STATE.
    eexists. splits; eauto.
    econs 3; eauto. econs; eauto.
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
    rs stmts commit local mem:
    sim_seq s
            (Thread.mk lang (State.mk rs stmts) commit local, mem)
            (Thread.mk lang (State.mk rs (stmts ++ s)) commit local, mem)
.

Lemma rtc_internal_step_seq
      stmts
      rs1 stmts1 commit1 local1 mem1
      rs2 stmts2 commit2 local2 mem2
      (STEP: rtc (@Thread.internal_step lang)
               (Thread.mk lang (State.mk rs1 stmts1) commit1 local1, mem1)
               (Thread.mk lang (State.mk rs2 stmts2) commit2 local2, mem2)):
  rtc (@Thread.internal_step lang)
    (Thread.mk lang (State.mk rs1 (stmts1 ++ stmts)) commit1 local1, mem1)
    (Thread.mk lang (State.mk rs2 (stmts2 ++ stmts)) commit2 local2, mem2).
Proof.
  exploit (sim_rtc (sim_seq stmts)); eauto.
  - i. inv SIM1. inv RA. ss.
    destruct a2. destruct t. destruct state. ss.
    exploit internal_step_seq; eauto. i.
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
    commit local
    (RS: sim_regs rs_src rs_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (Thread.mk lang (State.mk rs_src []) commit local) mem_k_src
        (Thread.mk lang (State.mk rs_tgt []) commit local) mem_k_tgt
| ctx_instr
    (sim_regs:SIM_REGS)
    instr
    (REGS: forall reg (REG: RegSet.mem reg (Instr.regs_of instr))
             rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
        rs_src reg = rs_tgt reg)
    rs_src mem_k_src
    rs_tgt mem_k_tgt
    commit local
    (RS: sim_regs rs_src rs_tgt):
    ctx sim_thread
        (sim_terminal sim_regs)
        (Thread.mk lang (State.mk rs_src [Stmt.instr instr]) commit local) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.instr instr]) commit local) mem_k_tgt
| ctx_seq
    sim_regs1 sim_regs2
    stmts1_src stmts2_src rs_src commit_src local_src mem_k_src
    stmts1_tgt stmts2_tgt rs_tgt commit_tgt local_tgt mem_k_tgt
    (SIM1: sim_thread (sim_terminal sim_regs1)
                      (Thread.mk lang (State.mk rs_src stmts1_src) commit_src local_src) mem_k_src
                      (Thread.mk lang (State.mk rs_tgt stmts1_tgt) commit_tgt local_tgt) mem_k_tgt)
    (SIM2: _sim_stmts sim_thread sim_regs1 stmts2_src stmts2_tgt sim_regs2):
    ctx sim_thread
        (sim_terminal sim_regs2)
        (Thread.mk lang (State.mk rs_src (stmts1_src ++ stmts2_src)) commit_src local_src) mem_k_src
        (Thread.mk lang (State.mk rs_tgt (stmts1_tgt ++ stmts2_tgt)) commit_tgt local_tgt) mem_k_tgt
| ctx_ite
    sim_regs0 sim_regs1
    cond_src stmts1_src stmts2_src rs_src mem_k_src
    cond_tgt stmts1_tgt stmts2_tgt rs_tgt mem_k_tgt
    commit local
    (COND: sim_expr sim_regs0 cond_src cond_tgt)
    (RS: sim_regs0 rs_src rs_tgt)
    (SIM1: _sim_stmts sim_thread sim_regs0 stmts1_src stmts1_tgt sim_regs1)
    (SIM2: _sim_stmts sim_thread sim_regs0 stmts2_src stmts2_tgt sim_regs1):
    ctx sim_thread
        (sim_terminal sim_regs1)
        (Thread.mk lang (State.mk rs_src [Stmt.ite cond_src stmts1_src stmts2_src]) commit local) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.ite cond_tgt stmts1_tgt stmts2_tgt]) commit local) mem_k_tgt
| ctx_dowhile
    sim_regs
    cond_src stmts_src rs_src mem_k_src
    cond_tgt stmts_tgt rs_tgt mem_k_tgt
    commit local
    (COND: sim_expr sim_regs cond_src cond_tgt)
    (RS: sim_regs rs_src rs_tgt)
    (SIM: _sim_stmts sim_thread sim_regs stmts_src stmts_tgt sim_regs):
    ctx sim_thread
        (sim_terminal sim_regs)
        (Thread.mk lang (State.mk rs_src [Stmt.dowhile stmts_src cond_src]) commit local) mem_k_src
        (Thread.mk lang (State.mk rs_tgt [Stmt.dowhile stmts_tgt cond_tgt]) commit local) mem_k_tgt
.
Hint Constructors ctx.

Lemma ctx_mon: monotone5 ctx.
Proof.
  ii. inv IN.
  - econs 1. auto.
  - econs 2. auto.
  - econs 3; eauto; eapply _sim_stmts_mon; eauto.
  - econs 4; eauto; eapply _sim_stmts_mon; eauto.
  - econs 5; eauto; eapply _sim_stmts_mon; eauto.
  - econs 6; eauto; eapply _sim_stmts_mon; eauto.
Qed.
Hint Resolve ctx_mon.

Lemma sim_memory_add_new
      mem1_src mem1_tgt mem2_tgt
      loc from to msg
      (ADD: Memory.add_new loc from to msg mem1_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  exists mem2_src,
    <<ADD: Memory.add_new loc from to msg mem1_src mem2_src>> /\
    <<SIM: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv ADD. destruct (Cell.add_new_iff from to msg (mem1_tgt loc)) as [DECL _].
  exploit DECL; eauto. clear DECL. i. des.
  destruct (Cell.add_new_iff from to msg (mem1_src loc)) as [_ DECL].
  exploit DECL; eauto.
  { splits; auto. ii. eapply OWN; eauto. apply SIM. auto. }
  clear DECL. i. des.
  eexists. splits.
  - econs. eauto.
  - admit. (* sim_memory *)
Admitted.

Lemma sim_memory_add_split
      mem1_src mem1_tgt mem2_tgt
      loc from to to' msg msg'
      (TO: Memory.get loc to mem1_src = None)
      (ADD: Memory.add_split loc from to to' msg msg' mem1_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  exists from'' to'' msg'' mem2_src,
    <<ADD: Memory.add_split loc from'' to to'' msg msg'' mem1_src mem2_src>> /\
    <<SIM: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv ADD. destruct (Cell.add_split_iff from to to' msg msg' (mem1_tgt loc)) as [DECL _].
  exploit DECL; eauto. clear DECL. i. des.
  assert (Memory.own mem1_tgt loc to).
  { econs; eauto. econs; eauto. s. apply Time.le_lteq. auto. }
  inv SIM. apply OWNERSHIP in H. inv H.
  destruct (Cell.add_split_iff from0 to to0 msg msg0 (mem1_src loc)) as [_ DECL].
  exploit DECL; eauto.
  { inv INTERVAL. ss. splits; auto.
    apply Time.le_lteq in TO1. des; auto. subst.
    unfold Memory.get, Cell.get in TO. rewrite MESSAGE in TO. ss.
  }
  i. des.
  eexists _, _, _, _. splits.
  - econs. eauto.
  - admit. (* sim_memory *)
Admitted.

Lemma sim_add
      lang_src st1_src mem1_src
      lang_tgt st1_tgt mem1_tgt th2_tgt mem2_tgt
      commit1 local1
      (SIM: sim_memory mem1_src mem1_tgt)
      (LE1_SRC: Memory.le local1 mem1_src)
      (LE1_TGT: Memory.le local1 mem1_tgt)
      (STEP: Thread.add_step (Thread.mk lang_tgt st1_tgt commit1 local1) mem1_tgt
                             th2_tgt mem2_tgt):
  exists commit2 local2 mem2_src,
    <<TH2: th2_tgt = Thread.mk lang_tgt st1_tgt commit2 local2>> /\
    <<SIM: sim_memory mem2_src mem2_tgt>> /\
    <<COMMIT: Commit.le commit1 commit2>> /\
    <<ADD: Thread.add_step (Thread.mk lang_src st1_src commit1 local1) mem1_src
                           (Thread.mk lang_src st1_src commit2 local2) mem2_src>>.
Proof.
  destruct th2_tgt. inv STEP; ss.
  - exploit sim_memory_add_new; try apply LOCAL0; eauto. i. des.
    exploit sim_memory_add_new; try apply MEMORY; eauto. i. des.
    eexists _, _, _. splits; eauto.
    econs 1; eauto.
  - exploit Memory.add_split_le; eauto. i. des.
    exploit Memory.add_split_unique; [apply MEMORY|apply ADD_SPLIT2|].
    i. des. subst. clear ADD_SPLIT2.
    exploit sim_memory_add_split; try apply MEMORY; eauto.
    { inv LOCAL.
      destruct (Cell.add_split_iff from to to' msg msg' (local1 loc)) as [DECL _].
      exploit DECL; eauto. clear DECL. i. des.
      destruct (Memory.get loc to mem1_src) eqn:X; [|auto].
      unfold Memory.get, Cell.get in X.
      destruct (Cell.messages (mem1_src loc) to) as [[]|] eqn:Y; inv X.
      apply LE1_SRC in MSG.
      exfalso. eapply (@Cell.DISJOINT (mem1_src loc) to to'); eauto.
      - ii. subst. apply Time.lt_strorder in TO'. inv TO'.
      - apply Interval.mem_ub. eapply Cell.VOLUME. eauto.
      - econs; eauto. s. apply Time.le_lteq. auto.
    }
    i. des.
    exploit Memory.add_split_le; try apply LE1_SRC; eauto. i. des.
    exploit Memory.add_split_unique; [apply ADD|apply ADD_SPLIT2|].
    i. des. subst. clear ADD_SPLIT2.
    eexists _, _, _. splits; eauto.
    econs 2; eauto.
Qed.

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
      etransitivity; eauto. apply sim_memory_future. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; inv STATE.
    + exploit sim_add; try apply STEP; eauto. i. des. subst.
      eexists _, _, _, _. splits; eauto.
      * econs 2. eauto.
      * apply rclo5_step. apply ctx_nil. auto.
    + inv STATE.
  - (* instr *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply sim_memory_future. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; inv STATE.
      * generalize MESSAGE. intro X. apply MEMORY in X.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 1; eauto. econs. admit. (* regs *) }
        { apply rclo5_step. apply ctx_nil. admit. (* regs *) }
      * eexists _, _, _, _. splits; eauto.
        { econs 1. econs 2; eauto. econs. admit. (* regs *) }
        { apply rclo5_step. apply ctx_nil. admit. (* regs *) }
      * generalize MESSAGE1. intro X. apply MEMORY in X.
        eexists _, _, _, _. splits; eauto.
        { econs 1. econs 3; eauto. econs. admit. (* regs *) }
        { apply rclo5_step. apply ctx_nil. admit. (* regs *) }
      * eexists _, _, _, _. splits; eauto.
        { econs 1. econs 4; eauto. econs. admit. (* regs *) }
        { apply rclo5_step. apply ctx_nil. admit. (* regs *) }
      * eexists _, _, _, _. splits; eauto.
        { econs 1. econs 5; eauto. econs. admit. (* regs *) }
        { apply rclo5_step. apply ctx_nil. admit. (* regs *) }
    + exploit sim_add; eauto. i. des. subst.
      eexists _, _, _, _. splits; eauto.
      * econs 2. eauto.
      * apply rclo5_step. apply ctx_instr; auto.
    + inv STATE.
      eexists _, _, _, _. splits; eauto.
      * econs 3; eauto. econs. admit. (* regs *)
      * apply rclo5_step. apply ctx_nil. admit. (* regs *)
  - (* seq *)
    ii. ss.
    exploit GF; eauto. s. i. des.
    splits; s; i.
    { inv TERMINAL_TGT. destruct stmts1_tgt, stmts2_tgt; inv H0.
      exploit TERMINAL; try by econs. i. des.
      destruct th2_src, state. inv TERMINAL_SRC. ss. subst.
      exploit Thread.future_rtc_internal_step; eauto. s. i. des.
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
    { subst. exploit LOCAL; eauto. i. des.
      destruct th2_src, state. ss. subst.
      eexists _, _. splits; [|eauto|eauto].
      + eapply rtc_internal_step_seq. apply STEPS.
      + eauto.
    }
    destruct stmts1_tgt.
    + exploit TERMINAL; try by econs. i. des.
      destruct th2_src, state. inv TERMINAL_SRC. ss. subst.
      exploit Thread.future_rtc_internal_step; eauto. s. i. des.
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
      etransitivity; eauto. apply sim_memory_future. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; inv STATE.
      eexists _, _, _, _. splits; eauto.
      * econs 1. econs 5; eauto. econs.
      * s. rewrite ? app_nil_r.
        exploit COND; eauto. intro C. rewrite C.
        destruct (RegFile.eval_expr rs_tgt cond_tgt).
        { apply rclo5_incl. eauto. }
        { apply rclo5_incl. eauto. }
    + exploit sim_add; eauto. i. des. subst.
      eexists _, _, _, _. splits; eauto.
      * econs 2. eauto.
      * apply rclo5_step. eapply ctx_ite; eauto.
        { eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
        { eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
          eapply _sim_stmts_mon; try apply LE; eauto.
        }
    + inv STATE.
  - (* dowhile *)
    ii. splits; s; i.
    { inv TERMINAL_TGT. }
    { ss. eexists. splits; try reflexivity; eauto.
      etransitivity; eauto. apply sim_memory_future. auto.
    }
    { ss. subst. eexists _, _. splits; eauto. }
    inv STEP_TGT; ss.
    + inv STEP; ss; inv STATE.
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
    + exploit sim_add; eauto. i. des. subst.
      eexists _, _, _, _. splits; eauto.
      * econs 2. eauto.
      * apply rclo5_step. apply ctx_dowhile; auto.
        eapply _sim_stmts_mon; try apply rclo5_incl; eauto.
        eapply _sim_stmts_mon; try apply LE; eauto.
    + inv STATE.
Admitted.

Definition sim_stmts := @_sim_stmts (paco5 (@_sim_thread lang lang <*> grespectful5 (@_sim_thread lang lang)) bot5).

Lemma sim_stmts_nil sim_regs:
  sim_stmts sim_regs [] [] sim_regs.
Proof.
  ii. pupto5 ctx_weak_respectful.
Qed.

Lemma sim_stmts_instr
      (sim_regs:SIM_REGS) instr
      (REGS: forall reg (REG: RegSet.mem reg (Instr.regs_of instr))
               rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
          rs_src reg = rs_tgt reg):
  sim_stmts sim_regs [Stmt.instr instr] [Stmt.instr instr] sim_regs.
Proof.
  ii. pupto5 ctx_weak_respectful.
Qed.

Lemma sim_stmts_seq
      sim_regs0 sim_regs1 sim_regs2
      stmts1_src stmts2_src
      stmts1_tgt stmts2_tgt
      (SIM1: sim_stmts sim_regs0 stmts1_src stmts1_tgt sim_regs1)
      (SIM2: sim_stmts sim_regs1 stmts2_src stmts2_tgt sim_regs2):
  sim_stmts sim_regs0 (stmts1_src ++ stmts2_src) (stmts1_tgt ++ stmts2_tgt) sim_regs2.
Proof.
  ii. pupto5 ctx_weak_respectful.
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
  ii. pupto5 ctx_weak_respectful.
Qed.

Lemma sim_stmts_dowhile
      sim_regs
      cond_src stmts_src
      cond_tgt stmts_tgt
      (COND: sim_expr sim_regs cond_src cond_tgt)
      (SIM: sim_stmts sim_regs stmts_src stmts_tgt sim_regs):
  sim_stmts sim_regs [Stmt.dowhile stmts_src cond_src] [Stmt.dowhile stmts_tgt cond_tgt] sim_regs.
Proof.
  ii. pupto5 ctx_weak_respectful.
Qed.
