Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import ConfigurationRR.
Require Import Simulation.
Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)
(* TODO: now supporting only the reordering of single thread *)

Inductive reordered_instr: forall (i1 i2:Instr.t), Prop :=
| reordered_instr_load_store
    r1 l1 o1
    l2 v2 o2
    (LOC: l1 <> l2)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1)) (Instr.regs_of (Instr.store l2 v2 o2)))
    (ORDERING1: ~ Ordering.le Ordering.acquire o1)
    (ORDERING1: ~ Ordering.le Ordering.release o2):
    reordered_instr (Instr.load r1 l1 o1) (Instr.store l2 v2 o2)
.

Inductive reordered_stmt: forall (s1 s2:Stmt.t), Prop :=
| reordered_stmt_instr i:
    reordered_stmt
      (Stmt.instr i)
      (Stmt.instr i)
| reordered_stmt_ite
    cond c11 c12 c21 c22
    (REORDER1: reordered_stmts c11 c21)
    (REORDER2: reordered_stmts c12 c22):
    reordered_stmt
      (Stmt.ite cond c11 c12)
      (Stmt.ite cond c21 c22)
| reordered_stmt_dowhile
    cond c1 c2
    (REORDER2: reordered_stmts c1 c2):
    reordered_stmt
      (Stmt.dowhile c1 cond)
      (Stmt.dowhile c2 cond)

with reordered_stmts: forall (s1 s2:list Stmt.t), Prop :=
| reordered_stmts_nil:
    reordered_stmts nil nil
| reordered_stmts_cons
    s11 s12 s21 s22
    (REORDER1: reordered_stmt s11 s21)
    (REORDER2: reordered_stmts s12 s22):
    reordered_stmts (s11::s12) (s21::s22)
| reordered_stmts_reorder
    i1 i2 s1 s2
    (REORDER: reordered_instr i1 i2)
    (REORDER: reordered_stmts s1 s2):
    reordered_stmts
      ((Stmt.instr i1)::(Stmt.instr i2)::s1)
      ((Stmt.instr i2)::(Stmt.instr i1)::s2)
.

Scheme reordered_stmt_ind_ := Induction for reordered_stmt Sort Prop
with reordered_stmts_ind_ := Induction for reordered_stmts Sort Prop.
Combined Scheme reordered_ind from reordered_stmt_ind_, reordered_stmts_ind_.

Inductive reordered_thread: forall (text1 text2:Thread.syntax), Prop :=
| reordered_thread_intro
    s1 s2
    (REORDER: reordered_stmts s1 s2):
    reordered_thread
      (Thread.mk_syntax lang s1)
      (Thread.mk_syntax lang s2)
.

Inductive reordered_program tid: forall (prog1 prog2:Configuration.syntax), Prop :=
| reordered_program_intro
    prog1 th1 th2
    (TH1: IdentMap.find tid prog1 = Some th1)
    (REORDER: reordered_thread th1 th2):
    reordered_program tid prog1 (IdentMap.add tid th2 prog1)
.

Inductive sim_reordered_thread: forall (th1 th2:Thread.t), Prop :=
| sim_reordered_thread_intro
    rs s1 s2
    (REORDER: reordered_stmts s1 s2):
    sim_reordered_thread
      (Thread.mk lang (State.mk rs s1))
      (Thread.mk lang (State.mk rs s2))
.

(* TODO: refactoring *)
Lemma sim_reordered_thread_inv
      th1 th2 (SIM: sim_reordered_thread th1 th2):
  exists rs s1 s2,
    th1 = Thread.mk lang (State.mk rs s1) /\
    th2 = Thread.mk lang (State.mk rs s2) /\
    reordered_stmts s1 s2.
Proof.
  inv SIM. eexists _, _, _. splits; eauto.
Qed.

Inductive sim_consumed_thread (e:option MemEvent.t): forall (th1 th2' th2:Thread.t), Prop :=
| sim_consumed_thread_intro
    i1 i2 rs1 rs2 s1 s2 tid
    (REORDER: reordered_instr i1 i2)
    (REORDER: reordered_stmts s1 s2)
    (EVAL: RegFile.eval_instr rs1 tid (option_map ThreadEvent.mem e) rs2):
    sim_consumed_thread
      e
      (Thread.mk lang (State.mk rs1 ((Stmt.instr i1)::(Stmt.instr i2)::s1)))
      (Thread.mk lang (State.mk rs1 ((Stmt.instr i2)::(Stmt.instr i1)::s2)))
      (Thread.mk lang (State.mk rs2 ((Stmt.instr i1)::s2)))
.

(* TODO: refactoring *)
Lemma sim_consumed_thread_inv
      e th1 th2' th2 (SIM: sim_consumed_thread e th1 th2' th2):
  exists i1 i2 rs1 rs2 s1 s2 tid,
    th1 = Thread.mk lang (State.mk rs1 ((Stmt.instr i1)::(Stmt.instr i2)::s1)) /\
    th2' = Thread.mk lang (State.mk rs1 ((Stmt.instr i2)::(Stmt.instr i1)::s2)) /\
    th2 = Thread.mk lang (State.mk rs2 ((Stmt.instr i1)::s2)) /\
    reordered_instr i1 i2 /\
    reordered_stmts s1 s2 /\
    RegFile.eval_instr rs1 tid (option_map ThreadEvent.mem e) rs2.
Proof.
  inv SIM. eexists _, _, _, _, _, _, _. splits; eauto.
Qed.

Inductive sim_thread m1 m2 commit1 commit2 th1 th2: Prop :=
| sim_thread_reordered
    (TH: sim_reordered_thread th1 th2)
    (MESSAGES: m1 = m2)
    (COMMIT: commit1 = commit2)
| sim_thread_consumed
    th2' reading e
    (TH: sim_consumed_thread e th1 th2' th2)
    (MESSAGES: Commit.step commit1 m1 reading e commit2 m2)
.

Inductive sim_configuration (tid:Ident.t) (conf1 conf2:Configuration.t): Prop :=
| sim_configuration_intro
    commit1 commit2 th1 th2
    (CONTEXT: forall i (TID: i <> tid),
        IdentMap.find i conf1.(Configuration.threads) = IdentMap.find i conf2.(Configuration.threads))
    (TH1: IdentMap.find tid conf1.(Configuration.threads) = Some (commit1, th1))
    (TH2: IdentMap.find tid conf2.(Configuration.threads) = Some (commit2, th2))
    (TH: sim_thread conf1.(Configuration.messages) conf2.(Configuration.messages) commit1 commit2 th1 th2)
.

Lemma sim_init
      tid prog_src prog_tgt
      (REORDER: reordered_program tid prog_src prog_tgt):
  Simulation.INIT (sim_configuration tid) prog_src prog_tgt.
Proof.
  inv REORDER. unfold Simulation.INIT, Configuration.init.
  econs; simpl; eauto.
  - i. rewrite ? IdentMap.Facts.map_o.
    rewrite IdentMap.Facts.add_neq_o; auto.
  - rewrite IdentMap.Facts.map_o.
    rewrite TH1. simpl. eauto.
  - rewrite IdentMap.Facts.map_o.
    rewrite IdentMap.Facts.add_eq_o; auto. simpl. eauto.
  - inv REORDER0. econs; eauto. econs; eauto.
Qed.

Lemma sim_consistent tid: Simulation.CONSISTENT (sim_configuration tid).
Proof.
  ii. inv SIM. inv TH.
  - econs.
    + econs 1.
    + rewrite MESSAGES. auto.
  - admit. (* consumed *)
Admitted.

Lemma sim_base tid: Simulation.BASE_STEP (sim_configuration tid).
Proof.
  ii. inv SIM. inv TH.
  - (* reordered *)
    inv STEP.
    + (* thread *)
      admit.
    + (* declare *)
      eexists _, _. splits; eauto.
      * apply Configuration.step_confirmed.
        eapply Configuration.step_declare.
        rewrite MESSAGES. eauto.
      * econs; eauto. apply sim_thread_reordered; eauto.
    + (* commit *)
      destruct (Ident.eq_dec tid0 tid).
      * subst. rewrite TH2 in TID. inv TID.
        eexists _, _. splits; eauto.
        { apply Configuration.step_confirmed.
          eapply Configuration.step_commit; eauto.
        }
        { econs; simpl; eauto.
          - i. rewrite ? IdentMap.Facts.add_neq_o; eauto.
          - rewrite IdentMap.Facts.add_eq_o; eauto.
          - rewrite IdentMap.Facts.add_eq_o; eauto.
          - apply sim_thread_reordered; eauto.
        }
      * exploit CONTEXT; eauto. intro X.
        eexists _, _. splits; eauto.
        { apply Configuration.step_confirmed.
          eapply Configuration.step_commit; [|eauto].
          rewrite X. eauto.
        }
        { econs; simpl; eauto.
          - i. rewrite ? IdentMap.Facts.add_o.
            destruct (IdentMap.Facts.eq_dec tid0 i); eauto.
          - rewrite IdentMap.Facts.add_neq_o; eauto.
          - rewrite IdentMap.Facts.add_neq_o; eauto.
          - apply sim_thread_reordered; eauto.
        }
  - (* consumed *)
    inv STEP.
    + (* thread *)
      admit.
    + (* declare *)
      admit.
    + (* commit *)
      destruct (Ident.eq_dec tid0 tid).
      * subst. rewrite TH2 in TID. inv TID.
        eexists _, _. splits; eauto.
        { apply Configuration.step_confirmed.
          eapply Configuration.step_commit; eauto.
          admit.
        }
        { econs; simpl; eauto.
          - i. rewrite ? IdentMap.Facts.add_neq_o; eauto.
          - rewrite IdentMap.Facts.add_eq_o; eauto.
          - rewrite IdentMap.Facts.add_eq_o; eauto.
          - apply sim_thread_reordered; eauto.
            admit.
            admit.
        }
      * exploit CONTEXT; eauto. intro X.
        eexists _, _. splits; eauto.
        { apply Configuration.step_confirmed.
          eapply Configuration.step_commit; [|eauto].
          rewrite X. eauto.
        }
        { econs; simpl; eauto.
          - i. rewrite ? IdentMap.Facts.add_o.
            destruct (IdentMap.Facts.eq_dec tid0 i); eauto.
          - rewrite IdentMap.Facts.add_neq_o; eauto.
          - rewrite IdentMap.Facts.add_neq_o; eauto.
          - apply sim_thread_reordered; eauto.
            admit.
            admit.
            admit.
        }
Admitted.

Lemma sim_external tid: Simulation.EXTERNAL_STEP (sim_configuration tid).
Proof.
Admitted.

Lemma sim_terminal tid: Simulation.TERMINAL (sim_configuration tid).
Proof.
  ii. eexists. split.
  { econs 1. }
  econs. i. inv TERM. specialize (TERMINAL tid0).
  destruct (Ident.eq_dec tid0 tid); subst.
  - inv SIM. rewrite FIND in TH1. inv TH1.
    exploit TERMINAL; eauto. inv TH.
    + inv TH0.
      unfold Thread.is_terminal. simpl.
      unfold State.is_terminal. simpl.
      inv REORDER; congruence.
    + inv TH0.
      unfold Thread.is_terminal. simpl.
      unfold State.is_terminal. simpl.
      congruence.
  - inv SIM. exploit CONTEXT; eauto. intro FIND0.
    eapply TERMINAL. rewrite <- FIND0. eauto.
Qed.

Lemma sim tid:
  reordered_program tid <2= Simulation.t.
Proof.
  i. eapply Simulation.sim_lemma.
  - apply sim_init. eauto.
  - apply sim_consistent.
  - apply sim_base.
  - apply sim_external.
  - apply sim_terminal.
Qed.
