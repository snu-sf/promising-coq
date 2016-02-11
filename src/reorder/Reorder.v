Require Import Bool.
Require Import List.
Require Import ProofIrrelevance.

Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Syntax.
Require Import Semantics.
Require Import Thread.
Require Import Memory.
Require Import Configuration.
Require Import Program.
Require Import Simulation.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)

Definition reorderable_message (msg1 msg2:Message.t): bool :=
  match msg1, msg2 with
  | Message.rw (RWEvent.read l1 c1 o1) t1,
    Message.rw (RWEvent.write l2 c2 o2) t2 =>
    (negb (Loc.eqb l1 l2)) &&
    (negb (Ordering.ord Ordering.acquire o1)) &&
    (negb (Ordering.ord Ordering.release o2))
  | _, _ =>
    false
  end.

Definition reorderable_instr (i1 i2:Instr.t): bool :=
  match i1, i2 with
  | Instr.load r1 l1 o1,
    Instr.store l2 v2 o2 =>
    (negb (Loc.eqb l1 l2)) &&
    (RegSet.is_empty (RegSet.inter (Instr.regs_of i1) (Instr.regs_of i2))) &&
    (negb (Ordering.ord Ordering.acquire o1)) &&
    (negb (Ordering.ord Ordering.release o2))
  | _, _ =>
    false
  end.

Inductive trans_stmt: forall (s1 s2:Stmt.t), Prop :=
| trans_stmt_instr i:
    trans_stmt
      (Stmt.instr i)
      (Stmt.instr i)
| trans_stmt_ite
    cond c11 c12 c21 c22
    (TRANS1: trans_stmts c11 c21)
    (TRANS2: trans_stmts c12 c22):
    trans_stmt
      (Stmt.ite cond c11 c12)
      (Stmt.ite cond c21 c22)
| trans_stmt_dowhile
    cond c1 c2
    (TRANS2: trans_stmts c1 c2):
    trans_stmt
      (Stmt.dowhile c1 cond)
      (Stmt.dowhile c2 cond)

with trans_stmts: forall (s1 s2:list Stmt.t), Prop :=
| trans_stmts_nil:
    trans_stmts nil nil
| trans_stmts_cons
    s11 s12 s21 s22
    (TRANS1: trans_stmt s11 s21)
    (TRANS2: trans_stmts s12 s22):
    trans_stmts (s11::s12) (s21::s22)
| trans_stmts_reorder
    i1 i2 s1 s2
    (REORDER: reorderable_instr i1 i2)
    (TRANS: trans_stmts s1 s2):
    trans_stmts
      ((Stmt.instr i1)::(Stmt.instr i2)::s1)
      ((Stmt.instr i2)::(Stmt.instr i1)::s2)
.

Scheme trans_stmt_ind_ := Induction for trans_stmt Sort Prop
with trans_stmts_ind_ := Induction for trans_stmts Sort Prop.
Combined Scheme trans_ind from trans_stmt_ind_, trans_stmts_ind_.

Inductive trans_prog_thread: forall (text1 text2:Program.thread_t), Prop :=
| trans_prog_thread_intro
    s1 s2
    (TRANS: trans_stmts s1 s2):
    trans_prog_thread
      (Program.thread_mk lang s1)
      (Program.thread_mk lang s2)
.

Inductive trans_prog (prog1 prog2:Program.t): Prop :=
| trans_prog_intro
    (TRANS: IdentMap.rel2 trans_prog_thread prog1 prog2)
.

Inductive consumed (i2:Instr.t): forall (c1 c2:list Stmt.t), Prop :=
| consumed_intro
    i1 c1 c2
    (REORDER: reorderable_instr i1 i2)
    (TRANS: trans_stmts c1 c2):
    consumed i2 ((Stmt.instr i1)::(Stmt.instr i2)::c1) ((Stmt.instr i1)::c2)
.

Inductive sim_thread: forall (e:option ThreadEvent.t) (th1 th2:Thread.t), Prop :=
| sim_thread_trans
    rs s1 s2
    (TRANS: trans_stmts s1 s2):
    sim_thread
      None
      (Thread.mk lang (State.mk rs s1))
      (Thread.mk lang (State.mk rs s2))
| sim_thread_consumed
    rs1 rs2 s1 s2 i e
    (CONSUMED: consumed i s1 s2)
    (EVAL: RegFile.eval_instr rs1 i e rs2):
    sim_thread
      e
      (Thread.mk lang (State.mk rs1 s1))
      (Thread.mk lang (State.mk rs2 s2))
.

Inductive sim_history: forall (b1 b2:list Message.t), Prop :=
| sim_history_nil:
    sim_history nil nil
| sim_history_cons
    msg b1 b2
    (HISTORY: sim_history b1 b2):
    sim_history (b1 ++ [msg]) (b2 ++ [msg])
| sim_history_reorder
    msg1 msg2 b1 b2
    (MSG: reorderable_message msg1 msg2)
    (HISTORY: sim_history b1 b2):
    sim_history (b1 ++ [msg1; msg2]) (b2 ++ [msg2; msg1])
.

Inductive sim_buffer: forall (e:option ThreadEvent.t) (b1 b2:Buffer.t), Prop :=
| sim_buffer_trans
    history1 history2 inception
    (HISTORY: sim_history history1 history2):
    sim_buffer
      None
      (Buffer.mk history1 inception)
      (Buffer.mk history2 inception)
| sim_buffer_consumed_observable
    msg history1 history2 inception2
    (HISTORY: sim_history history1 history2)
    (OBSERVABLE: Message.observable msg):
    sim_buffer
      (Some (Message.get_threadevent msg))
      (Buffer.mk history1 (MessageSet.add msg inception2))
      (Buffer.mk (history2 ++ [msg]) inception2)
| sim_buffer_consumed_unobservable
    msg history1 history2 inception
    (HISTORY: sim_history history1 history2)
    (UNOBSERVABLE: ~ Message.observable msg):
    sim_buffer
      (Some (Message.get_threadevent msg))
      (Buffer.mk history1 inception)
      (Buffer.mk (history2 ++ [msg]) inception)
.

Inductive sim_thread_buffer: forall (th1 th2:option Thread.t) (b1 b2:option Buffer.t), Prop :=
| sim_thread_buffer_None:
    sim_thread_buffer None None None None
| sim_thread_buffer_Some
    th1 th2 b1 b2 e
    (THREAD: sim_thread e th1 th2)
    (BUFFER: sim_buffer e b1 b2):
    sim_thread_buffer (Some th1) (Some th2) (Some b1) (Some b2)
.

Definition sim_threads_memory (th1 th2:Threads.t) (m1 m2:Memory.t): Prop :=
  forall i,
    <<SIM: sim_thread_buffer
             (IdentMap.find i th1) (IdentMap.find i th2)
             (IdentMap.find i m1) (IdentMap.find i m2)>>.

Inductive sim_configuration (c1 c2:Configuration.t): Prop :=
| sim_configuration_intro
    (CLOCKS: Clocks.le c1.(Configuration.clocks) c2.(Configuration.clocks))
    (CUR: sim_threads_memory
            c1.(Configuration.threads) c2.(Configuration.threads)
            c1.(Configuration.memory) c2.(Configuration.memory))
    (STACK:
       Forall2
         (fun stk1 stk2 => sim_threads_memory stk1.(fst) stk2.(fst) stk1.(snd) stk2.(snd))
         c1.(Configuration.stack) c2.(Configuration.stack))
.

Lemma sim_load_thread
      text_src text_tgt th_tgt
      (TRANS: trans_prog_thread text_src text_tgt)
      (TGT: Program.load_thread text_tgt th_tgt):
  exists th_src,
    <<SRC: Program.load_thread text_src th_src>> /\
    <<SIM: sim_thread None th_src th_tgt>>.
Proof.
  inv TRANS; inv TGT.
  apply inj_pair2 in H1. subst.
  inv LOAD. exists (Thread.mk lang (State.mk RegFile.init s1)).
  split; repeat constructor; auto.
Qed.

Lemma sim_load
      prog_src prog_tgt
      (TRANS: trans_prog prog_src prog_tgt):
  Simulation.LOAD prog_src prog_tgt sim_configuration.
Proof.
  inv TRANS.
  ii. inv TGT. inv LOAD.
  generalize (IdentMap.rel2_elim TRANS0 LOAD0). intro REL2.
  eapply (IdentMap.rel2_implies
            (fun text th => exists th', Program.load_thread text th' /\
                                sim_thread None th' th))
    in REL2.
  all: cycle 1.
  { intros. des. inv H. inv H0. inv LOAD.
    apply inj_pair2 in H2. subst.
    repeat econs; eauto.
  }

  apply IdentMap.rel2_intro in REL2. des.
  eexists (Configuration.mk Clocks.init mb _ []).
  repeat econs; simpl; eauto.
  intro i. rewrite ? IdentMap.Facts.map_o.
  specialize (BC i). inv BC; simpl; try constructor.
  repeat econs; eauto.
Qed.

Lemma sim_step: Simulation.STEP sim_configuration.
Proof.
  ii. inv STEP.
  - admit.
  - destruct src. inv SIM. simpl in *.
    eexists. split.
    + eapply srcsteps_progress.
      { apply tausteps_nil. }
      apply Configuration.step_dream.
    + econs; simpl; auto.
  - admit.
  - destruct src. inv SIM. inv STACK. simpl in *. subst.
    eexists. split.
    + eapply srcsteps_progress.
      { apply tausteps_nil. }
      apply Configuration.step_commit.
      * admit.
      * admit.
    + econs; simpl; eauto.
  - destruct src. inv SIM. inv STACK. simpl in *. subst.
    eexists. split.
    + eapply srcsteps_progress.
      { apply tausteps_nil. }
      eapply Configuration.step_syscall.
      admit.
    + econs; simpl; eauto.
      admit.
Admitted.

Lemma sim_observable: Simulation.OBSERVABLE sim_configuration.
Proof.
  (* TODO: bogus step for *each* thread *)
Admitted.

Lemma sim_terminal: Simulation.TERMINAL sim_configuration.
Proof.
  ii. destruct src, tgt. inv SIM. inv TERM.
  simpl in *. subst. inv STACK.
  eexists. split.
  { apply tausteps_nil. }
  econs; simpl; eauto.
  econs. ii. specialize (CUR i). inv CUR; try congruence.
  rewrite THREAD in H0. inv H0.
  inv THREADS. symmetry in H. specialize (TERMINAL _ _ H).
  inv THREAD0.
  - inv TERMINAL. simpl in *. subst.
    inv TRANS. econs.
  - inv TERMINAL. simpl in *. subst.
    inv CONSUMED.
Qed.

Definition sim
           prog_src prog_tgt
           (TRANS: trans_prog prog_src prog_tgt):
  Simulation.t prog_src prog_tgt :=
  Simulation.mk
    (sim_load TRANS)
    sim_step
    sim_observable
    sim_terminal.
