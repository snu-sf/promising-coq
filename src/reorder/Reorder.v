Require Import Basics.
Require Import Bool.
Require Import List.
Require Import ProofIrrelevance.

Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Program.
Require Import Memory.
Require Import Configuration.
Require Import Simulation.
Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)

Definition reordered_instr (i1 i2:Instr.t): bool :=
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

Inductive reordered_program i: forall (prog1 prog2:Program.syntax), Prop :=
| reordered_program_intro
    prog1 th1 th2
    (TH1: IdentMap.find i prog1 = Some th1)
    (REORDER: reordered_thread th1 th2):
    reordered_program i prog1 (IdentMap.add i th2 prog1)
.

Inductive consumed_stmts (i2:Instr.t): forall (c1 c2:list Stmt.t), Prop :=
| consumed_stmts_intro
    i1 c1 c2
    (REORDER: reordered_instr i1 i2)
    (REORDER: reordered_stmts c1 c2):
    consumed_stmts i2 ((Stmt.instr i1)::(Stmt.instr i2)::c1) ((Stmt.instr i1)::c2)
.

Inductive consumed_thread i: forall (text1 text2:Thread.syntax), Prop :=
| consumed_thread_intro
    s1 s2
    (CONSUME: consumed_stmts i s1 s2):
    consumed_thread
      i
      (Thread.mk_syntax lang s1)
      (Thread.mk_syntax lang s2)
.

Inductive sim_thread: forall (th1 th2:Thread.t), Prop :=
| sim_thread_intro
    rs s1 s2
    (REORDER: reordered_stmts s1 s2):
    sim_thread
      (Thread.mk lang (State.mk rs s1))
      (Thread.mk lang (State.mk rs s2))
.

Inductive sim_consumed_thread (e:option RWEvent.t): forall (th1 th2:Thread.t), Prop :=
| sim_consumed_thread_intro
    rs1 rs2 s1 s2 i
    (CONSUMED: consumed_stmts i s1 s2)
    (EVAL: RegFile.eval_instr rs1 i (option_map (ThreadEvent.mem <*> ThreadEvent.rw) e) rs2):
    sim_consumed_thread
      e
      (Thread.mk lang (State.mk rs1 s1))
      (Thread.mk lang (State.mk rs2 s2))
.

Definition sim_message (msg1 msg2:Message.t): bool :=
  match msg1, msg2 with
  | Message.rw (RWEvent.read l1 c1 o1) t1,
    Message.rw (RWEvent.write l2 c2 o2) t2 =>
    (negb (Loc.eqb l1 l2)) &&
    (negb (Ordering.ord Ordering.acquire o1)) &&
    (negb (Ordering.ord Ordering.release o2))
  | _, _ =>
    false
  end.

Inductive sim_buffer: forall (b1 b2:Buffer.t), Prop :=
| sim_buffer_nil:
    sim_buffer nil nil
| sim_buffer_cons
    msg b1 b2
    (BUFFER: sim_buffer b1 b2):
    sim_buffer (b1 ++ [msg]) (b2 ++ [msg])
| sim_buffer_reorder
    msg1 msg2 b1 b2
    (MSG: sim_message msg1 msg2)
    (BUFFER: sim_buffer b1 b2):
    sim_buffer (b1 ++ [msg1; msg2]) (b2 ++ [msg2; msg1])
.

Inductive sim_consumed_buffer: forall (e:option (RWEvent.t * nat)) (b1 b2:Buffer.t), Prop :=
| sim_consumed_buffer_None
    b1 b2
    (BUFFER: sim_buffer b1 b2):
    sim_consumed_buffer None b1 b2
| sim_consumed_buffer_Some
    e ts b1 b2
    (BUFFER: sim_buffer b1 b2):
    sim_consumed_buffer (Some (e, ts)) b1 (b2 ++ [Message.rw e ts])
.

Inductive sim_inceptions i: forall (e:option (RWEvent.t * nat)) (inceptions1 inceptions2:InceptionSet.t), Prop :=
| sim_inceptions_None inceptions:
    sim_inceptions i None inceptions inceptions
| sim_inceptions_Some
    e ts inceptions2:
    sim_inceptions
      i (Some (e, ts))
      (InceptionSet.add (Inception.mk (Message.rw e ts) (IdentSet.singleton i)) inceptions2)
      inceptions2
.

Inductive sim_configuration: forall (conf1 conf2:Configuration.t), Prop :=
| sim_configuration_reordered
    i c1 c2 p1 p2 bs1 bs2 inceptions1 inceptions2
    th1 th2 b1 b2
    (THREAD1: IdentMap.find i p1 = Some th1)
    (BUFFER1: IdentMap.find i bs1 = Some b1)
    (THREAD2: sim_thread th1 th2)
    (BUFFER2: sim_buffer b1 b2)
    (CLOCK: c1 = c2)
    (PROGRAMS: p2 = IdentMap.add i th2 p1)
    (BUFFERS: bs2 = IdentMap.add i b2 bs1)
    (INCEPTIONS: inceptions1 = inceptions2):
    sim_configuration
      (Configuration.mk c1 p1 (Memory.mk bs1 inceptions1))
      (Configuration.mk c2 p2 (Memory.mk bs2 inceptions2))
| sim_configuration_consumed
    i e c1 c2 p1 p2 bs1 bs2 inceptions1 inceptions2
    th1 th2 b1 b2
    (CLOCK: Clock.le c1 c2)
    (THREAD1: IdentMap.find i p1 = Some th1)
    (BUFFER1: IdentMap.find i bs1 = Some b1)
    (THREAD2: sim_consumed_thread (option_map fst e) th1 th2)
    (BUFFER2: sim_consumed_buffer e b1 b2)
    (PROGRAMS: p2 = IdentMap.add i th2 p1)
    (BUFFERS: bs2 = IdentMap.add i b2 bs1)
    (INCEPTIONS: sim_inceptions i e inceptions1 inceptions2):
    sim_configuration
      (Configuration.mk c1 p1 (Memory.mk bs1 inceptions1))
      (Configuration.mk c2 p1 (Memory.mk bs2 inceptions2))
.

Lemma sim_load
      i prog_src prog_tgt
      (REORDER: reordered_program i prog_src prog_tgt):
  Simulation.LOAD prog_src prog_tgt sim_configuration.
Proof.
  inv REORDER. econs 1; eauto.
  - unfold Program.load.
    rewrite IdentMap.Facts.map_o, TH1.
    simpl. eauto.
  - rewrite IdentMap.Facts.map_o, TH1.
    simpl. eauto.
  - instantiate (1 := Thread.load th2).
    inv REORDER0. econs. auto.
  - econs.
  - apply IdentMap.map_add.
  - apply IdentMap.map_add.
Qed.

Lemma sim_feasible: Simulation.FEASIBLE sim_configuration.
Proof.
Admitted.

Lemma sim_base: Simulation.BASE_STEP sim_configuration.
Proof.
Admitted.

Lemma sim_inception: Simulation.INCEPTION_STEP sim_configuration.
Proof.
Admitted.

Lemma sim_syscall: Simulation.SYSCALL_STEP sim_configuration.
Proof.
Admitted.

Lemma sim_terminal: Simulation.TERMINAL sim_configuration.
Proof.
  ii. eexists. split.
  { apply Configuration.steps_nil. }
  econs. econs. intros.
  inv TERM. inv PROGRAM. specialize (TERMINAL i).
  inv SIM; simpl in *.
  - rewrite IdentMap.Facts.add_o in *.
    destruct (IdentMap.Properties.F.eq_dec i0 i).
    + exploit TERMINAL; eauto. intro X.
      inv THREAD2. inv X. simpl in *. subst.
      inv REORDER. rewrite THREAD in THREAD1. inv THREAD1. auto.
    + apply TERMINAL. auto.
  - apply TERMINAL. auto.
Qed.

Definition sim
           i prog_src prog_tgt
           (REORDER: reordered_program i prog_src prog_tgt):
  Simulation.t prog_src prog_tgt :=
  Simulation.mk
    _ _
    (sim_load REORDER)
    (Simulation.step_lemma sim_feasible sim_base sim_inception sim_syscall)
    sim_terminal.
