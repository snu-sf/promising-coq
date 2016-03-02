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

Inductive reordered_instr: forall (i1 i2:Instr.t), Prop :=
| reordered_instr_load_store
    r1 l1 o1
    l2 v2 o2
    (LOC: l1 <> l2)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1)) (Instr.regs_of (Instr.store l2 v2 o2)))
    (ORDERING1: ~ Ordering.ord Ordering.acquire o1)
    (ORDERING1: ~ Ordering.ord Ordering.release o2):
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

Inductive sim_thread: forall (th1 th2:Thread.t), Prop :=
| sim_thread_intro
    rs s1 s2
    (REORDER: reordered_stmts s1 s2):
    sim_thread
      (Thread.mk lang (State.mk rs s1))
      (Thread.mk lang (State.mk rs s2))
.

(* TODO: refactoring *)
Lemma sim_thread_inv
      th1 th2 (SIM: sim_thread th1 th2):
  exists rs s1 s2,
    th1 = Thread.mk lang (State.mk rs s1) /\
    th2 = Thread.mk lang (State.mk rs s2) /\
    reordered_stmts s1 s2.
Proof.
  inv SIM. eexists _, _, _. splits; eauto.
Qed.

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

(* TODO: refactoring *)
Lemma sim_consumed_thread_inv
      e th1 th2 (SIM: sim_consumed_thread e th1 th2):
  exists rs1 rs2 s1 s2 i,
    th1 = Thread.mk lang (State.mk rs1 s1) /\
    th2 = Thread.mk lang (State.mk rs2 s2) /\
    consumed_stmts i s1 s2 /\
    RegFile.eval_instr rs1 i (option_map (ThreadEvent.mem <*> ThreadEvent.rw) e) rs2.
Proof.
  inv SIM. eexists _, _, _, _, _. splits; eauto.
Qed.

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

Inductive sim_context i:
  forall (c1 c2:Clock.t)
    (th1 th2:Thread.t)
    (b1 b2:Buffer.t)
    (inceptions1 inceptions2:InceptionSet.t), Prop :=
| sim_context_reordered
    c1 c2 th1 th2 b1 b2 inceptions1 inceptions2
    (CLOCK: c1 = c2)
    (THREAD: sim_thread th1 th2)
    (BUFFER: sim_buffer b1 b2)
    (INCEPTIONS: inceptions1 = inceptions2):
    sim_context i c1 c2 th1 th2 b1 b2 inceptions1 inceptions2
| sim_context_consumed
    c1 c2 th1 th2 b1 b2 inceptions1 inceptions2
    e
    (CLOCK: Clock.le c1 c2)
    (THREAD2: sim_consumed_thread (option_map fst e) th1 th2)
    (BUFFER2: sim_consumed_buffer e b1 b2)
    (INCEPTIONS: sim_inceptions i e inceptions1 inceptions2):
    sim_context i c1 c2 th1 th2 b1 b2 inceptions1 inceptions2
.

Inductive sim_configuration i: forall (conf1 conf2:Configuration.t), Prop :=
| sim_configuration_intro
    c1 c2 th1 th2 b1 b2 inceptions1 inceptions2
    p1 p2 bs1 bs2
    (PROGRAM1: IdentMap.find i p1 = Some th1)
    (BUFFER1: IdentFun.find i bs1 = b1)
    (PROGRAM2: p2 = IdentMap.add i th2 p1)
    (BUFFER2: bs2 = IdentFun.add i b2 bs1)
    (CONTEXT: sim_context i c1 c2 th1 th2 b1 b2 inceptions1 inceptions2):
    sim_configuration
      i
      (Configuration.mk c1 p1 (Memory.mk bs1 inceptions1))
      (Configuration.mk c2 p2 (Memory.mk bs2 inceptions2))
.

Lemma sim_init
      i prog_src prog_tgt
      (REORDER: reordered_program i prog_src prog_tgt):
  Simulation.INIT prog_src prog_tgt (sim_configuration i).
Proof.
  inv REORDER. repeat econs.
  - unfold Program.init.
    rewrite IdentMap.Facts.map_o, TH1.
    simpl. eauto.
  - apply IdentMap.map_add.
  - rewrite IdentFun.add_init. auto.
  - inv REORDER0. econs. eauto.
Qed.

Lemma sim_feasible i: Simulation.FEASIBLE (sim_configuration i).
Proof.
  ii. inversion SIM. subst. simpl in *.
  inv CONTEXT.
  { repeat econs. auto. }
  inv INCEPTIONS.
  { repeat econs. auto. }
  simpl in *. inv THREAD2. inv BUFFER2. inv CONSUMED. simpl in *.
  econs; [econs 2; [|econs 2; [|econs 1]]|].
  - admit. (* we can execute i1 *)
  - admit. (* we can execute i0 *)
  - admit. (* the execution of i0 removes the only inception *)
Admitted.

Lemma sim_Memory_message c1 c2 m1 m2 i e msg
      (CLOCK: Clock.le c1 c2)
      (MESSAGE: Memory.message c2 m2 i e msg):
  Memory.message c1 m1 i e msg.
Proof.
  inv MESSAGE.
  - econs.
    admit.
  - econs.
    admit.
  - econs.
    admit.
    admit.
  - econs.
Admitted.

Lemma sim_base i: Simulation.BASE_STEP (sim_configuration i).
Proof.
  ii. inv SIM. inv STEP.
  destruct (Ident.eq_dec i i0).
  - subst i0. inv PROGRAM.
    rewrite IdentMap.Facts.add_eq_o in *; auto.
    inv THREAD. inv STEP. inv CONTEXT.
    + apply sim_thread_inv in THREAD. des. subst.
      inv THREAD0. apply inj_pair2 in H1. subst.
      admit. (* program step, sim *)
    + apply sim_consumed_thread_inv in THREAD2. des. subst.
      inv THREAD0. apply inj_pair2 in H1. subst.
      inv THREAD1.
      admit. (* reordered instr should emit mem events: REORDER & STEP0 *)
  - inv PROGRAM. rewrite IdentMap.Facts.add_neq_o in *; auto.
    inv MEMORY.
    + eexists _, _. splits.
      * econs 1.
      * econs 1. repeat (econs; eauto).
      * econs; eauto.
        { rewrite IdentMap.Facts.add_neq_o; auto. }
        { apply IdentMap.add_add. auto. }
    + inv ADD. rewrite IdentFun.add_spec_neq in *; auto.
      eexists _, _. splits; eauto.
      * econs 1.
      * econs 1. econs.
        { repeat (econs; eauto). }
        econs.
        { 

admit. (* Memory.message *) }
        { unfold Memory.add_message. simpl in *. eauto. }
        { simpl in *.
          admit.
        }
        { admit. }
      * econs; eauto.
        { rewrite IdentMap.Facts.add_neq_o; eauto. }
        { apply IdentMap.add_add. auto. }
        { apply IdentFun.add_add. auto. }
        admit. (* sim_context *)
Admitted.

Lemma sim_inception i: Simulation.INCEPTION_STEP (sim_configuration i).
Proof.
Admitted.

Lemma sim_external i: Simulation.EXTERNAL_STEP (sim_configuration i).
Proof.
  ii. inv SIM. inv STEP.
  - eexists _, _. splits.
    + econs 1.
    + econs 1. inv CONTEXT; eauto.
      admit. (* Clock.le transitive *)
    + econs; eauto.
      inv CONTEXT; [econs 1|econs 2]; eauto.
      admit. (* Clock.le reflexive *)
  - inv PROGRAM. inv STEP. simpl in *.
    rewrite IdentMap.Facts.add_o in *. destruct (IdentMap.Facts.eq_dec i i0).
    + subst. 
      admit. (* the reordered thread syscalled *)
    + eexists _, _. splits.
      * econs 1.
      * econs 2; simpl in *.
        { econs; eauto. econs. eauto. }
        { admit. (* inceptions *) }
      * econs; eauto.
        { rewrite IdentMap.Facts.add_neq_o; auto. }
        { apply IdentMap.add_add. auto. }
Admitted.

Lemma sim_terminal i: Simulation.TERMINAL (sim_configuration i).
Proof.
  ii. eexists. split.
  { apply Configuration.steps_nil. }
  econs. econs. i.
  inv TERM. inv PROGRAM. specialize (TERMINAL i0).
  inv SIM. simpl in *.
  rewrite IdentMap.Facts.add_o in *.
  destruct (IdentMap.Facts.eq_dec i i0); auto.
  subst. exploit TERMINAL; eauto. intro X.
  rewrite PROGRAM1 in THREAD. inv THREAD.
  inv CONTEXT.
  - inv THREAD. inv X. simpl in *. subst. inv REORDER. auto.
  - inv THREAD2. inv X. simpl in *. subst. inv CONSUMED.
Qed.

Definition sim
           i prog_src prog_tgt
           (REORDER: reordered_program i prog_src prog_tgt):
  Simulation.t prog_src prog_tgt :=
  Simulation.mk
    _ _
    (sim_init REORDER)
    (Simulation.step_lemma
       (@sim_feasible _)
       (@sim_base _)
       (@sim_inception _)
       (@sim_external _))
    (@sim_terminal _).
