Require Import List.

Require Import sflib.

Require Import Basic.
Require Import Event.
Require Import Syntax.
Require Import Semantics.
Require Import Thread.
Require Import Memory.
Require Import Configuration.

Inductive reorderable: forall (i1 i2:Instr.t), Prop :=
| reorderable_intro
    i1 i2
    (I1NACQ: not (Ordering.le Ordering.acquire (Instr.ordering_of i1)))
    (I2NREL: not (Ordering.le Ordering.release (Instr.ordering_of i2)))
    (LOC: forall loc1 loc2
            (LOC1: Instr.loc_of i1 = Some loc1)
            (LOC2: Instr.loc_of i2 = Some loc2),
        loc1 <> loc2)
    (REG: Reg.Set_.Empty (Reg.Set_.inter (Instr.regs_of i1) (Instr.regs_of i2))):
    reorderable i1 i2
.

Inductive reordered_stmt: forall (s1 s2:Stmt.t), Prop :=
| reordered_instr i:
    reordered_stmt
      (Stmt.instr i)
      (Stmt.instr i)
| reordered_ite
    cond c11 c12 c21 c22
    (REORDER1: reordered_stmts c11 c21)
    (REORDER2: reordered_stmts c12 c22):
    reordered_stmt
      (Stmt.ite cond c11 c12)
      (Stmt.ite cond c21 c22)
| reordered_dowhile
    cond c1 c2
    (REORDER2: reordered_stmts c1 c2):
    reordered_stmt
      (Stmt.dowhile c1 cond)
      (Stmt.dowhile c2 cond)

with reordered_stmts: forall (s1 s2:list Stmt.t), Prop :=
| reordered_nil:
    reordered_stmts nil nil
| reordered_cons
    s11 s12 s21 s22
    (REORDER1: reordered_stmt s11 s21)
    (REORDER2: reordered_stmts s12 s22):
    reordered_stmts (s11::s12) (s21::s22)
| reordered_reorder
    i1 i2 s1 s2
    (REORDER1: reorderable i1 i2)
    (REORDER2: reordered_stmts s1 s2):
    reordered_stmts
      ((Stmt.instr i1)::(Stmt.instr i2)::s1)
      ((Stmt.instr i2)::(Stmt.instr i1)::s2)
.

Scheme reordered_stmt_ind_ := Induction for reordered_stmt Sort Prop
with reordered_stmts_ind_ := Induction for reordered_stmts Sort Prop.
Combined Scheme reordered_ind from reordered_stmt_ind_, reordered_stmts_ind_.

Inductive consumed (i2:Instr.t): forall (c1 c2:list Stmt.t), Prop :=
| consumed_intro
    i1 c1 c2
    (REORDER1: reorderable i1 i2)
    (REORDER2: reordered_stmts c1 c2):
    consumed i2 ((Stmt.instr i1)::(Stmt.instr i2)::c1) ((Stmt.instr i1)::c2)
.

Inductive sim_thread: forall (e:option ThreadEvent.t) (th1 th2:Thread.t), Prop :=
| sim_thread_reordered
    rs s1 s2
    (REORDERED: reordered_stmts s1 s2):
    sim_thread
      None
      (Thread.mk lang (State.mk rs s1))
      (Thread.mk lang (State.mk rs s2))
| sim_thread_consumed
    rs1 rs2 s1 s2 i e
    (CONSUMED: consumed i s1 s2)
    (EVAL: RegSet.eval_instr rs1 i e rs2):
    sim_thread
      e
      (Thread.mk lang (State.mk rs1 s1))
      (Thread.mk lang (State.mk rs2 s2))
.

Inductive sim_buffer: forall (e:option ThreadEvent.t) (b1 b2:Buffer.t), Prop :=
| sim_buffer_reordered
    history inception1 inception2
    (INCEPTION: MessageSet.Equal inception1 inception2):
    sim_buffer
      None
      (Buffer.mk history inception1)
      (Buffer.mk history inception2)
| sim_buffer_consumed_observable
    msg history1 inception1 inception2
    (OBSERVABLE: Message.observable msg = true)
    (INCEPTION: MessageSet.disjoint_add inception2 msg inception1):
    sim_buffer
      (Some (Message.get_threadevent msg))
      (Buffer.mk history1 inception1)
      (Buffer.mk (history1 ++ [msg]) inception2)
| sim_buffer_consumed_unobservable
    msg history1 inception1 inception2
    (UNOBSERVABLE: Message.observable msg = false)
    (INCEPTION: MessageSet.Equal inception1 inception2):
    sim_buffer
      (Some (Message.get_threadevent msg))
      (Buffer.mk history1 inception1)
      (Buffer.mk (history1 ++ [msg]) inception2)
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
             (Ident.Map.find i th1) (Ident.Map.find i th2)
             (Ident.Map.find i m1) (Ident.Map.find i m2)>>.

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
