Require Import List.

Require Import Basic.
Require Import Event.
Require Import Syntax.

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

Scheme reordered_stmt_ind' := Induction for reordered_stmt Sort Prop
with reordered_stmts_ind' := Induction for reordered_stmts Sort Prop.
Combined Scheme reordered_ind from reordered_stmt_ind', reordered_stmts_ind'.

Inductive consumed (i2:Instr.t): forall (c1 c2:list Stmt.t), Prop :=
| consumed_intro
    i1 c1 c2
    (REORDER1: reorderable i1 i2)
    (REORDER2: reordered_stmts c1 c2):
    consumed i2 ((Stmt.instr i1)::(Stmt.instr i2)::c1) ((Stmt.instr i1)::c2)
.
