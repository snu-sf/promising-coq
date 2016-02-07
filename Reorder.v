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

Inductive reordered_list: forall (is1 is2:list Instr.t), Prop :=
| reordered_nil:
    reordered_list nil nil
| reordered_cons
    i is1 is2
    (REORDER: reordered_list is1 is2):
    reordered_list (i::is1) (i::is2)
| reordered_reorder
    i1 i2 is1 is2
    (REORDER1: reorderable i1 i2)
    (REORDER2: reordered_list is1 is2):
    reordered_list (i1::i2::is1) (i2::i1::is2)
.

Inductive reordered: forall (c1 c2:Core.t), Prop :=
| reordered_instrs
    is1 is2
    (REORDER: reordered_list is1 is2):
    reordered (Core.instrs is1) (Core.instrs is2)
| reordered_seq
    i11 i12 i21 i22
    (REORDER1: reordered i11 i21)
    (REORDER2: reordered i12 i22):
    reordered
      (Core.seq i11 i12)
      (Core.seq i21 i22)
| reordered_ite
    cond i11 i12 i21 i22
    (REORDER1: reordered i11 i21)
    (REORDER2: reordered i12 i22):
    reordered
      (Core.ite cond i11 i12)
      (Core.ite cond i21 i22)
| reordered_while
    cond i1 i2
    (REORDER: reordered i1 i2):
    reordered
      (Core.while cond i1)
      (Core.while cond i2)
.

Inductive consumed (i2:Instr.t): forall (c1 c2:Core.t), Prop :=
| consumed_instrs
    i1 is1 is2
    (REORDER1: reorderable i1 i2)
    (REORDER2: reordered_list is1 is2):
    consumed i2 (Core.instrs (i1::i2::is1)) (Core.instrs (i1::is2))
| consumed_seq
    c11 c12 c21 c22
    (CONSUMED: consumed i2 c11 c21)
    (REORDER: reordered c21 c22):
    consumed i2 (Core.seq c11 c12) (Core.seq c21 c22)
.
