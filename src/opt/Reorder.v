Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* TODO: now supporting only the reordering of load and store *)
(* TODO: now supporting only the reordering of single thread *)

Inductive reorder: forall (i1 i2:Instr.t), Prop :=
| reorder_load_store
    r1 l1 o1
    l2 v2 o2
    (LOC: l1 <> l2)
    (DISJOINT: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1)) (Instr.regs_of (Instr.store l2 v2 o2)))
    (ORDERING1: ~ Ordering.le Ordering.acquire o1)
    (ORDERING1: ~ Ordering.le Ordering.release o2):
    reorder (Instr.load r1 l1 o1) (Instr.store l2 v2 o2)
.

Lemma reorder_sim_stmts
      (sim_regs:SIM_REGS)
      i1 i2
      (I1: forall reg (REG: RegSet.mem reg (Instr.regs_of i1))
             rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
          rs_src reg = rs_tgt reg)
      (I2: forall reg (REG: RegSet.mem reg (Instr.regs_of i2))
             rs_src rs_tgt (RS: sim_regs rs_src rs_tgt),
          rs_src reg = rs_tgt reg)
      (REORDER: reorder i1 i2):
  sim_stmts sim_regs
            [Stmt.instr i1; Stmt.instr i2]
            [Stmt.instr i2; Stmt.instr i1]
            sim_regs.
Proof.
Admitted.
