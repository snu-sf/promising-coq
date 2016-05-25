Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

(* NOTE: it is also possible to eliminate unused relaxed load, but the
   proof requires additional invariant on the commits.  Currently we
   do not pursue that direction.
 *)
Lemma unused_load_sim_stmts
      r loc ord
      (ORD: Ordering.le ord Ordering.unordered):
  sim_stmts (RegFile.eq_except (RegSet.singleton r))
            [Stmt.instr (Instr.load r loc ord)]
            []
            (RegFile.eq_except (RegSet.singleton r)).
Proof.
  ii. pfold. ii. splits.
  - admit.
  - admit.
  - admit.
  - ii. inv STEP_TGT; try by inv STEP; inv STATE.
    admit.
Admitted.
