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

(* NOTE: Elimination of a unused relaxed load is unsound under the
 * semantics with liveness.  Consider the following example:

    while (!y_unordered) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the semantics with liveness, the loop *should* break, as once
 * `x_rlx` will read `x =rel 1` and the acquire fence guarantees that
 * `y_unordered` will read 1.  However, the elimination of `x_rlx`
 * will allow the loop to run forever.
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
