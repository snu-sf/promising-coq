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
 * liveness-aware semantics.  Consider the following example:

    while (!y_unordered) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the liveness-aware semantics, the loop *should* break, as
 * once `x_rlx` will read `x =rel 1` and the acquire fence guarantees
 * that `y_unordered` will read 1.  However, the elimination of
 * `x_rlx` will allow the loop to run forever.
 *)

Lemma unused_read
      lc0 mem0
      loc ord
      (ORD: Ordering.le ord Ordering.unordered)
      (WF: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0):
  exists ts val released,
    Local.read_step lc0 mem0 loc ts val released ord lc0.
Proof.
  destruct lc0.
  assert (exists from val released, Memory.get loc (Capability.ur (Commit.cur commit) loc) mem0 = Some (from, Message.mk val released)).
  { inv WF. ss. inv COMMIT_CLOSED; eauto. inv CUR.
    exploit UR; eauto. i. des; eauto.
    

      by apply WF.
  i. des.
  inv MEM. exploit CLOSED; eauto. i. des.
  exploit (CommitFacts.read_min_spec loc); eauto.
  { refl. }
  { i. instantiate (1 := ord) in H0. destruct ord; inv ORD; inv H0. }
  { apply WF. }
  s. i. eexists _, _, _. refine (Local.step_read _ _ _ _ _ ); eauto. s.
  replace (CommitFacts.read_min
             loc
             (Capability.ur (Commit.cur commit) loc) released ord
             commit)
  with commit in x0; auto.
  destruct commit. unfold CommitFacts.read_min. ss. f_equal.
  - destruct (Ordering.le Ordering.acqrel ord) eqn:X; s.
    { destruct ord; inv ORD; inv X. }
    rewrite Capability.incr_rw_nop; auto; apply WF.
  - destruct (Ordering.le Ordering.relaxed ord) eqn:X; s.
    { destruct ord; inv ORD; inv X. }
    rewrite Capability.incr_rw_nop; auto; try apply WF. etrans; apply WF.
  - apply WF.
Qed.

Lemma unused_load_sim_stmts
      r loc ord
      (ORD: Ordering.le ord Ordering.unordered):
  sim_stmts (RegFile.eq_except (RegSet.singleton r))
            [Stmt.instr (Instr.load r loc ord)]
            [Stmt.instr Instr.skip]
            (RegFile.eq_except (RegSet.singleton r)).
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. esplits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* silent *)
    exploit unused_read; try apply WF_SRC; eauto. i. des.
    esplits; eauto.
    + econs 2. econs 2; eauto. econs. econs.
    + auto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      * etrans; eauto. apply RegFile.eq_except_singleton.
      * inv LOCAL. inv LOCAL0. econs; ss. etrans; eauto.
Qed.
