From Stdlib Require Import Bool.
From Stdlib Require Import List.
From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import lang.Event.
From PromisingLib Require Import Language.
Require Import lang.Time.
Require Import lang.View.
Require Import lang.Cell.
Require Import lang.Memory.
Require Import lang.TView.
Require Import lang.Thread.
Require Import lang.Configuration.
Require Import lang.Progress.

Require Import opt.SimMemory.
Require Import opt.SimPromises.
Require Import opt.SimLocal.
Require Import opt.Compatibility.
Require Import opt.SimThread.

Require Import while.Syntax.
Require Import while.Semantics.

Set Implicit Arguments.


Lemma intro_load_sim_stmts
      r loc ord:
  sim_stmts (RegFile.eq_except (RegSet.singleton r))
            []
            [Stmt.instr (Instr.load r loc ord)]
            (RegFile.eq_except (RegSet.singleton r)).
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; try done.
  { i. exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { i. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    destruct e; inv H4.
    esplits; eauto.
    + econs 1.
    + ss.
    + sfby inv LOCAL0.
    + sfby inv LOCAL0.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      * etrans; [eauto|].
        symmetry. apply RegFile.eq_except_singleton.
      * inv LOCAL. inv LOCAL0. inv LOCAL. econs; ss.
        etrans; eauto. apply TViewFacts.read_tview_incr.
Qed.
