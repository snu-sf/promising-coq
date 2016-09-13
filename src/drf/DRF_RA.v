Require Import Omega.
Require Import RelationClasses.
Require Import Bool.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import MemoryRel.
Require Import OrdStep.

Set Implicit Arguments.


Inductive sim_thread: forall (th_src th_tgt:{lang:Language.t & lang.(Language.state)} * Local.t), Prop :=
| sim_thread_intro
    st rel_src rel_tgt cur acq:
    sim_thread
      (st, Local.mk (TView.mk rel_src cur acq) Memory.bot)
      (st, Local.mk (TView.mk rel_tgt cur acq) Memory.bot)
.

(* Inductive sim_thread (th_src th_tgt:{lang:Language.t & lang.(Language.state)} * Local.t): Prop := *)
(* | sim_thread_intro *)
(*     (STATE: th_src.(fst) = th_tgt.(fst)) *)
(*     (CUR: th_src.(snd).(Local.tview).(TView.cur) = th_tgt.(snd).(Local.tview).(TView.cur)) *)
(*     (ACQ: th_src.(snd).(Local.tview).(TView.acq) = th_tgt.(snd).(Local.tview).(TView.acq)) *)
(*     (PROMISE_SRC: th_src.(snd).(Local.promises) = Memory.bot) *)
(*     (PROMISE_TGT: th_tgt.(snd).(Local.promises) = Memory.bot) *)
(* . *)

Inductive sim_conf (c_src c_tgt:Configuration.t): Prop :=
| sim_conf_intro
    (THREADS:
       forall tid th_tgt
         (TH_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some th_tgt),
       exists th_src,
         <<TH_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some th_src>> /\
         <<SIM: sim_thread th_src th_tgt>>)
    (SC: c_src.(Configuration.sc) = c_tgt.(Configuration.sc))
    (MEM: mem_eqlerel c_tgt.(Configuration.memory) c_src.(Configuration.memory))
.

Inductive sim_step (etid:ThreadEvent.program_t * Ident.t) (cs1 cs2:Configuration.t * Configuration.t): Prop :=
| sim_step_intro
    (SIM_CONF: sim_conf cs2.(fst) cs2.(snd))
    (STEP_SRC: ord_step Ordering.acqrel etid.(fst) etid.(snd) cs1.(fst) cs2.(fst))
    (STEP_TGT: ord_step Ordering.relaxed etid.(fst) etid.(snd) cs1.(snd) cs2.(snd))
.

(* TODO: add the condition for race-freedom *)
Inductive sim (c_src c_tgt:Configuration.t): Prop :=
| sim_intro
    s
    (STEPS: rtc (union sim_step)
                (Configuration.init s, Configuration.init s)
                (c_src, c_tgt))
.

Lemma init_sim_conf s: sim_conf (Configuration.init s) (Configuration.init s).
Proof.
  econs; ss.
  - i. esplits; eauto.
    unfold Threads.init in TH_TGT. rewrite IdentMap.Facts.map_o in TH_TGT.
    destruct (IdentMap.find tid s) eqn:FIND; inv TH_TGT. ss.
  - econs; ii; esplits; eauto.
    + refl.
    + refl.
Qed.

Lemma sim_sim_conf: sim <2= sim_conf.
Proof.
  s. i. inv PR. apply rtc_tail in STEPS. des.
  - inv STEPS0. inv USTEP. ss.
  - inv STEPS. apply init_sim_conf.
Qed.

Lemma sim_read_split
      c3_src c3_tgt
      e_read tid_read c4_tgt
      loc to val released ordr
      (SIM: sim c3_src c3_tgt)
      (STEP_TGT: ord_step Ordering.relaxed e_read tid_read c3_tgt c4_tgt)
      (READING: ThreadEvent.is_reading e_read = Some (loc, to, val, released, ordr)):
  <<BOT: to = Time.bot>> \/
  (exists s c1_src c1_tgt c2_src c2_tgt e_write tid_write from ordw,
      <<STEPS01: rtc (union sim_step)
                     (Configuration.init s, Configuration.init s)
                     (c1_src, c1_tgt)>> /\
      <<STEP12: sim_step (e_write, tid_write) (c1_src, c1_tgt) (c2_src, c2_tgt)>> /\
      <<STEPS23: rtc (union sim_step)
                     (c2_src, c2_tgt)
                     (c3_src, c3_tgt)>> /\
      <<WRITING: ThreadEvent.is_writing e_write = Some (loc, from, to, val, released, ordw)>>).
Proof.
Admitted.

Lemma sim_progress
      c3_src c3_tgt
      e tid c4_tgt
      (SIM: sim c3_src c3_tgt)
      (STEP_TGT: ord_step Ordering.relaxed e tid c3_tgt c4_tgt):
  exists c4_src,
    <<STEP_SRC: ord_step Ordering.acqrel e tid c3_src c4_src>> /\
    <<SIM: sim c3_src c4_tgt>>.
Proof.
  exploit sim_sim_conf; eauto. intro SIM_CONF.
  destruct (ThreadEvent.is_reading e) eqn:READING; cycle 1.
  { (* not reading *)
    inv SIM_CONF. destruct c3_src, c3_tgt; ss. subst.
    inv STEP_TGT. ss. exploit THREADS; eauto. i. des. inv SIM0.
    admit.
  }
  (* reading *)
  rename e into e_read, tid into tid_read.
  destruct p as [[[[loc to] val] released] ordr].
  exploit sim_read_split; eauto. i. des.
  { (* reading from bot *)
    subst.
    exploit sim_sim_conf; eauto. i. inv x0.
    inversion STEP_TGT. subst. ss. exploit THREADS; eauto. i. des. inv SIM0.
    admit.
  }
  destruct (classic (<<ORDR: Ordering.le Ordering.acqrel ordr>> /\
                     <<ORDW: Ordering.le Ordering.acqrel ordw>>)).
  { (* acqrel <= ordr, ordw *)
    des.
    admit.
  }
  exploit ord_step_threads2.
  { inv STEP12. apply STEP_SRC. }
  s. i. des. rename th2 into th2_src, x0 into TH2_SRC.
  exploit ord_step_threads1; try exact STEP_TGT; eauto. i. des.
  inv SIM_CONF. exploit THREADS; eauto. i. des.
  rename th_src into th3_src, TH_SRC into TH3_SRC.
  destruct (classic (<<VIEW: View.le (th2_src.(snd).(Local.tview).(TView.cur))
                                     (th3_src.(snd).(Local.tview).(TView.cur))>>)).
  { (* ik's cur <= in's cur *)
    des.
    admit.
  }
  (* constructing a race *)
  admit.
Admitted.
