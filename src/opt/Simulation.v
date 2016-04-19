Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (SPLITS: Memory.splits mem_tgt mem_src)
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation. ii. econs. reflexivity. Qed.
Next Obligation. ii. inv H. inv H0. econs. etransitivity; eauto. Qed.


Section SimulationThread.
  Variable (lang_src lang_tgt:Language.t).

  Definition SIM_THREAD :=
    forall (sim_terminal: forall (th_src:Thread.t lang_src) (th_tgt:Thread.t lang_tgt), Prop)
      (th1_src:Thread.t lang_src) (mem_k_src:Memory.t)
      (th1_tgt:Thread.t lang_tgt) (mem_k_tgt:Memory.t), Prop.

  (* TODO: inftau & liveness *)
  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: forall (th_src:Thread.t lang_src) (th_tgt:Thread.t lang_tgt), Prop)
             (th1_src:Thread.t lang_src) (mem_k_src:Memory.t)
             (th1_tgt:Thread.t lang_tgt) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (LE_SRC: Memory.le th1_src.(Thread.local) mem1_src)
      (LE_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) th1_tgt.(Thread.state)),
        exists th2_src mem2_src,
          <<STEPS: rtc (@Thread.internal_step lang_src) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: lang_src.(Language.is_terminal) th2_src.(Thread.state)>> /\
          <<LOCAL: th2_src.(Thread.local) = th1_tgt.(Thread.local)>> /\
          <<SIM: sim_terminal th2_src th1_tgt>>>> /\
      <<FUTURE:
        forall mem2_src
          (LE_SRC: Memory.le th1_src.(Thread.local) mem2_src)
          (FUTURE_SRC: Memory.future mem1_src mem2_src),
        exists mem2_tgt,
          <<MEMORY: sim_memory mem2_src mem2_tgt>> /\
          <<LE_TGT: Memory.le th1_tgt.(Thread.local) mem2_tgt>> /\
          <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>>>> /\
      <<LOCAL:
        forall (LOCAL_TGT: th1_tgt.(Thread.local) = Memory.bot),
        exists th2_src mem2_src,
          <<STEPS: rtc (@Thread.internal_step lang_src) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<LOCAL_SRC: th2_src.(Thread.local) = Memory.bot>>>> /\
      <<STEP:
        forall e th3_tgt mem3_tgt
          (STEP_TGT: Thread.step e th1_tgt mem1_tgt th3_tgt mem3_tgt),
        exists th2_src mem2_src th3_src mem3_src,
          <<STEPS: rtc (@Thread.internal_step lang_src) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
          <<STEP_SRC: Thread.step e th2_src mem2_src th3_src mem3_src>> /\
          <<MEMORY2: sim_memory mem3_src mem3_tgt>> /\
          <<SIM: sim_thread sim_terminal th3_src mem3_src th3_tgt mem3_tgt>>>>.

  Lemma _sim_thread_mon: monotone5 _sim_thread.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco5 _sim_thread bot5.

  Lemma sim_thread_mon
        sim_terminal1 sim_terminal2
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <4= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des.
      eexists _, _. splits; eauto.
    - i. exploit STEP; eauto. i. des; [|done].
      eexists _, _, _, _. splits; eauto.
  Qed.
End SimulationThread.
Hint Resolve _sim_thread_mon: paco.


Section Simulation.
  Definition SIM :=
    forall (th1_src:Threads.t) (mem_k_src:Memory.t)
      (th1_tgt:Threads.t) (mem_k_tgt:Memory.t), Prop.

  (* TODO: inftau & liveness *)
  Definition _sim
             (sim: SIM)
             (ths1_src:Threads.t) (mem_k_src:Memory.t)
             (ths1_tgt:Threads.t) (mem_k_tgt:Memory.t): Prop :=
    forall mem1_src mem1_tgt
      (MEMORY1: sim_memory mem1_src mem1_tgt)
      (CONSISTENT_SRC: Configuration.consistent (Configuration.mk ths1_src mem1_src))
      (CONSISTENT_TGT: Configuration.consistent (Configuration.mk ths1_tgt mem1_tgt))
      (FUTURE_SRC: Memory.future mem_k_src mem1_src)
      (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
        exists ths2_src mem2_src,
          <<STEPS: rtc (Configuration.step None) (Configuration.mk ths1_src mem1_src) (Configuration.mk ths2_src mem2_src)>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: Threads.is_terminal ths2_src>>>> /\
      <<STEP:
        forall e ths3_tgt mem3_tgt
          (STEP_TGT: Configuration.step e (Configuration.mk ths1_tgt mem1_tgt) (Configuration.mk ths3_tgt mem3_tgt)),
        exists ths2_src mem2_src ths3_src mem3_src,
          <<STEPS: rtc (Configuration.step None) (Configuration.mk ths1_src mem1_src) (Configuration.mk ths2_src mem2_src)>> /\
          <<STEP_SRC: Configuration.step e (Configuration.mk ths2_src mem2_src) (Configuration.mk ths3_src mem3_src)>> /\
          <<MEMORY2: sim_memory mem3_src mem3_tgt>> /\
          <<SIM: sim ths3_src mem3_src ths3_tgt mem3_tgt>>>>.

  Lemma _sim_mon: monotone4 _sim.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco4 _sim bot4.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      th_src mem_k1_src mem_k2_src
      th_tgt mem_k1_tgt mem_k2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal th_src mem_k1_src th_tgt mem_k1_tgt)
      (FUTURE_SRC: Memory.future mem_k1_src mem_k2_src)
      (FUTURE_TGT: Memory.future mem_k1_tgt mem_k2_tgt):
  sim_thread sim_terminal th_src mem_k2_src th_tgt mem_k2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.


Lemma sim_future
      ths_src mem_k1_src mem_k2_src
      ths_tgt mem_k1_tgt mem_k2_tgt
      (SIM: sim ths_src mem_k1_src ths_tgt mem_k1_tgt)
      (FUTURE_SRC: Memory.future mem_k1_src mem_k2_src)
      (FUTURE_TGT: Memory.future mem_k1_tgt mem_k2_tgt):
  sim ths_src mem_k2_src ths_tgt mem_k2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.


Lemma singleton_find
      tid lang (th:Thread.t lang):
  IdentMap.find tid (Threads.singleton tid th) = Some (existT _ lang th).
Proof.
  unfold Threads.singleton.
  rewrite IdentMap.Facts.add_eq_o; auto.
Qed.

Lemma singleton_find_inv
      tid lang (th:Thread.t lang)
      tid' th'
      (FIND: IdentMap.find tid' (Threads.singleton tid th) = Some th'):
  <<TID: tid' = tid>> /\
  <<TH: th' = existT _ lang th>>.
Proof.
  unfold Threads.singleton in *.
  rewrite IdentMap.Facts.add_o in *.
  destruct (IdentMap.Facts.eq_dec tid tid'); inv FIND; auto.
  rewrite IdentMap.Facts.empty_o in *. congruence.
Qed.

Lemma singleton_consistent
      tid lang (th:Thread.t lang) mem:
  Configuration.consistent (Configuration.mk (Threads.singleton tid th) mem) <->
  <<LE: Memory.le th.(Thread.local) mem>> /\
  <<CONSISTENT: Thread.consistent th mem>>.
Proof.
  econs; intro X.
  - inv X. ss. splits.
    + exploit LE; eauto.
      apply singleton_find.
    + eapply VALID.
      apply singleton_find.
  - des. econs; s.
    + ii.
      apply singleton_find_inv in TH1.
      apply singleton_find_inv in TH2.
      des. Configuration.simplify. congruence.
    + ii. apply singleton_find_inv in TH. des.
      Configuration.simplify.
    + i. apply singleton_find_inv in FIND. des.
      Configuration.simplify.
Qed.

Lemma singleton_is_terminal
      tid lang (th:Thread.t lang):
  Threads.is_terminal (Threads.singleton tid th) <->
  Thread.is_terminal th.
Proof.
  econs; intro X.
  - eapply X. apply singleton_find.
  - ii. apply singleton_find_inv in FIND. i. des.
    Configuration.simplify.
Qed.

Lemma singleton_add
      tid lang1 lang2 (th1:Thread.t lang1) (th2:Thread.t lang2):
  (IdentMap.add tid (existT _ lang1 th1) (Threads.singleton tid th2)) =
  Threads.singleton tid th1.
Proof.
  apply IdentMap.eq_leibniz. ii.
  unfold Threads.singleton.
  rewrite ? IdentMap.Facts.add_o.
  destruct (IdentMap.Facts.eq_dec tid y); auto.
Qed.

Lemma sim_step
      lang_src lang_tgt
      sim_terminal
      e
      th1_src mem1_src
      th1_tgt mem1_tgt
      th3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt e th1_tgt mem1_tgt th3_tgt mem3_tgt)
      (LE_SRC: Memory.le th1_src.(Thread.local) mem1_src)
      (LE_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (SIM: sim_thread sim_terminal th1_src mem1_src th1_tgt mem1_tgt):
  exists th2_src mem2_src th3_src mem3_src,
    <<STEPS: rtc (@Thread.internal_step lang_src) (th1_src, mem1_src) (th2_src, mem2_src)>> /\
    <<STEP: @Thread.step lang_src e th2_src mem2_src th3_src mem3_src>> /\
    <<LE_SRC: Memory.le th3_src.(Thread.local) mem3_src>> /\
    <<LE_TGT: Memory.le th3_tgt.(Thread.local) mem3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal th3_src mem3_src th3_tgt mem3_tgt>>.
Proof.
  exploit Thread.future_step; eauto. i. des.
  punfold SIM. exploit SIM; eauto; try reflexivity. i. des.
  exploit STEP0; eauto. i. des; [|done].
  exploit Thread.future_rtc_internal_step; eauto. s. i. des.
  exploit Thread.future_step; eauto. i. des.
  eexists _, _, _, _. splits; eauto.
Qed.

Lemma sim_rtc_internal_step
      lang_src lang_tgt
      sim_terminal
      thm1_src thm1_tgt thm2_tgt
      (STEPS: rtc (@Thread.internal_step lang_tgt) thm1_tgt thm2_tgt)
      (LE_SRC: Memory.le thm1_src.(fst).(Thread.local) thm1_src.(snd))
      (LE_TGT: Memory.le thm1_tgt.(fst).(Thread.local) thm1_tgt.(snd))
      (MEMORY: sim_memory thm1_src.(snd) thm1_tgt.(snd))
      (SIM: sim_thread sim_terminal thm1_src.(fst) thm1_src.(snd) thm1_tgt.(fst) thm1_tgt.(snd)):
  exists thm2_src,
    <<STEPS: rtc (@Thread.internal_step lang_src) thm1_src thm2_src>> /\
    <<LE_SRC: Memory.le thm2_src.(fst).(Thread.local) thm2_src.(snd)>> /\
    <<LE_TGT: Memory.le thm2_tgt.(fst).(Thread.local) thm2_tgt.(snd)>> /\
    <<MEMORY: sim_memory thm2_src.(snd) thm2_tgt.(snd)>> /\
    <<SIM: @sim_thread lang_src lang_tgt sim_terminal thm2_src.(fst) thm2_src.(snd) thm2_tgt.(fst) thm2_tgt.(snd)>>.
Proof.
  revert thm1_src LE_SRC LE_TGT MEMORY SIM. induction STEPS; i.
  { eexists _. splits; eauto. }
  inv H. destruct x, y. ss.
  exploit sim_step; try apply MEMORY; eauto. i. des.
  exploit (IHSTEPS (th3_src, mem3_src)); eauto. i. des.
  destruct thm1_src, thm2_src, z. ss.
  eexists. splits.
  - etransitivity; [eauto|]. econs 2.
    + econs. instantiate (1 := (_, _)). s. eauto.
    + eauto.
  - auto.
  - auto.
  - auto.
  - auto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      th_src mem_src
      th_tgt mem_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal th_src mem_src th_tgt mem_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (LE_SRC: Memory.le (Thread.local th_src) mem_src)
      (LE_TGT: Memory.le (Thread.local th_tgt) mem_tgt)
      (CONSISTENT: Thread.consistent th_tgt mem_tgt):
  Thread.consistent th_src mem_src.
Proof.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try reflexivity. i. des.
  ii. exploit FUTURE; eauto. i. des.
  exploit CONSISTENT; eauto; try reflexivity. i. des.
  exploit sim_rtc_internal_step;
    try instantiate (1 := (_, _));
    try apply MEMORY0; eauto.
  { s. eapply sim_thread_future; eauto. }
  s. i. des.
  destruct thm2_src. ss.
  punfold SIM0. exploit SIM0; eauto; try reflexivity. i. des.
  exploit LOCAL2; eauto. i. des.
  eexists _, _. splits; [|eauto].
  etransitivity; eauto.
Qed.


Lemma sim_thread_sim
      lang_src lang_tgt
      sim_terminal
      th1_src mem_k_src th1_tgt mem_k_tgt tid
      (SIM: @sim_thread lang_src lang_tgt sim_terminal th1_src mem_k_src th1_tgt mem_k_tgt):
  sim
    (Threads.singleton tid th1_src) mem_k_src
    (Threads.singleton tid th1_tgt) mem_k_tgt.
Proof.
  revert th1_src mem_k_src th1_tgt mem_k_tgt SIM. pcofix CIH. i. pfold. ii.
  splits.
  - i. apply (singleton_is_terminal tid) in TERMINAL_TGT.
    inv TERMINAL_TGT.
    punfold SIM0. exploit SIM0; eauto.
    { apply singleton_consistent in CONSISTENT_SRC. des. auto. }
    { apply singleton_consistent in CONSISTENT_TGT. des. auto. }
    i. des. exploit TERMINAL; eauto. i. des.
    eexists _, _. splits; [|eauto|].
    + generalize (rtc_tail STEPS). intro X. des.
      * destruct a2. inv X0. ss. econs 2; [|econs 1].
        econs; ss; eauto.
        { eapply singleton_find. }
        { ii. eexists _, _. splits; eauto. congruence. }
      * inv X. s. rewrite singleton_add. econs.
    + ii. ss.
      rewrite singleton_add in *.
      apply singleton_find_inv in FIND. des.
      Configuration.simplify.
      econs; eauto. congruence.
  - i. inv STEP_TGT. ss.
    apply singleton_find_inv in TID. des.
    Configuration.simplify.
    apply singleton_consistent in CONSISTENT_SRC.
    apply singleton_consistent in CONSISTENT_TGT.
    des.
    exploit sim_rtc_internal_step; eauto;
      try instantiate (1 := (th1_src, mem1_src)); s; eauto.
    { eapply sim_thread_future; eauto. }
    i. des. destruct thm2_src. ss.
    exploit sim_step; try apply MEMORY; eauto. i. des.
    eexists _, _, _, _. splits; eauto.
    + econs; s.
      * apply singleton_find.
      * etransitivity; eauto.
      * eauto.
      * eapply sim_thread_consistent; eauto.
    + right. s. rewrite ? singleton_add.
      apply CIH. eauto.
Qed.
