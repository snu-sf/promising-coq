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
Require Import Upto4.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Inductive sim_ctx_terminal: forall (th_src th_tgt:Thread.t), Prop :=
| sim_ctx_terminal_intro
    rs commit:
    sim_ctx_terminal
      (Thread.mk (Language.State.mk lang (State.mk rs nil)) commit Memory.init)
      (Thread.mk (Language.State.mk lang (State.mk rs nil)) commit Memory.init)
.

Definition sim_ctx_interference
           (th1_src:Thread.t) (mem_k_src:Memory.t)
           (th1_tgt:Thread.t) (mem_k_tgt:Memory.t): Prop :=
  forall mem1_src mem1_tgt
    (MEMORY1: sim_memory mem1_src mem1_tgt)
    (LOCAL_SRC: Memory.le th1_src.(Thread.local) mem1_src)
    (LOCAL_TGT: Memory.le th1_tgt.(Thread.local) mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt),
    <<TERMINAL:
      forall (TERMINAL_TGT: Thread.is_terminal th1_tgt),
      exists th2_src mem2_src,
        <<STEPS: rtc Thread.internal_step (th1_src, mem1_src) (th2_src, mem2_src)>> /\
        <<TERMINAL_SRC: Thread.is_terminal th2_src>> /\
        <<CTX: sim_ctx_terminal th2_src th1_tgt>>>> /\
    <<DECLARE:
      forall (TERMINAL_TGT: th1_tgt.(Thread.local) = Memory.init),
      exists th2_src mem2_src,
        <<STEPS: rtc Thread.internal_step (th1_src, mem1_src) (th2_src, mem2_src)>> /\
        <<TERMINAL_SRC: th2_src.(Thread.local) = Memory.init>>>>.

Definition _sim_ctx R := sim_ctx_interference /4\ _sim_thread_step R.

Lemma _sim_ctx_future
      r1 r2
      th_src mem1_src mem2_src
      th_tgt mem1_tgt mem2_tgt
      (R: r1 <4= r2)
      (SRC: Memory.future mem1_src mem2_src)
      (TGT: Memory.future mem1_tgt mem2_tgt)
      (SIM: _sim_ctx r1 th_src mem1_src th_tgt mem1_tgt):
  _sim_ctx r2 th_src mem2_src th_tgt mem2_tgt.
Proof.
  ii. unfold _sim_ctx in *. des. splits.
  - ii. exploit SIM; eauto; etransitivity; eauto.
  - ii. exploit SIM0; eauto.
    + etransitivity; eauto.
    + etransitivity; eauto.
    + i. des. eexists _, _. eauto.
Qed.

Lemma _sim_ctx_mon: monotone4 _sim_ctx.
Proof.
  ii. unfold _sim_ctx in IN. des.
  split; auto. eapply _sim_thread_step_mon; eauto.
Qed.
Hint Resolve _sim_ctx_mon: paco.

Definition sim_ctx: SIM_THREAD := paco4 _sim_ctx bot4.

Definition _sim_stmts
           (sim_thread:SIM_THREAD)
           (stmts_src:list Stmt.t) (mem_k_src:Memory.t)
           (stmts_tgt:list Stmt.t) (mem_k_tgt:Memory.t): Prop :=
  forall rs commit local,
    _sim_ctx
      sim_thread
      (Thread.mk (Language.State.mk lang (State.mk rs stmts_src)) commit local) mem_k_src
      (Thread.mk (Language.State.mk lang (State.mk rs stmts_tgt)) commit local) mem_k_tgt.

Lemma _sim_stmts_future
      r1 r2
      stmts_src mem1_src mem2_src
      stmts_tgt mem1_tgt mem2_tgt
      (R: r1 <4= r2)
      (SRC: Memory.future mem1_src mem2_src)
      (TGT: Memory.future mem1_tgt mem2_tgt)
      (SIM: _sim_stmts r1 stmts_src mem1_src stmts_tgt mem1_tgt):
  _sim_stmts r2 stmts_src mem2_src stmts_tgt mem2_tgt.
Proof.
  unfold _sim_stmts in *. i.
  eapply _sim_ctx_future; eauto.
Qed.
Hint Resolve _sim_stmts_future: paco.

Inductive ctx (sim_thread:SIM_THREAD): SIM_THREAD :=
| ctx_refl
    st commit local mem_k_src mem_k_tgt:
    ctx sim_thread
        (Thread.mk (Language.State.mk lang st) commit local) mem_k_src
        (Thread.mk (Language.State.mk lang st) commit local) mem_k_tgt
| ctx_incl
    th1 mem_k_src th2 mem_k_tgt
    (SIM: sim_thread th1 mem_k_src th2 mem_k_tgt):
    ctx sim_thread th1 mem_k_src th2 mem_k_tgt
| ctx_seq
    stmts1_src stmts2_src mem_k_src
    stmts1_tgt stmts2_tgt mem_k_tgt
    rs commit local
    (SIM1: _sim_stmts sim_thread stmts1_src mem_k_src stmts1_tgt mem_k_tgt)
    (SIM2: _sim_stmts sim_thread stmts2_src mem_k_src stmts2_tgt mem_k_tgt):
    ctx sim_thread
        (Thread.mk (Language.State.mk lang (State.mk rs (stmts1_src ++ stmts2_src))) commit local) mem_k_src
        (Thread.mk (Language.State.mk lang (State.mk rs (stmts1_tgt ++ stmts2_tgt))) commit local) mem_k_tgt
| ctx_ite
    stmts1_src stmts2_src mem_k_src
    stmts1_tgt stmts2_tgt mem_k_tgt
    e
    rs commit local
    (SIM1: _sim_stmts sim_thread stmts1_src mem_k_src stmts1_tgt mem_k_tgt)
    (SIM2: _sim_stmts sim_thread stmts2_src mem_k_src stmts2_tgt mem_k_tgt):
    ctx sim_thread
        (Thread.mk (Language.State.mk lang (State.mk rs [Stmt.ite e stmts1_src stmts2_src])) commit local) mem_k_src
        (Thread.mk (Language.State.mk lang (State.mk rs [Stmt.ite e stmts1_tgt stmts2_tgt])) commit local) mem_k_tgt
| ctx_dowhile
    stmts_src mem_k_src
    stmts_tgt mem_k_tgt
    e
    rs commit local
    (SIM: _sim_stmts sim_thread stmts_src mem_k_src stmts_tgt mem_k_tgt):
    ctx sim_thread
        (Thread.mk (Language.State.mk lang (State.mk rs [Stmt.dowhile stmts_src e])) commit local) mem_k_src
        (Thread.mk (Language.State.mk lang (State.mk rs [Stmt.dowhile stmts_tgt e])) commit local) mem_k_tgt
.
Hint Constructors ctx.

Lemma simplify_lang_step
      lang s1 e st2
      (STEP: Language.State.step (Language.State.mk lang s1) e st2):
  exists s2,
    <<ST2: st2 = Language.State.mk lang s2>> /\
    <<STEP: lang.(Language.step) s1 e s2>>.
Proof.
  inv STEP.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H1. subst.
  eexists. splits; eauto.
Qed.

Ltac simplify :=
  repeat
    ((try match goal with
          | [H: Language.State.step (Language.State.mk lang _) _ _ |- _] =>
            apply simplify_lang_step in H; des
          end);
     simpl in *; subst).

Lemma ctx_is_respectful: respectful _sim_ctx ctx.
Proof.
  econs.
  { (* monotone *)
    ii. inv IN.
    - econs 1.
    - econs 2. auto.
    - econs 3; eapply _sim_stmts_future; eauto; reflexivity.
    - econs 4; eapply _sim_stmts_future; eauto; reflexivity.
    - econs 5; eapply _sim_stmts_future; eauto; reflexivity.
  }
  i. destruct PR.
  - (* refl *)
    econs.
    { ii. simpl in *. splits.
      - intro X. inv X. simpl in *.
        inv STATE. destruct st. simpl in *. subst.
        eexists _, _. splits; eauto; econs; eauto.
        econs.
      - i. subst.
        eexists _, _. splits; eauto.
    }
    ii. simpl in *. inv STEP_TGT.
    + inv STEP; simplify.
      * eexists _, _. splits; eauto.
        econs 1. econs 1; eauto.
        { econs. eauto. }
        { apply MEMORY1. auto. }
      * eexists _, _. splits; eauto.
        econs 1. econs 2; eauto.
        econs. eauto.
      * eexists _, _. splits; eauto.
        econs 1. econs 3; eauto.
        { econs. eauto. }
        { apply MEMORY1. auto. }
      * eexists _, _. splits; eauto.
        econs 1. econs 4; eauto.
        econs. auto.
      * eexists _, _. splits; eauto.
        econs 1. econs 5; auto.
    + inv STEP. simpl in *.
      admit. (* declare *)
    + simplify. inv STEP.
      eexists _, _. splits; eauto.
      econs; auto. econs. econs. auto.
  - (* incl *)
    eapply _sim_ctx_mon; eauto.
  - (* seq *)
    admit.
  - (* ite *)
    econs.
    { ii. simpl in *. splits.
      - intro X. inv X. inv STATE.
      - i. subst. exploit SIM1; eauto.
    }
    ii. simpl in *. inv STEP_TGT.
    + inv STEP; simplify; try inv STEP.
      eexists _, _. splits.
      * econs. econs 5. eauto.
      * auto.
      * simpl in *. apply ctx_ite.
        { eapply _sim_stmts_future; eauto. }
        { eapply _sim_stmts_future; eauto. }
    + admit. (* declare *)
    + simplify. inv STEP.
  - (* dowhile *)
    econs.
    { ii. simpl in *. splits.
      - intro X. inv X. inv STATE.
      - i. subst. exploit SIM; eauto.
    }
    ii. simpl in *. inv STEP_TGT.
    + inv STEP; simplify; try inv STEP.
      eexists _, _. splits.
      * econs. econs 5. eauto.
      * auto.
      * simpl in *. apply ctx_dowhile.
        eapply _sim_stmts_future; eauto.
    + admit. (* declare *)
    + simplify. inv STEP.
Admitted.

Lemma sim_ctx_thread: sim_ctx <4= sim_thread.
Proof.
  pcofix CIH. i. punfold PR. destruct PR as [INT STEP].
  pfold. econs.
  - ii. exploit INT; eauto. i. des. splits; eauto.
    i. exploit TERMINAL; eauto. i. des. eauto.
  - ii. exploit STEP; eauto. i. des; [|inv SIM].
    eexists _, _. splits; eauto.
Qed.

Definition sim_ctx_init stmts_src stmts_tgt :=
  forall rs commit local,
    sim_ctx
      (Thread.mk (Language.State.mk lang (State.mk rs stmts_src)) commit local) Memory.init
      (Thread.mk (Language.State.mk lang (State.mk rs stmts_tgt)) commit local) Memory.init.
