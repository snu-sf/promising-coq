Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.

Set Implicit Arguments.


Inductive opt E T (step: forall (e:option E) (tid:Ident.t) (c1 c2:T), Prop):
  forall (e:option E) (tid:Ident.t) (c1 c2:T), Prop :=
| step_none
    tid c:
    opt step None tid c c
| step_some
    e tid c1 c2
    (STEP: step e tid c1 c2):
    opt step e tid c1 c2
.
Hint Constructors opt.


Module Threads.
  Definition syntax := IdentMap.t {lang:Language.t & lang.(Language.syntax)}.
  Definition t := IdentMap.t ({lang:Language.t & lang.(Language.state)} * Local.t).

  Definition init (s:syntax): t :=
    IdentMap.map
      (fun s => (existT _ _ (s.(projT1).(Language.init) s.(projT2)), Local.init))
      s.

  Definition is_terminal (ths:t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid ths = Some (existT Language.state lang st, lc)),
      <<STATE: lang.(Language.is_terminal) st>> /\
      <<THREAD: Local.is_terminal lc>>.

  Inductive wf (ths:t) (mem:Memory.t): Prop :=
  | wf_intro
      (DISJOINT:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (TID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
      (THREADS: forall tid lang st lc
                  (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
          Local.wf lc mem)
  .

  Definition consistent (ths:t) (sc:TimeMap.t) (mem:Memory.t): Prop :=
    forall tid lang st lc
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      Thread.consistent (Thread.mk lang st lc sc mem).

  Inductive disjoint (ths1 ths2:t): Prop :=
  | disjoint_intro
      (THREAD:
         forall tid llc1 llc2
           (TH1: IdentMap.find tid ths1 = Some llc1)
           (TH2: IdentMap.find tid ths2 = Some llc2),
           False)
      (MEMORY:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (TH1: IdentMap.find tid1 ths1 = Some (existT _ lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths2 = Some (existT _ lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
  .

  Lemma init_wf syn: wf (init syn) Memory.init.
  Proof.
    econs.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid1 syn); inv TH1.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid2 syn); inv TH2.
      econs. ss. econs. i. rewrite Memory.bot_get in *. congr.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid syn); inv TH.
      econs; ss.
      + apply TView.bot_wf.
      + apply TView.bot_closed.
      + ii. rewrite Memory.bot_get in LHS. congr.
      + apply Memory.bot_finite.
  Qed.

  Lemma init_consistent syn: consistent (init syn) TimeMap.bot Memory.init.
  Proof.
    ii. ss. esplits; eauto. s.
    unfold init in *. rewrite IdentMap.Facts.map_o in *.
    destruct (UsualFMapPositive.UsualPositiveMap'.find tid syn); inv TH. ss.
  Qed.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs; i.
    - eapply THREAD; eauto.
    - symmetry. eapply MEMORY; eauto.
  Qed.

  Definition compose_option {A} (lc1 lc2:option A) :=
    match lc1 with
    | None => lc2
    | Some _ => lc1
    end.

  Definition compose (ths1 ths2:t): t :=
    IdentMap.map2 compose_option ths1 ths2.

  Lemma compose_spec ths1 ths2 tid:
    IdentMap.find tid (compose ths1 ths2) = compose_option (IdentMap.find tid ths1) (IdentMap.find tid ths2).
  Proof. apply IdentMap.Facts.map2_1bis; auto. Qed.

  Inductive is_promised tid (loc:Loc.t) (to:Time.t) (threads:t): Prop :=
  | is_promised_intro
      lang st lc from msg
      (TID: IdentMap.find tid threads = Some (existT _ lang st, lc))
      (PROMISES: Memory.get loc to lc.(Local.promises) = Some (from, msg))
  .
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    sc: TimeMap.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) TimeMap.bot Memory.init.

  Definition is_terminal (conf:t): Prop := Threads.is_terminal conf.(threads).

  Inductive wf (conf:t): Prop :=
  | wf_intro
      (WF: Threads.wf conf.(threads) conf.(memory))
      (SC: Memory.closed_timemap conf.(sc) conf.(memory))
      (MEM: Memory.closed conf.(memory))
  .

  Definition consistent (conf:t): Prop :=
    Threads.consistent conf.(threads) conf.(sc) conf.(memory).

  Lemma init_wf syn: wf (init syn).
  Proof.
    econs.
    - apply Threads.init_wf.
    - viewtac.
    - apply Memory.init_closed.
  Qed.

  Lemma init_consistent syn: consistent (init syn).
  Proof.
    apply Threads.init_consistent.
  Qed.

  Inductive step: forall (e:option Event.t) (tid:Ident.t) (c1 c2:t), Prop :=
  | step_intro
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(sc) c1.(memory)) e2)
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (CONSISTENT: Thread.consistent (Thread.mk lang st3 lc3 sc3 memory3)):
      step (ThreadEvent.get_event e) tid c1 (mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(threads)) sc3 memory3)
  .

  Definition opt_step := opt step.

  Definition tau_step := union (step None).

  Inductive has_promise (c:t): Prop :=
  | has_promise_intro
      tid st lc loc from to msg
      (FIND: IdentMap.find tid c.(threads) = Some (st, lc))
      (GET: Memory.get loc to lc.(Local.promises) = Some (from, msg))
  .

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: (_, _) = (_, _) |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?P ?q _ |- _] =>
             apply eq_sigT_sig_eq in H; inv H
           end;
       ss; subst).

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv WF1. inv WF. inv STEP. s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    splits; [| |by etrans; eauto|by etrans; eauto].
    - econs; ss. econs.
      + i. simplify.
        * exploit THREADS; try apply TH1; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. s. i. des.
          symmetry. auto.
        * exploit THREADS; try apply TH2; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
          exploit Thread.step_disjoint; eauto. i. des.
          auto.
        * eapply DISJOINT; [|eauto|eauto]. auto.
      + i. simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
    - ii. simplify; eauto.
      eapply CONSISTENT1; eauto.
      + s. repeat (etrans; eauto).
      + s. repeat (etrans; eauto).
  Qed.

  Lemma step_disjoint
        e tid c1 c2 ths
        (STEP: step e tid c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1)
        (WF: wf (mk ths c1.(sc) c1.(memory)))
        (CONSISTENT: consistent (mk ths c1.(sc) c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<WF: wf (mk ths c2.(sc) c2.(memory))>> /\
      <<CONSISTENT: consistent (mk ths c2.(sc) c2.(memory))>>.
  Proof.
    inv STEP. ss.
    exploit Thread.rtc_tau_step_future; eauto.
    { econs; eapply WF1; eauto. }
    { apply WF1. }
    { apply WF1. }
    s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    splits.
    - econs; s; ii; simplify.
      + inv DISJOINT. eapply THREAD; eauto.
      + inv DISJOINT. eapply THREAD; eauto.
      + exploit Thread.rtc_tau_step_disjoint; eauto; s.
        { econs; eapply WF1; eauto. }
        { apply WF1. }
        { apply WF1. }
        { eapply DISJOINT; eauto. }
        { eapply WF; eauto. }
        i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        auto.
      + inv DISJOINT. eapply MEMORY; eauto.
    - econs; s; eauto.
      + econs.
        * i. eapply WF; eauto.
        * i.
          exploit Thread.rtc_tau_step_disjoint; eauto.
          { econs; eapply WF1; eauto. }
          { apply WF1. }
          { apply WF1. }
          { eapply DISJOINT; eauto. }
          { eapply WF; eauto. }
          i. des.
          exploit Thread.step_disjoint; eauto. s. i. des.
          splits; ss.
    - ii. ss.
      exploit Thread.rtc_tau_step_disjoint; eauto.
      { econs; eapply WF1; eauto. }
      { apply WF1. }
      { apply WF1. }
      { eapply DISJOINT; eauto. }
      { eapply WF; eauto. }
      i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      eapply CONSISTENT; eauto.
      + s. etrans; eauto. etrans; eauto.
      + s. etrans; eauto. etrans; eauto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv STEP.
    - splits; auto; refl.
    - eapply step_future; eauto.
  Qed.

  Lemma opt_step_disjoint
        e tid c1 c2 ths
        (STEP: opt_step e tid c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1)
        (WF: wf (mk ths c1.(sc) c1.(memory)))
        (CONSISTENT: consistent (mk ths c1.(sc) c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<WF: wf (mk ths c2.(sc) c2.(memory))>> /\
      <<CONSISTENT: consistent (mk ths c2.(sc) c2.(memory))>>.
  Proof.
    inv STEP.
    - splits; auto; refl.
    - eapply step_disjoint; eauto.
  Qed.

  Lemma rtc_step_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    revert CONSISTENT1. induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.

  Lemma rtc_step_disjoint
        c1 c2 ths
        (STEPS: rtc tau_step c1 c2)
        (DISJOINT: Threads.disjoint c1.(threads) ths)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1)
        (WF: wf (mk ths c1.(sc) c1.(memory)))
        (CONSISTENT: consistent (mk ths c1.(sc) c1.(memory))):
      <<DISJOINT: Threads.disjoint c2.(threads) ths>> /\
      <<WF: wf (mk ths c2.(sc) c2.(memory))>> /\
      <<CONSISTENT: consistent (mk ths c2.(sc) c2.(memory))>>.
  Proof.
    revert DISJOINT CONSISTENT1 CONSISTENT. induction STEPS; auto. i. inv H.
    exploit step_future; eauto. i. des.
    exploit step_disjoint; eauto. i. des.
    apply IHSTEPS; auto.
  Qed.
End Configuration.
