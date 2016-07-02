Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.

Definition option_app {A} (a b: option A) : option A :=
  if a then a else b.

Lemma option_map_map 
      A B C (f: B -> C) (g: A -> B) (a: option A):
  option_map f (option_map g a) = option_map (fun x => f (g x)) a.
Proof.
  destruct a; eauto.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Definition ThreadEvent_is_promising (e: ThreadEvent.t) : option (Loc.t * Time.t) :=
  match e with
  | ThreadEvent.promise loc from to v rel => Some (loc, to)
  | _ => None
  end.





Inductive step_union {A} {E} (step: E -> A -> A -> Prop) (c1 c2: A) : Prop :=
| step_evt_intro e
    (USTEP: step e c1 c2)
.
Hint Constructors step_union.

Inductive with_pre {A} {E} (step: E -> A -> A -> Prop) bs : option (A*E) ->  A -> Prop :=
| swp_base:
  with_pre step bs None bs
| swp_step
    pre ms e es
    (PSTEPS: with_pre step bs pre ms)
    (PSTEP: step e ms es):
  with_pre step bs (Some(ms,e)) es
.
Hint Constructors with_pre.

Lemma with_pre_rtc_step_union
      A E (step: E -> A -> A -> Prop) c1 c2 pre
      (STEPS: with_pre step c1 pre c2):
  rtc (step_union step) c1 c2.
Proof.
  ginduction STEPS; s; i; subst; eauto.
  i. etrans; eauto.
  econs 2; [|reflexivity]. eauto.
Qed.

Lemma rtc_step_union_with_pre
      A E (step: E -> A -> A -> Prop) c1 c2
      (STEPS: rtc (step_union step) c1 c2):
  exists pre,
  with_pre step c1 pre c2.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEPS.
  induction STEPS.
  { exists None. eauto. }
  des. inv H. exists (Some(y,e)). s. eauto.
Qed.

Lemma with_pre_implies
      E A (step step': E -> A -> A -> Prop) c1 c2 pre
      (IMPL: forall e c1 c2 (STEP: step e c1 c2), step' e c1 c2)
      (STEPS: with_pre step c1 pre c2):
  with_pre step' c1 pre c2.
Proof.
  induction STEPS; eauto.
Qed.

Lemma with_pre_trans 
      A E (step: E -> A -> A -> Prop) c1 c2 c3 pre1 pre2
      (STEPS1: with_pre step c1 pre1 c2)
      (STEPS2: with_pre step c2 pre2 c3):
  with_pre step c1 (option_app pre2 pre1) c3.
Proof.
  ginduction STEPS2; s; i; des; subst; eauto.
Qed.













Definition Thread_step_all {lang} (t1 t2:Thread.t lang) : Prop :=
  step_union (@Thread.step lang) t1 t2.
Hint Unfold Thread_step_all.


Inductive small_step (withprm: bool) (tid:Ident.t) (e:ThreadEvent.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 st2 lc1 ths2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2))
    (THS2: ths2 = IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads))
    (PFREE: if withprm then True else ThreadEvent_is_promising e = None)
  :
  small_step withprm tid e c1 (Configuration.mk ths2 sc2 memory2)
.
Hint Constructors small_step.

Definition small_step_evt withprm (tid:Ident.t) (c1 c2:Configuration.t) : Prop :=
  step_union (small_step withprm tid) c1 c2.
Hint Unfold small_step_evt.

Definition small_step_all withprm (c1 c2:Configuration.t) : Prop :=
  step_union (small_step_evt withprm) c1 c2.
Hint Unfold small_step_all.


Lemma small_step_future
      e tid c1 c2 withprm
      (WF1: Configuration.wf c1)
      (STEP: small_step withprm e tid c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  inv WF1. inv WF. inv STEP. ss. clear PFREE.
  exploit THREADS; ss; eauto. i.
  exploit Thread.step_future; eauto.
  s; i; des. splits; [|by eauto]. econs; ss. econs.
  - i. Configuration.simplify.
    + congr.
    + exploit THREADS; try apply TH1; eauto. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      symmetry. auto.
    + exploit THREADS; try apply TH2; eauto. i. des.
      exploit Thread.step_disjoint; eauto. i. des.
      auto.
    + eapply DISJOINT; [|eauto|eauto]. auto.
  - i. Configuration.simplify.
    exploit THREADS; try apply TH; eauto. i.
    exploit Thread.step_disjoint; eauto. s. i. des.
    auto.
Qed.

Lemma rtc_small_step_future
      c1 c2 withprm
      (WF1: Configuration.wf c1)
      (STEP: rtc (small_step_all withprm) c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  revert WF1. induction STEP; i.
  - splits; eauto; reflexivity.
  - destruct H. destruct USTEP. 
    exploit small_step_future; eauto. i; des.
    exploit IHSTEP; eauto. i; des.
    splits; eauto. etrans; eauto.
Qed.

Lemma thread_step_small_step
      lang e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: Thread.step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step true tid e
             (Configuration.mk threads sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  econs; eauto.
Qed.

Lemma thread_step_small_step_aux
      lang e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step true tid e
             (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc1) threads) sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit thread_step_small_step; eauto.
  { eapply IdentMap.Facts.add_eq_o. eauto. }
  rewrite (IdentMap.add_add_eq tid (existT Language.state lang st2, lc2)). eauto.
Qed.

Lemma rtc_thread_step_rtc_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (@Thread_step_all lang)) th1 th2):
  rtc (small_step_evt true tid)
      (Configuration.mk threads th1.(Thread.sc) th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.sc) th2.(Thread.memory)).
Proof.
  revert threads TID. induction STEP; i.
  - apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
    rewrite IdentMap.Facts.add_o. condtac; auto. subst. auto.
  - inv H. destruct x, y. ss. econs 2.
    + econs; eauto.
    + etrans; [eapply IHSTEP|].
      * apply IdentMap.Facts.add_eq_o. auto.
      * apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
        rewrite ? IdentMap.Facts.add_o. condtac; auto.
Qed.

Lemma rtc_thread_step_rtc_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (@Thread_step_all lang)) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (small_step_evt true tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit rtc_thread_step_rtc_small_step_aux; eauto. auto.
Qed.

Lemma step_small_steps
      e tid c1 c3
      (STEP: Configuration.step e tid c1 c3)
      (WF1: Configuration.wf c1)
      (CONSISTENT1: Configuration.consistent c1):
    <<STEPS: rtc (small_step_evt true tid) c1 c3>> /\
    <<WF3: Configuration.wf c3>> /\
    <<CONSISTENT3: Configuration.consistent c3>>.
Proof.
  exploit Configuration.step_future; eauto. i. des.
  inv STEP. destruct c1, e2. ss. esplits; [|eauto|eauto].
  etrans.
  - eapply rtc_thread_step_rtc_small_step; cycle 1.
    + eapply rtc_implies, STEPS.
      i. inv PR. econs; eauto.
    + eauto.
  - econs; eauto. econs. econs; s; cycle 1; eauto.
    + rewrite IdentMap.add_add_eq. auto.
    + rewrite IdentMap.gss. eauto.
Qed.

Lemma small_step_find
      tid1 tid2 c1 c2 e withprm
      (STEP: small_step withprm tid1 e c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  inv STEP. s.
  rewrite IdentMap.gso; eauto.
Qed.

Lemma rtc_small_step_find
      tid1 tid2 c1 c2 withprm
      (STEP: rtc (small_step_evt withprm tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  induction STEP; auto. 
  inv H. rewrite <-IHSTEP.
  eauto using small_step_find.
Qed.

Lemma thread_step_commit_future
     lang e (t1 t2: @Thread.t lang)
     (STEP: Thread.step e t1 t2):
  Commit.le t1.(Thread.local).(Local.commit) t2.(Thread.local).(Local.commit).
Proof.
Admitted. (* Done *)

Lemma rtc_small_step_commit_future
     c1 c2 tid lst1 lst2 lc1 lc2 withprm
     (STEPS: rtc (small_step_evt withprm tid) c1 c2)
     (THREAD1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
     (THREAD2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2)):
  Commit.le lc1.(Local.commit) lc2.(Local.commit).
Proof.
  ginduction STEPS; i.
  - rewrite THREAD1 in THREAD2. depdes THREAD2. reflexivity.
  - destruct H. destruct USTEP. rewrite THREAD1 in TID. depdes TID.
      etrans; [apply (thread_step_commit_future STEP)|].
      eapply IHSTEPS; eauto.
      s. subst. rewrite IdentMap.gss. eauto.
Qed.

Lemma write_step_lt
      tid c c1 e lst lc loc from ts val rel ord withprm
      (STEP: small_step withprm tid e c c1)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
      (THREAD: IdentMap.find tid (Configuration.threads c) = Some (lst, lc))
: Time.lt (lc.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
Admitted.






















(* NOTE: `race_rw` requires two *distinct* threads to have a race.
 * However, C/C++ acknowledges intra-thread races.  For example,
 * according to the Standard, `f(x=1, x)` is RW-racy on `x`, since the
 * order of evaluation of the arguments is unspecified.  We currently
 * ignore this aspect of the race semantics.
 *)

Inductive Configuration_program_event c tid e : Prop :=
| configuration_program_event_intro lang st st' lc
    (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc))
    (STATE: lang.(Language.step) (Some e) st st').
Hint Constructors Configuration_program_event.

Inductive race_condition e1 e2 ord1 ord2 : Prop :=
| race_condition_rw loc
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2))
| race_condition_ww loc
    (EVENT1: ProgramEvent.is_writing e1 = Some (loc, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2))
.
Hint Constructors race_condition.

Inductive race (c:Configuration.t) (ord1 ord2:Ordering.t): Prop :=
| race_intro
    tid1 e1
    tid2 e2
    (TID: tid1 <> tid2)
    (PROEVT1: Configuration_program_event c tid1 e1)
    (PROEVT2: Configuration_program_event c tid2 e2)
    (RACE: race_condition e1 e2 ord1 ord2)
.
Hint Constructors race.            

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc (small_step_all false) c1 c2)
    (RACE: race c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Lemma pf_racefree_steps
      c1 c2
      (FREE: pf_racefree c1)
      (STEPS: rtc (small_step_all false) c1 c2):
  pf_racefree c2.
Proof.
  ii. eapply FREE, RACE. etrans; eauto.
Qed.

Lemma small_step_to_program_step_writing
      c1 c2 e tid loc ord from ts val rel withprm
      (STEP: small_step withprm tid e c1 c2)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)):
  exists (pe : ProgramEvent.t),
  <<EVENT: Configuration_program_event c1 tid pe >> /\
  <<WRITE: ProgramEvent.is_writing pe = Some (loc, ord) >>.
Proof.
  inv STEP. inv STEP0; inv STEP; inv EVENT; eauto 10.
Qed.

Lemma small_step_to_program_step_reading
      c1 c2 e tid loc ord ts val rel withprm
      (STEP: small_step withprm tid e c1 c2)
      (EVENT: ThreadEvent.is_reading e = Some (loc, ts, val, rel, ord)):
  exists (pe : ProgramEvent.t),
  <<EVENT: Configuration_program_event c1 tid pe >> /\
  <<WRITE: ProgramEvent.is_reading pe = Some (loc, ord) >>.
Proof.
  inv STEP. inv STEP0; inv STEP; inv EVENT; eauto 10.
Qed.



































Inductive pi_step withprm: Ident.t -> ThreadEvent.t -> Configuration.t*Configuration.t -> Configuration.t*Configuration.t -> Prop :=
| pi_step_step
    e tid cS1 cT1 cS2 cT2
    (STEPT: small_step withprm tid e cT1 cT2)
    (STEPS: if ThreadEvent_is_promising e
            then cS1 = cS2
            else small_step false tid e cS1 cS2)
    (LANGMATCH: 
     option_map fst (IdentMap.find tid cS2.(Configuration.threads)) =
     option_map fst (IdentMap.find tid cT2.(Configuration.threads)))
    (NOWR: forall loc from ts val rel ord tid' ts'
             (WRITE:ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
             (TIDNEQ: tid' <> tid),
           ~ Threads.is_promised tid' loc ts' cT1.(Configuration.threads)):
  pi_step withprm tid e (cS1,cT1) (cS2,cT2)
.
Hint Constructors pi_step.

Definition pi_step_evt withprm tid cST1 cST2: Prop :=
  step_union (pi_step withprm tid) cST1 cST2.
Hint Unfold pi_step_evt.

Definition pi_step_all withprm cST1 cST2: Prop :=
  step_union (pi_step_evt withprm) cST1 cST2.
Hint Unfold pi_step_all.

Inductive pi_step_except (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro tid
    (PI_STEP: pi_step_evt true tid cST1 cST2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_except.

Definition remove_promise (th: {lang : Language.t & Language.state lang} * Local.t) :=
  (th.(fst), Local.mk th.(snd).(Local.commit) Memory.bot).

Inductive pi_wf: Configuration.t*Configuration.t -> Prop :=
| pi_wf_intro cS cT
    (WFS: Configuration.wf cS)
    (WFT: Configuration.wf cT)
    (THS: cS.(Configuration.threads) = IdentMap.map remove_promise cT.(Configuration.threads))
    (SC: cS.(Configuration.sc) = cT.(Configuration.sc))
    (LR: forall loc ts from msg
           (IN: Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)),
         <<IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
         <<NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)>>)
    (RL: forall loc ts from msg
           (IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg))
           (NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)),
         Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)):
  pi_wf (cS,cT)
.
Hint Constructors pi_wf.

Inductive pi_consistent: Configuration.t*Configuration.t -> Prop :=
| pi_consistent_intro cS1 cT1
  (CONSIS:
    forall tid cS2 cT2 lst2 lc2 loc ts from msg
    (STEPS: rtc (pi_step_except tid) (cS1,cT1) (cS2,cT2))
    (THREAD: IdentMap.find tid cT2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from, msg)),
  exists cS3 e ord,
    <<STEPS: rtc (small_step_evt false tid) cS2 cS3>> /\
    <<PROEVT: Configuration_program_event cS3 tid e>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>):
  pi_consistent (cS1, cT1).
Hint Constructors pi_consistent.

Inductive conf_local_wf tid (c: Configuration.t) : Prop :=
| conf_local_wf_intro
    (LWF: forall lst lc
            (FIND: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc)),
          Local.wf lc c.(Configuration.memory))
    (MCLOTM: Memory.closed_timemap c.(Configuration.sc) c.(Configuration.memory))
    (MCLO: Memory.closed c.(Configuration.memory)).
 
Inductive pi_local_wf tid (promise_oth: Loc.t -> Time.t -> Prop) : Configuration.t*Configuration.t -> Prop :=
| pi_local_wf_intro cS cT
    (WFS: conf_local_wf tid cS)
    (WFT: conf_local_wf tid cT)
    (THS: IdentMap.find tid cS.(Configuration.threads) =
          option_map remove_promise (IdentMap.find tid cT.(Configuration.threads)))
    (SC: cS.(Configuration.sc) = cT.(Configuration.sc))
    (LR: forall loc ts from msg
           (IN: Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)),
         <<IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
         <<NOTPRSELF: ~ Threads.is_promised tid loc ts cT.(Configuration.threads)>> /\
         <<NOTPROTH: ~ promise_oth loc ts>>)
    (RL: forall loc ts from msg
           (IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg))
           (NOTPRSELF: ~ Threads.is_promised tid loc ts cT.(Configuration.threads))
           (NOTPROTH: ~ promise_oth loc ts),
         Memory.get loc ts cS.(Configuration.memory) = Some (from, msg))
    (PRM: forall loc ts 
            (PROTH: promise_oth loc ts),
          <<IN: exists from msg, Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
          <<NOTPRSELF: ~Threads.is_promised tid loc ts cT.(Configuration.threads)>>)
:
  pi_local_wf tid promise_oth (cS,cT)
.

Inductive promises_except tid (c: Configuration.t) loc ts : Prop :=
| promises_except_intro tid1
    (NEQ: tid1 <> tid)
    (PRM: Threads.is_promised tid1 loc ts c.(Configuration.threads))
.

Definition promise_consistent (tid: Ident.t) (c: Configuration.t) : Prop :=
  forall lst lc loc ts from msg
         (THREAD: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc))
         (PROMISE: Memory.get loc ts lc.(Local.promises) = Some (from, msg)),
  Time.lt (lc.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.

Definition pi_pre_proj (pre: option (Configuration.t*Configuration.t*ThreadEvent.t)) := 
  option_map (fun p => (p.(fst).(snd),p.(snd))) pre.


Lemma conf_wf_local_wf
    tid c
    (WF: Configuration.wf c):
  conf_local_wf tid c. 
Proof.
  inv WF. inv WF0. 
  econs; eauto.
  i. destruct lst. eauto.
Qed.

Lemma pi_wf_pi_local_wf
      cST tid
      (WF: pi_wf cST):
  pi_local_wf tid (promises_except tid cST.(snd)) cST.
Proof.
  inv WF. econs; eauto using conf_wf_local_wf.
  - rewrite THS. rewrite IdentMap.Properties.F.map_o. eauto.
  - i. apply LR in IN. des.
    esplits; eauto.
    intro X. destruct X.
    eapply NOT. eauto.
  - i. eapply RL; eauto.
    intros tid1 PRM.
    destruct (Ident.eq_dec tid1 tid) eqn: EQ.
    + subst. eauto.
    + apply NOTPROTH. econs; eauto.
  - i. destruct PROTH. inv PRM. ss.
    inv WFT. inv WF.
    esplits; eauto.
    + exploit THREADS; eauto.
      intro X. inv X.
      eapply PROMISES0. eauto.
    + intro X. inv X.
      exploit DISJOINT; eauto.
      intro X. inv X.
      admit. (* with PROMISES, PROMISES0, DISJOINT0 *)
Admitted.

Lemma rtc_pi_step_local_wf
      cST1 cST2 tid oth withprm
      (MATCH: pi_local_wf tid oth cST1)
      (STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  pi_local_wf tid oth cST2.
Proof.
(*
  induction STEPS; eauto.
  apply IHSTEPS. clear IHSTEPS STEPS z.
  unfold pi_local_wf, remove_promise, mem_sub in *.
  ss. des. rename MATCH0 into MATCH. 
  inv H. inv PI_STEP. inv STEPT. inv STEP; inv STEP0; ss.
  - subst. rewrite IdentMap.gss, MATCH, TID.
    inv LOCAL; esplits; eauto.
    i. apply MEMLE in IN. des. subst. esplits; eauto.
    admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. depdes MATCH. ss. 
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. rewrite SCMAT. ss.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. rewrite SCMAT. ss.
    esplits; eauto.
    + do 3 f_equal.
      admit.
    + i.
      admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL1. inv LOCAL0. inv LOCAL2. inv LOCAL3. rewrite SCMAT.
    s. esplits; eauto. 
    + do 3 f_equal. s in WRITE0.
      admit.
    + i.
      admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. ss. by rewrite SCMAT.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. ss. by rewrite SCMAT.
*)
Admitted.

Lemma pi_step_future
      tid cST1 cST2 withprm
      (WF1: pi_wf cST1)
      (STEP: pi_step_evt withprm tid cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  inv WF1. inv STEP. inv USTEP. splits; cycle 1. 
  - destruct (ThreadEvent_is_promising e).
    + subst. ss. econs.
    + eapply small_step_future in STEPS; eauto; des; ss.
  - eapply small_step_future in STEPT; eauto; des; ss.
  - assert (WFT2: Configuration.wf cT2).
    { by eapply small_step_future, STEPT. }
    assert (WFS2: Configuration.wf cS2).
    { destruct (ThreadEvent_is_promising e); [by inv STEPS|].
      by eapply small_step_future, STEPS. }
    destruct cS. inv STEPT. inv STEP; inv STEP0; ss.
    { subst. inv LOCAL. econs; eauto.
      - apply IdentMap.eq_leibniz.
        ii. setoid_rewrite IdentMap.map_add.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. setoid_rewrite IdentMap.Properties.F.map_o.
          rewrite IdentMap.gss, TID. done.
        + by rewrite IdentMap.gso.
      - admit.
      - admit.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. by rewrite !IdentMap.gss.
        + by rewrite !IdentMap.gso.
      - admit.
      - admit.
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
Admitted.

Lemma rtc_pi_step_future
      cST1 cST2 withprm
      (WF1: pi_wf cST1)
      (STEPS: rtc (pi_step_all withprm) cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  revert WF1. induction STEPS; i.
  - splits; auto; econs.
  - inv H. exploit pi_step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    splits; auto; etrans; eauto.
Qed.

Lemma pi_step_evt_all_incl
      withprm tid cST1 cST2
      (STEP: pi_step_evt withprm tid cST1 cST2):
  pi_step_all withprm cST1 cST2.
Proof.
  econs; eauto.
Qed.

Lemma pi_step_except_all_incl
      tid cST1 cST2
      (STEP: pi_step_except tid cST1 cST2):
  pi_step_all true cST1 cST2.
Proof.
  inv STEP; econs; eauto.
Qed.

Lemma pi_local_wf_prm_oth_iff
      tid cST prm_oth1 prm_oth2
      (WF: pi_local_wf tid prm_oth1 cST)
      (IFF: forall loc ts, prm_oth1 loc ts <-> prm_oth2 loc ts):
  pi_local_wf tid prm_oth2 cST.
Proof.
  inv WF. econs; eauto.
  - i. exploit LR; eauto.
    i. des. esplits; eauto. 
    intro X. apply IFF in X. eauto.
  - i. eapply RL; eauto.
    intro X. apply IFF in X. eauto.
  - i. exploit PRM; eauto.
    apply IFF in PROTH. eauto.
Qed.

Lemma pi_steps_small_steps_fst
      tid cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  rtc (small_step_evt withprm' tid) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. 
  destruct (ThreadEvent_is_promising e).
  - subst. eauto.
  - econs; eauto. s. inv STEPS. destruct withprm'; econs; eauto 10. 
Qed.

Lemma pi_steps_small_steps_snd
      tid cST1 cST2 withprm
      (PI_STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  rtc (small_step_evt withprm tid) (snd cST1) (snd cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. econs; eauto.
Qed.

Lemma pi_steps_small_steps_snd_with_pre
      tid cST1 cST2 pre withprm
      (PI_STEPS: with_pre (pi_step withprm tid) cST1 pre cST2):
  with_pre (small_step withprm tid) (snd cST1) (pi_pre_proj pre) (snd cST2).
Proof.
  ginduction PI_STEPS; s; i; subst; eauto.
  des. inv PSTEP. eauto.
Qed.

Lemma pi_steps_all_pf_steps_fst
      cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (pi_step_all withprm) cST1 cST2):
  rtc (small_step_all withprm') (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. inv USTEP0. 
  destruct (ThreadEvent_is_promising e0) eqn: PROM.
  - subst. eauto.
  - econs; eauto. s. inv STEPS. destruct withprm'; econs; eauto 10. 
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3):
  forall loc from to val ord rel tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, val, rel, ord) \/
         ThreadEvent.is_writing e = Some (loc, from, to, val, rel, ord)),
  ~Threads.is_promised tid' loc ts cST2.(snd).(Configuration.threads).
Proof.
  ii. inv H.
  inv PI_CONSISTENT. ss.
  guardH RW. destruct cST2 as [cS2 cT2].
  exploit CONSIS.
  { eapply rtc_implies, PI_STEPS. i. econs; eauto. }
  { eauto. }
  { eauto. }
  clear CONSIS. i. des.
  exploit (PI_RACEFREE cS3 ord ord0).
  { etrans. 
    - eapply rtc_implies; [by i; eapply step_evt_intro, PR|].
      by eapply pi_steps_small_steps_fst in PI_STEPS; eauto.
    - eapply rtc_implies, STEPS. by econs; eauto.
  }
  { ss. inv STEP. inv STEP0; [by inv STEP; inv RW; inv H|].
    exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply (@pi_step_evt_all_incl true)|]|]; eauto.
    i; des. clear FUTURES FUTURET.
    assert (LC1: exists lc1', IdentMap.find tid (Configuration.threads cS3) = Some (existT _ lang0 st1, lc1')).
    { eexists. erewrite <-(@rtc_small_step_find _ _ cS2); eauto.
      destruct cS2. inv WF2. ss. subst.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID0. }

    des. inv STEP; inv RW; inv H
    ; econs; eauto; first [by econs 1; ss|by econs 2; ss].
  }
  i. des. destruct ord0; inv ORD; inv ORDW.
Qed.

Lemma pi_consistent_small_step_pi
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (FULFILL: promise_consistent tid cT3):
  exists cS3, pi_step withprm tid e cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT PI_RACEFREE PI_STEPS STEP).
  exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
  i; des. destruct cS2. inv WF2. ss. assert (MSTEP:=STEP). inv STEP. inv STEP0.
  - eexists. econs; [by eauto|by inv STEP; s; eauto|..].
    + inv STEP. ss. rewrite IdentMap.gss.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID.
    + i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
  - inv STEP.
    { eexists. econs.
      - eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 1; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 2; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 2; eauto.
          econs; eauto.
          s. eapply RL; eauto.
          i. destruct (Ident.eq_dec tid tid0) eqn: EQ.
          * subst. intro PROMISED. inv PROMISED.
            ss. rewrite TID0 in TID. depdes TID.
            rdes FULFILL. ss. rewrite IdentMap.gss in FULFILL.
            exploit FULFILL; s; eauto.
            intro LT. ss.
            inv READABLE; eauto.
            admit. (* with LT *)
          * eapply RW; s; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { inv LOCAL. inv WRITE. eexists. econs.
      - econs; eauto. econs 2. econs 3; eauto. econs; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 3; eauto.
          ss. admit.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { admit.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 5; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 5; eauto.
          econs; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 6; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 6; eauto.
          econs; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
Admitted. (* Mostly done *)

Lemma fulfill_unset_promises
      loc from ts val rel
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts val rel promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ m.(Message.val) = val /\ Capability.le rel m.(Message.released).
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. erewrite Memory.remove_get0 in TH1; eauto. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma thread_step_unset_promises
      lang loc e from ts msg (th1 th2:Thread.t lang)
      (STEP: Thread.step e th1 th2)
      (TH1: Memory.get loc ts th1.(Thread.local).(Local.promises) = Some (from, msg))
      (TH2: Memory.get loc ts th2.(Thread.local).(Local.promises) = None):
  exists ord from val rel,
  <<EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)>> /\
  <<ORD: Ordering.le ord Ordering.relaxed>> /\
  <<TIME: Time.lt (th1.(Thread.local).(Local.commit).(Commit.cur).(Capability.rw) loc) ts>>.
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. destruct msg. ss. 
    exploit Memory.promise_promises_get1; eauto. i. des. congr.
  }
  destruct msg.
  inv STEP0; ss; try by inv LOCAL; ss; congr.
  - by rewrite TH1 in TH2.
  - inv LOCAL. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. eauto.
  - inv LOCAL1. inv LOCAL2. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. inv READABLE. ss. move TS at bottom.
      eapply TimeFacts.le_lt_lt; eauto.
      repeat (etrans; [|apply Time.join_l]). refl.
Qed.

Lemma rtc_small_step_unset_promises
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg withprm
      (STEPS: rtc (small_step_evt withprm tid) c1 c2)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  Time.lt (lc1.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2.
  }
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) as [[t m]|] eqn: PRM.
  - rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intro LT. move STEP at bottom.
    eapply TimeFacts.le_lt_lt; eauto.
    admit. (* with STEP0 *)
  - eapply thread_step_unset_promises in STEP; eauto.
Admitted.

Lemma promise_consistent_small_step
      tid c1 c2 withprm
      (STEP: small_step_evt withprm tid c1 c2)
      (FULFILL: promise_consistent tid c2):
  promise_consistent tid c1.
Proof.
  ii. destruct (IdentMap.find tid (Configuration.threads c2)) as [[lang2 lc2]|] eqn: THREAD2; cycle 1.
  { inv STEP. inv USTEP. ss. by rewrite IdentMap.gss in THREAD2. }
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from2 msg2]|] eqn: PROMISE2; cycle 1.
  - apply Operators_Properties.clos_rt1n_step in STEP.
    eauto using rtc_small_step_unset_promises.
  - eapply FULFILL in PROMISE2; eauto.
    eapply TimeFacts.le_lt_lt; eauto.
    admit. (* trivial *)
Admitted.

Lemma promise_consistent_rtc_small_step
      tid c1 c2 withprm
      (STEP: rtc (small_step_evt withprm tid) c1 c2)
      (FULFILL: promise_consistent tid c2):
  promise_consistent tid c1.
Proof.
  ginduction STEP; eauto using promise_consistent_small_step.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      cT3 pre
      (STEP: with_pre (small_step withprm tid) cST2.(snd) pre cT3)
      (FULFILL: promise_consistent tid cT3):
  exists cS3 pre', with_pre (pi_step withprm tid) cST2 pre' (cS3,cT3) /\ 
                   pre = pi_pre_proj pre'.
Proof.
  destruct cST2 as [cS2 cT2].
  revert_until STEP. induction STEP.
  { s; i. eauto. }
  s; i. assert (FULFILL1 := FULFILL).
  eapply promise_consistent_small_step in FULFILL1; eauto. 
  exploit IHSTEP; s; eauto.
  intro STEPS. des. ss.
  eapply (@pi_consistent_small_step_pi _ _ _ (_,_)) in PSTEP; eauto; cycle 1.
  { etrans; eauto. subst. eapply with_pre_rtc_step_union; eauto. 
    eapply with_pre_implies, STEPS.
    i. inv STEP0. inv STEPT. eauto. }
  des. esplits; eauto.
Qed.

Lemma consistent_promise_consistent
      tid c 
      (WF: Configuration.wf c)
      (CONSISTENT: Configuration.consistent c):
  promise_consistent tid c.
Proof.
  ii. inv WF. inv WF0. destruct lst as [lang st].
  exploit CONSISTENT; eauto; try reflexivity.
  i; des. destruct e2.
  exploit rtc_thread_step_rtc_small_step; [eauto|..].
  { ss. eapply rtc_implies, STEPS. i; inv PR; eauto. }
  intro STEPS2. 
  eapply rtc_small_step_unset_promises in STEPS2; eauto.
  - s. rewrite IdentMap.gss. eauto.
  - ss. rewrite PROMISES. apply Cell.bot_get.
Qed.

Theorem pi_consistent_step_pi
      cST1 cT2 e tid
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (STEP: Configuration.step e tid cST1.(snd) cT2):
  exists cS2, rtc (pi_step_evt true tid) cST1 (cS2,cT2).
Proof.
  exploit step_small_steps; eauto; [by inv WF|].
  i. des.
  eapply rtc_step_union_with_pre in STEPS. des.
  exploit pi_consistent_rtc_small_step_pi; eauto.
  { eapply consistent_promise_consistent; eauto. }
  i; des. eexists. eapply with_pre_rtc_step_union. eauto.
Qed.
































Inductive can_fulfill (tid: Ident.t) loc ts (c1 c4: Configuration.t) : Prop :=
| can_fulfill_intro
    c2 c3 e ord lst2 lc2 from2 msg2 from val rel 
    (STEPS: rtc (small_step_evt false tid) c1 c2)
    (STEP: small_step false tid e c2 c3)
    (THREAD: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from2, msg2))
    (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
    (ORD: Ordering.le ord Ordering.relaxed)
    (STEPS: rtc (small_step_evt false tid) c3 c4):
  can_fulfill tid loc ts c1 c4
.

Inductive can_fulfill_promises (tid: Ident.t) : Configuration.t -> Prop :=
| can_fulfill_promises_step
    c1
    (FULFILL: forall lst1 lc1 loc ts from msg
                (THREAD: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
                (PROMISE: Memory.get loc ts lc1.(Local.promises) = Some (from, msg)),
              exists c2,
              <<FULFILL1: can_fulfill tid loc ts c1 c2>> /\
              <<FULFILL2: can_fulfill_promises tid c2>>):
  can_fulfill_promises tid c1
.
Hint Constructors can_fulfill_promises.

Lemma rtc_small_step_fulfill
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg 
      (STEPS: rtc (small_step_evt false tid) c1 c2)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  can_fulfill tid loc ts c1 c2.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2. 
  }
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) eqn: PRM.
  - destruct p as [t m].
    rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intros []; i.
    econs; swap 5 8; eauto.
    etrans; [|apply STEPS0].
    econs; eauto 10.  
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto 10. 
Qed.

Lemma can_fulfill_lt
      tid loc ts c1 c3 lst1 lc1 from msg
      (FULFILL: can_fulfill tid loc ts c1 c3)
      (FIND: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (PROMISE: Memory.get loc ts lc1.(Local.promises) = Some (from, msg)):
  Time.lt (lc1.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
  destruct FULFILL.
  inv STEP.
  eapply rtc_implies, rtc_small_step_commit_future in STEPS; eauto; cycle 1.
  inv STEP0; inv STEP; inv EVENT.
  + inv LOCAL. inv WRITABLE.
    move STEPS at bottom. move TS at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply STEPS.
  + inv LOCAL1. inv READABLE. inv LOCAL2. inv WRITABLE.
    ss. move STEPS at bottom. move TS at bottom.
    eapply TimeFacts.le_lt_lt; eauto.
    repeat (etrans; [|apply Time.join_l]). apply STEPS.
Qed.

Lemma rtc_small_step_unset_fulfill
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg 
      (STEPS: rtc (small_step_evt false tid) c1 c2)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  can_fulfill tid loc ts c1 c2.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2. 
  }
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) eqn: PRM.
  - destruct p as [t m].
    rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intros []; i.
    econs; swap 5 8; eauto.
    etrans; [|apply STEPS0].
    econs; eauto 10.
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto. 
Qed.

Lemma consistent_can_fulfill_promises_future
      tid c 
      (CONSISTENT: Configuration.consistent c)
      sc1 mem1 lst lc
      (TH1: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc))
      (FUTURE: Memory.future c.(Configuration.memory) mem1)
      (TIMELE: TimeMap.le c.(Configuration.sc) sc1)
      (LOCWF: Local.wf lc mem1)
      (SC: Memory.closed_timemap sc1 mem1)
      (MEM: Memory.closed mem1):
  can_fulfill_promises tid (Configuration.mk c.(Configuration.threads) sc1 mem1).
Proof.
  admit.
  (* ii. destruct lst as [lang st]. econs. i. *)
  (* exploit CONSISTENT; ss; eauto. *)
  (* i; des. destruct e2. *)
  (* exploit rtc_thread_step_rtc_small_step; swap 1 2. *)
  (* { eapply rtc_implies, STEPS. i. inv PR. eauto. } *)
  (* { eauto. } *)
  (* intro STEPS1. ss. *)
  (* match goal with [STEPS1: rtc _ _ ?cfg|-_] => set (c2 := cfg) end. *)
  (* exploit (@rtc_small_step_unset_fulfill tid loc ts (Configuration.mk c.(Configuration.threads) sc1 mem1)); cycle 1. *)
  (* - apply THREAD. *)
  (* - apply PROMISE. *)
  (* - instantiate (3:=c2). s. rewrite IdentMap.gss. eauto. *)
  (* - rewrite PROMISES. apply Cell.bot_get. *)
  (* - intro FULFILL. exists c2; split; eauto. *)
  (*   econs; i. unfold c2 in *. ss. *)
  (*   rewrite IdentMap.gss in THREAD0. depdes THREAD0. *)
  (*   rewrite PROMISES in PROMISE0.  *)
  (*   by setoid_rewrite Cell.bot_get in PROMISE0. *)
  (* - done. *)
Admitted.

Lemma can_fulfill_promises_promise_consistent
      tid c
      (FULFILL: can_fulfill_promises tid c):
  promise_consistent tid c.
Proof.
  ii. inv FULFILL. exploit FULFILL0; eauto.
  i; des.
  eauto using can_fulfill_lt.
Qed.






























Definition TimeMap_lift (x: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec x y then Time.join (tm y) t else tm y.

Definition Capability_lift (x: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift x t rw) (TimeMap_lift x t sc)
  end.

Definition pi_step_lift_mem l t e M1 M2 : Prop :=
  match ThreadEvent.is_writing e with
  | Some (loc,from,to,val,rel,ord) =>
    exists pm1 pm2 kind,
      <<PMREL: Memory.write pm1 M1 loc from to val (if Loc.eq_dec l loc then rel else Capability_lift l t rel) pm2 M2 kind>>
  | None =>
    M1 = M2
  end.

Inductive pi_step_lift (l: Loc.t) (t: Time.t) : Ident.t -> ThreadEvent.t -> Configuration.t*Configuration.t*Memory.t ->  Configuration.t*Configuration.t*Memory.t -> Prop :=
| pi_step_lift_intro tid e cS1 cS2 cT1 cT2 M1 M2
    (PI_STEP: pi_step true tid e (cS1,cT1) (cS2,cT2))
    (MEM: pi_step_lift_mem l t e M1 M2):
  pi_step_lift l t tid e (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift.

Definition pi_step_lift_evt l t tid cSTM1 cSTM2 : Prop :=
  step_union (pi_step_lift l t tid) cSTM1 cSTM2.
Hint Unfold pi_step_lift_evt.

Inductive pi_step_lift_except x t (tid_except:Ident.t) cSTM1 cSTM2: Prop :=
| pi_step_lift_except_intro tid
    (PI_STEP: pi_step_lift_evt x t tid cSTM1 cSTM2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_lift_except.

Definition mem_sub (cmp: Capability.t -> Capability.t -> Prop) (m1 m2: Memory.t) : Prop :=
  forall loc ts from val rel1
    (IN: Memory.get loc ts m1 = Some (from, Message.mk val rel1)),
  exists rel2,
  <<IN: Memory.get loc ts m2 = Some (from, Message.mk val rel2)>> /\
  <<CMP: cmp rel1 rel2>>.

Definition mem_eqlerel (m1 m2: Memory.t) : Prop :=
  <<LR: mem_sub Capability.le m1 m2>> /\
  <<RL: mem_sub (fun x y => Capability.le y x) m2 m1>>.

Inductive mem_eqlerel_lift loc ts e (m1 m2: Memory.t) : Prop :=
| mem_le_lift_intro m1'
  (MEMEQ: mem_eqlerel m1 m1')
  (MEMWR: pi_step_lift_mem loc ts e m1' m2)
.

Definition conf_update_global (c: Configuration.t) sc (m: Memory.t) : Configuration.t :=
  Configuration.mk c.(Configuration.threads) sc m.

Inductive promises_aux tid cS cT loc ts : Prop :=
| promises_aux_intro
    (IN: exists from msg, Memory.get loc ts cT.(Configuration.memory) = Some(from,msg))
    (NOSRC: Memory.get loc ts cS.(Configuration.memory) = None)
    (NOPRM: ~Threads.is_promised tid loc ts cT.(Configuration.threads))
.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 x t tid
      (STEPS: rtc (pi_step_lift_except x t tid) cSTM1 cSTM2):
  rtc (pi_step_except tid) cSTM1.(fst) cSTM2.(fst).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. inv PI_STEP. inv USTEP.
  econs; eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 x t
      (PI_STEPS: rtc (pi_step_except tid) cST1 cST2):
  exists M2, rtc (pi_step_lift_except x t tid) (cST1,cST1.(snd).(Configuration.memory)) (cST2,M2).
Proof.
Admitted.

Lemma pi_step_lift_except_future
      x t tid cS1 cT1 cSTM2 lst1 lc1
      (PI_STEPS: rtc (pi_step_lift_except x t tid) (cS1,cT1,cT1.(Configuration.memory)) cSTM2)
      (WF: pi_wf (cS1,cT1))
      (FIND: IdentMap.find tid cT1.(Configuration.threads) = Some (lst1,lc1)):
  <<MEMFUT: Memory.future cT1.(Configuration.memory) cSTM2.(snd)>> /\
  <<TIMELE: TimeMap.le cT1.(Configuration.sc) cSTM2.(fst).(snd).(Configuration.sc)>> /\
  <<LOCWF: Local.wf lc1 cSTM2.(snd)>> /\
  <<MEMCLOTM: Memory.closed_timemap (cSTM2.(fst).(snd).(Configuration.sc)) cSTM2.(snd)>> /\
  <<MEMCLO: Memory.closed cSTM2.(snd)>>.
Proof.
Admitted.

Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid loc ts
      (STEPS: rtc (pi_step_lift_except loc ts tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(fst).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(fst).(Configuration.threads) /\
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads).
Proof.
  (* ginduction STEPS; eauto. *)
  (* des. rewrite <-IHSTEPS, <-IHSTEPS0. *)
  (* inv H. inv PI_STEP. inv PI_STEP0. inv PI_STEP. *)
  (* ss; split; [by eapply small_step_find; eauto|]. *)
  admit.
Admitted.

Lemma rtc_pi_step_except_local_wf
      loc ts tid cS1 cT1 cSTM2
      (WF: pi_wf (cS1,cT1))
      (STEPS_LIFT : rtc (pi_step_lift_except loc ts tid) (cS1, cT1, cT1.(Configuration.memory)) cSTM2):
  pi_local_wf tid (promises_aux tid cSTM2.(fst).(fst) (conf_update_global cT1 cSTM2.(fst).(snd).(Configuration.sc) cSTM2.(snd)))
                  (cSTM2.(fst).(fst), conf_update_global cT1 cSTM2.(fst).(snd).(Configuration.sc) cSTM2.(snd)).
Proof.
(*
  destruct cSTM2 as [[cS2 cT2] M2]. ss.

  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEPS_LIFT.
  induction STEPS_LIFT.
  { assert (WF2 := pi_wf_pi_local_wf tid WF).
    destruct cS1, cT1. ss.
    eapply pi_local_wf_prm_oth_iff; eauto.
    clear WF2. inv WF. inv WFT. split; intro PR.
    - inv PR. ss. subst. econs; s.
      + inv WF. inv PRM. exploit THREADS; eauto.
        intro LOCAL. inv LOCAL.
        apply PROMISES0 in PROMISES. eauto.
      + destruct (Memory.get loc0 ts0 memory) as [[from msg]|] eqn: EQ; eauto.
        exfalso. exploit LR; eauto.
        i. des. eapply NOT; eauto.
      + intro PRM2. inv WF. inv PRM. inv PRM2.
        exploit DISJOINT; eauto.
        intro DISJ.
        admit. (* with DISJ, PROMISES, PROMISES0 *)
    - inv PR. des. ss. subst.
      assert (NA: ~ forall tid, ~ Threads.is_promised tid loc0 ts0 threads0).
      { intro NPRM. exploit RL; eauto. 
        intro X. by rewrite X in NOSRC. }
      eapply not_all_not_ex in NA. destruct NA as [tid0 NA].
      destruct (Ident.eq_dec tid0 tid) eqn: EQ.
      { subst. exfalso. eauto. }
      econs; eauto.
  }
  apply Operators_Properties.clos_rt_rtn1_iff,
        Operators_Properties.clos_rt_rt1n_iff in STEPS_LIFT.

  destruct y as [[cS2 cT2] M2].
  destruct z as [[cS3 cT3] M3]. ss.
  


  rdes IHSTEPS_LIFT. r; ss.
  exploit rtc_pi_step_lift_except_find.
  { econs 2; eauto. }
  intro EQ; des. rewrite <-EQ.

  inv H. inv PI_STEP. inv PI_STEP0. ss.

  assert(WF2: pi_wf (cS2,cT2)).
  { eapply rtc_pi_step_future; eauto.
    etrans.
    - apply pi_steps_lift_except_pi_steps in STEPS_LIFT.
      eapply rtc_implies, STEPS_LIFT.
      i. inv PR. eauto.
    - s. econs 2; eauto. }

  inv WF2.
  esplits; eauto.
  i. admit.
*)
Admitted.

Lemma pi_step_lift_mem_get
      l t e m1 m1' m2 m2' loc ts from1 msg2 from2' msg2'
      (LIFT1: pi_step_lift_mem l t e m1 m1')
      (LIFT2: pi_step_lift_mem l t e m2 m2')
      (IN1: Memory.get loc ts m1 = Some (from1, msg2))
      (IN2: Memory.get loc ts m2' = Some (from2', msg2')):
  exists from2 msg2,
  Memory.get loc ts m2 = Some (from2, msg2).
Proof.
Admitted.









































































Lemma local_simul_fence
      com prm prm' sc ordr ordw com' sc'
      (LOCAL: Local.fence_step (Local.mk com prm) sc ordr ordw (Local.mk com' prm') sc'):
  Local.fence_step (Local.mk com Memory.bot) sc ordr ordw (Local.mk com' Memory.bot) sc'.
Proof.
  inv LOCAL. econs; eauto.
Qed.

Lemma local_simul_write
      com com' sc sc' mS mT mT' loc from to val relr relw ord kind prm prm'
      (SUB: mem_sub eq mS mT)
      (WRITE: Local.write_step (Local.mk com prm) sc mT loc from to val relr relw ord (Local.mk com' prm') sc' mT' kind):
  exists mS',
  Local.write_step (Local.mk com Memory.bot) sc mS loc from to val relr relw ord (Local.mk com' Memory.bot) sc' mS' kind.
Proof.
Admitted.

Lemma lift_fence
      sc1 sc2 sc2' com1 com2 com2' prm prm' ordr ordw
      (LOCAL: Local.fence_step (Local.mk com2 prm) sc2 ordr ordw (Local.mk com2' prm') sc2')
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2):
  exists com1' sc1',
  <<LOCAL: Local.fence_step (Local.mk com1 prm) sc1 ordr ordw (Local.mk com1' prm') sc1'>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>>.
Proof.
Admitted.

Lemma lift_write
      com1 com2 com2' sc1 sc2 sc2' m1 m2 m2' prm prm' loc ts e loc' from to val relr1 relr2 relw2 ord kind
      (LOCAL: Local.write_step (Local.mk com2 prm) sc2 m2 loc' from to val relr2 relw2 ord (Local.mk com2' prm') sc2' m2' kind)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2)
      (REL: Capability.le relr1 relr2)
      (MEMLE: mem_eqlerel_lift loc ts e m1 m2):
  exists com1' sc1' m1' relw1,
  <<LOCAL: Local.write_step (Local.mk com1 prm) sc1 m1 loc' from to val relr1 relw1 ord (Local.mk com1' prm') sc1' m1' kind>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>> /\
  <<MEMLE: mem_eqlerel_lift loc ts e m1' m2'>>.
Proof.
Admitted.

Lemma lift_read
      com1 com2 com2' m1 m2 prm prm' loc ts e loc' to val rel2 ordr
      (LOCAL: Local.read_step (Local.mk com2 prm) m2 loc' to val rel2 ordr (Local.mk com2' prm'))
      (CoMLE: Commit.le com1 com2)
      (MEMLE: mem_eqlerel_lift loc ts e m1 m2):
  (exists from ordw,
   <<EVENT: ThreadEvent.is_writing e = Some (loc', from, to, val, rel2, ordw)>>)
  \/
  (exists com1' rel1,
   <<LOCAL: Local.read_step (Local.mk com1 prm) m1 loc' to val rel1 ordr (Local.mk com1' prm')>> /\
   <<CoMLE: Commit.le com1' com2'>>).
Proof.
Admitted.

Inductive thread_event_eqlerel: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| teel_promise loc from to val rel1 rel2
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.promise loc from to val rel1) (ThreadEvent.promise loc from to val rel2) 
| teel_silent:
  thread_event_eqlerel (ThreadEvent.silent) (ThreadEvent.silent)
| teel_read loc ts val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.read loc ts val rel1 ord) (ThreadEvent.read loc ts val rel2 ord)
| teel_write loc from to val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.write loc from to val rel1 ord) (ThreadEvent.write loc from to val rel2 ord)
| teel_update loc tsr tsw valr valw relr1 relr2 relw1 relw2 ordr ordw
    (LEREL: Capability.le relr1 relr2)
    (LEREL: Capability.le relw1 relw2):
  thread_event_eqlerel (ThreadEvent.update loc tsr tsw valr valw relr1 relw1 ordr ordw) (ThreadEvent.update loc tsr tsw valr valw relr2 relw2 ordr ordw)
| teel_fence ordr ordw:
  thread_event_eqlerel (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
| teel_syscall e:
  thread_event_eqlerel (ThreadEvent.syscall e) (ThreadEvent.syscall e)
.

Lemma lift_step
      lang (thS1 thT1 thT2: @Thread.t lang) eT l t e
      (STEP: Thread.step eT thT1 thT2)
      (NOPRM: ThreadEvent_is_promising eT = None)
      (ST: thS1.(Thread.state) = thT1.(Thread.state))
      (COM: Commit.le thS1.(Thread.local).(Local.commit) thT1.(Thread.local).(Local.commit))
      (PRM: thS1.(Thread.local).(Local.promises) = thT1.(Thread.local).(Local.promises))
      (SC: TimeMap.le thS1.(Thread.sc) thT1.(Thread.sc))
      (MEM: mem_eqlerel_lift l t e thS1.(Thread.memory) thT1.(Thread.memory))
: 
  (exists loc ts from val relr relw ordr ordw,
   <<EVTR: ThreadEvent.is_reading eT = Some (loc, ts, val, relr, ordr)>> /\
   <<EVTW: ThreadEvent.is_writing e = Some (loc, from, ts, val, relw, ordw)>>)
  \/
  (exists eS thS2,
   <<EVT: thread_event_eqlerel eS eT>> /\
   <<STEP: Thread.step eS thS1 thS2>> /\
   <<ST: thS2.(Thread.state) = thT2.(Thread.state)>> /\
   <<COM: Commit.le thS2.(Thread.local).(Local.commit) thT2.(Thread.local).(Local.commit)>> /\
   <<PRM: thS2.(Thread.local).(Local.promises) = thT2.(Thread.local).(Local.promises)>> /\
   <<SC: TimeMap.le thS2.(Thread.sc) thT2.(Thread.sc)>> /\
   <<MEM: mem_eqlerel_lift l t e thS2.(Thread.memory) thT2.(Thread.memory)>>).
Proof.
Admitted.




















Lemma key_lemma
      cS1 cT1 cS2 cT2 tid
      (PI_CONSISTENT : pi_consistent (cS1, cT1))
      (WF : pi_wf (cS1, cT1))
      (RACEFREE : pf_racefree cS1)
      (STEPS : rtc (pi_step_evt true tid) (cS1, cT1) (cS2, cT2))
      loc ts 
      lst2 lc2 from2 msg2 
      (THREAD2 : IdentMap.find tid (Configuration.threads cT2) = Some (lst2, lc2))
      (PROMISE2 : Memory.get loc ts (Local.promises lc2) = Some (from2, msg2))
      cSTM3
      (STEPS_LIFT : rtc (pi_step_lift_except loc ts tid) (cS2, cT2, cT2.(Configuration.memory)) cSTM3)
      cM4 pre
      (PI_STEPS : with_pre (small_step false tid) (conf_update_global cT2 cSTM3.(fst).(snd).(Configuration.sc) cSTM3.(snd)) pre cM4)
      (PRCONSIS: promise_consistent tid cM4)
      lst4 lc4
      (THREAD4 : IdentMap.find tid (Configuration.threads cM4) = Some (lst4, lc4))
      (TIMELT: Time.lt (lc4.(Local.commit).(Commit.cur).(Capability.rw) loc) ts)
  : 
  exists cS4 pre',
  <<STEPS: with_pre (pi_step false tid) (cSTM3.(fst).(fst), conf_update_global cT2 cSTM3.(fst).(snd).(Configuration.sc) cSTM3.(snd)) pre' (cS4, cM4)>>
  /\
  <<EQPRE: pre = pi_pre_proj pre'>>.
Proof.
  assert (WF2: pi_wf (cS2,cT2)).
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, STEPS; eauto. }
  move WF2 after cSTM3.

  revert_until STEPS_LIFT.
  apply Operators_Properties.clos_rt_rt1n_iff, 
        Operators_Properties.clos_rt_rtn1_iff in STEPS_LIFT.
  induction STEPS_LIFT.
  { s. i. destruct cT2. unfold conf_update_global in *. ss.
    eapply with_pre_implies in PI_STEPS.
    - exploit pi_consistent_rtc_small_step_pi; try eapply WF; eauto.
    - i. inv STEP. eauto. }

  apply Operators_Properties.clos_rt_rtn1_iff, 
        Operators_Properties.clos_rt_rt1n_iff in STEPS_LIFT.

  destruct y as [[cS3 cT3] M3].
  destruct z as [[cS4 cT4] M4].
  rename H into PSTEP.

  assert (WF3: pi_wf (cS3, cT3)).
  { eapply rtc_pi_step_future; eauto.
    eapply pi_steps_lift_except_pi_steps in STEPS_LIFT.
    eapply rtc_implies, STEPS_LIFT.
    i. inv PR. eauto. }

  assert (WF4: pi_wf (cS4, cT4)).
  { inv PSTEP. inv PI_STEP. inv USTEP.
    eapply pi_step_future; eauto. }
  
  s. i. assert (X := PSTEP). inv X. inv PI_STEP. inv USTEP. rename cM4 into cM4'.

  cut ((exists cS3' cM3' lst3' com3' com4' prm3',
       <<STEPS3: rtc (pi_step_evt false tid) (cS3, conf_update_global cT2 (Configuration.sc cT3) M3) (cS3',cM3')>> /\
       <<MEMLE: mem_eqlerel_lift loc ts e cM3'.(Configuration.memory) cM4'.(Configuration.memory)>> /\
       <<SCLE: TimeMap.le cM3'.(Configuration.sc) cM4'.(Configuration.sc)>> /\
       <<THS3: IdentMap.find tid cM3'.(Configuration.threads) = Some (lst3', Local.mk com3' prm3') >> /\
       <<THS4: IdentMap.find tid cM4'.(Configuration.threads) = Some (lst3', Local.mk com4' prm3') >> /\
       <<COMLE: Commit.le com3' com4' >>) /\
       (exists cS4' pre',
       <<STEPS4: with_pre (pi_step false tid) (cS4, conf_update_global cT2 (Configuration.sc cT4) M4) pre' (cS4',cM4')>>/\
       <<EQPRE: pre = pi_pre_proj pre'>>)).
  { i; des. exists cS4'; esplits; eauto. }

  move WF2 after cM4'. move tid0 after cM4'. move TID after cM4'. move e after cM4'. move PI_STEP after cM4'. move MEM after cM4'. move PSTEP after cM4'.
  revert_until PI_STEPS.
  induction PI_STEPS; i.
  { destruct lc4 as [com4 prm4]. subst. ss.
    esplits.
    { eauto. }
    { econs; eauto.
      by split; ii; esplits; eauto; reflexivity. }
    { s. admit. }
    { s. eauto. }
    { s. eauto. }
    { reflexivity. }
    { eauto. }
    { eauto. }
  }

  rename ms into cM4', es into cM5'.

  assert (STEP2 := PSTEP0). inv PSTEP0. ss.
  rewrite IdentMap.gss in THREAD4. depdes THREAD4.

  exploit IHPI_STEPS; eauto using promise_consistent_small_step.
  { eapply TimeFacts.le_lt_lt; eauto. admit. (* with STEP *) }
  i; des. subst. clear IHPI_STEPS.
  rewrite THS4 in TID0. depdes TID0.

  exploit rtc_pi_step_local_wf; swap 1 2.
  { eapply STEPS3. }
  { hexploit rtc_pi_step_except_local_wf; [apply WF2|apply STEPS_LIFT|..]; eauto. }
  intro SEMI_WF3.

  exploit rtc_pi_step_local_wf; swap 1 2.
  { eapply with_pre_rtc_step_union, STEPS4. }
  { hexploit rtc_pi_step_except_local_wf; [by apply WF2|..].
    - etrans; [by apply STEPS_LIFT|].
      econs 2; [|reflexivity]; eauto.
    - eauto. }
  intro SEMI_WF4.

  exploit (@lift_step _ (Thread.mk _ st1 (Local.mk com3' prm3') cM3'.(Configuration.sc) cM3'.(Configuration.memory))); [apply STEP|..]; eauto.
  i; des.

  (* Read the message "e" *)
  { destruct (Loc.eq_dec loc loc0) eqn: NEQ.
    { exfalso. subst. inv PI_STEP.
      destruct lst2.
      eapply NOWR; eauto.
      econs; [|by apply PROMISE2].
      apply rtc_pi_step_lift_except_find in STEPS_LIFT.
      s in STEPS_LIFT. des.
      rewrite <- STEPS_LIFT0. eauto.
    }

    assert (X:= PI_STEP). inv X.
    destruct (ThreadEvent_is_promising e) eqn: EQ.
    { destruct e; inv EQ; inv EVTW. }

    assert (FREE3: pf_racefree cS3').
    { eapply pf_racefree_steps; eauto.
      etrans.
      { eapply rtc_implies, (pi_steps_small_steps_fst _ STEPS); eauto. }
      etrans.
      { eapply (@pi_steps_all_pf_steps_fst (_,_) (_,_)).
        eapply rtc_implies; [by i; eapply pi_step_except_all_incl; eauto|].
        eapply (@pi_steps_lift_except_pi_steps (_,_,_) (_,_,_)), STEPS_LIFT. }
      s. eapply (@pi_steps_all_pf_steps_fst (_,_) (_,_)).
      eapply rtc_implies, STEPS3. eauto.
    }

    exploit small_step_to_program_step_reading; try apply EVTR; eauto.
    i; des. inv EVENT.

    exploit small_step_to_program_step_writing; try apply EVTW; eauto.
    i; des. inv EVENT.

    exploit FREE3.
    { reflexivity. }
    { inv SEMI_WF3. ss.
      econs.
      - intro X. symmetry in X. eauto.
      - econs; [|apply STATE].
        rewrite THS4 in TH. depdes TH.
        by rewrite THS, THS3.
      - econs; [|apply STATE0].
        erewrite <- rtc_small_step_find; swap 1 2.
        + eapply (@pi_steps_small_steps_fst tid (_,_) (_,_)). eauto.
        + s. eauto.
        + eauto.
      - eauto.
    }

    i; des. exfalso.
    inv MEMLE. r in MEMWR. rewrite EVTW in MEMWR. des. rewrite NEQ in PMREL.
    inv STEP; inv STEP0; inv EVTR.
    - move TIMELT at bottom. move LOCAL at bottom. move PMREL at bottom. move ORDR at bottom.
      admit. (* PMREL, TIMELT, LOCAL, ORDR *)
    - move TIMELT at bottom. move LOCAL1 at bottom. move LOCAL2 at bottom. move PMREL at bottom. move ORDR at bottom.
      admit. (* PMREL, TIMELT, LOCAL1, LOCAL2, ORDR *)
  }

  (* Simulation exists *)  
  assert (NOPRMEVT: ThreadEvent_is_promising eS = None).
  { destruct e0; inv PFREE; inv EVT; eauto. }

  subst. destruct thS2 as [stx lcx scx mx]. ss. subst.

  exploit pi_steps_small_steps_snd; try apply STEPS3.
  intros STEPS3'.
  eapply rtc_step_union_with_pre in STEPS3'. des.

  exploit (@IHSTEPS_LIFT (Configuration.mk (IdentMap.add tid (existT _ _ st2, lcx) cM3'.(Configuration.threads)) scx mx)); s; swap 1 3; swap 2 3.
  { rewrite IdentMap.gss. eauto. }
  { eapply with_pre_trans.
    - apply STEPS3'.
    - s; eauto. }
  { ii. r in PRCONSIS. ss. 
    rewrite IdentMap.gss in THREAD. rewrite IdentMap.gss in PRCONSIS.
    inv THREAD. rewrite PRM in PROMISE. 
    exploit PRCONSIS; eauto.
    intro LT. move COM at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply COM.
  }
  { move TIMELT at bottom. move COM at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply COM.
  }
  i; des. ss.
  destruct pre'0; [|done].
  destruct p as [[cS3'x ?] ?]. symmetry in EQPRE. inv EQPRE.

  destruct lcx as [comx prmx].
  destruct lc4 as [com4 prm4].
  split.
  { esplits; [by eapply with_pre_rtc_step_union, STEPS0|..]; eauto.
    { s. rewrite IdentMap.gss. eauto. }
    { ss. rewrite IdentMap.gss, PRM. eauto. }
  }

  rename e0 into evt.
  inv STEP; inv STEP1.

  (* Promise step *)
  by inv PFREE.

  (* Silent step *)
  { esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - eauto.
      - inv SEMI_WF4; ss.
        econs; [by rewrite THS, THS4|..]; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. done.
    }
    eauto.
  }

  (* Read step *)
  { inv STEP2. inv SEMI_WF4. inv STEP; inv STEP1.
    rewrite THS4 in TID0. depdes TID0.
    eapply (f_equal (IdentMap.find tid)) in THS2.
    rewrite !IdentMap.gss in THS2. depdes THS2.

    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - eauto.
      - s. econs; eauto.
        { s. by rewrite THS, THS4. }
        s. econs 2. econs 2; [eauto|].
        
        inv LOCAL0. s.
        eapply Local.step_read; cycle 1; eauto.
        
        inv STEPS0.
        hexploit rtc_pi_step_local_wf.
        { eapply rtc_pi_step_except_local_wf, STEPS_LIFT. eauto. }
        { s. eapply with_pre_rtc_step_union, PSTEPS. }
        s; intro PIWF0. inv PIWF0.

        ss. des. subst. inv EVT. inv PSTEP0. inv STEPS0. inv STEP; inv STEP1. inv LOCAL0. ss.
        exploit LR0; eauto. i; des.

        eapply RL; eauto.
        { intro PRM4. apply NOTPRSELF. inv PRM4.
          rewrite THS4 in TID1. depdes TID1.
          econs; [rewrite THS3|]; eauto.
        }
        { intro PRM4. apply NOTPROTH.
          inv PRM4. des. econs.
          - ss. inv MEMLE. apply MEMEQ in IN. des.
            eapply pi_step_lift_mem_get; eauto.
          - move PI_STEP at bottom.
            admit. (* with PI_STEP, NOSRC *)
          - eauto.
        }
      - s. by rewrite !IdentMap.gss.
      - i. done.
    }
    eauto.
  }

  (* Write step *)
  { hexploit local_simul_write; try apply LOCAL.
    { inv SEMI_WF4. ii. apply LR in IN. des. esplits; eauto. }
    intro WRITE4. des.

    assert (X:= SEMI_WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs; s.
      - econs; eauto.
      - econs; [by rewrite THS, THS4|..]; eauto.
        s. rewrite SC0. econs 2. econs 3; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des. inv WRITE. inv STEPS0. inv PSTEP0. inv EVT.
        hexploit NOWR; s; eauto.
        intros X PRM. apply X.
        inv PRM. econs; eauto.
        rewrite <- TID0.
        apply with_pre_rtc_step_union in PI_STEPS.
        apply pi_steps_small_steps_snd_with_pre in PSTEPS.
        apply with_pre_rtc_step_union in PSTEPS.
        erewrite <- (rtc_small_step_find PI_STEPS); eauto.
        erewrite <- (rtc_small_step_find PSTEPS); eauto.
    }
    eauto.
  }

  (* Update step *)
  { assert (X:= LOCAL1). inv X. ss.

    hexploit local_simul_write; try apply LOCAL2. 
    { inv SEMI_WF4. ii. apply LR in IN. des. esplits; eauto. }
    intro WRITE4. des.
    
    inv STEP2. inv SEMI_WF4. inv STEP; inv STEP1.
    rewrite THS4 in TID0. depdes TID0.
    eapply (f_equal (IdentMap.find tid)) in THS2.
    rewrite !IdentMap.gss in THS2. depdes THS2.

    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      { eauto. }
      { s. econs; eauto.
        { s. by rewrite THS, THS4. }
        s. econs 2. econs 4; [eauto|..].
        { inv LOCAL0. s.
          eapply Local.step_read; cycle 1; eauto.
          
          inv STEPS0.
          hexploit rtc_pi_step_local_wf.
          { eapply rtc_pi_step_except_local_wf, STEPS_LIFT. eauto. }
          { s. eapply with_pre_rtc_step_union, PSTEPS. }
          s; intro PIWF0. inv PIWF0.

          ss. des. subst. inv EVT. inv PSTEP0. inv STEPS0. inv STEP; inv STEP1. inv LOCAL0. ss.
          exploit LR0; eauto. i; des.

          eapply RL; eauto.
          { intro PRM4. apply NOTPRSELF. inv PRM4.
            rewrite THS4 in TID1. depdes TID1.
            econs; [rewrite THS3|]; eauto.
          }
          { intro PRM4. apply NOTPROTH.
            inv PRM4. des. econs.
            - ss. inv MEMLE. apply MEMEQ in IN. des.
              eapply pi_step_lift_mem_get; eauto.
            - move PI_STEP at bottom.
              admit. (* with PI_STEP, NOSRC *)
            - eauto.
          }
        }
        { s. rewrite SC0. eauto. }
      }
      { s. by rewrite !IdentMap.gss. }
      { s. i. des. inv WRITE. inv STEPS0. inv PSTEP0. inv EVT.
        hexploit NOWR; s; eauto.
        intros X PRM'. apply X.
        inv PRM'. econs; eauto.
        rewrite <- TID0.
        apply with_pre_rtc_step_union in PI_STEPS.
        apply pi_steps_small_steps_snd_with_pre in PSTEPS.
        apply with_pre_rtc_step_union in PSTEPS.
        erewrite <- (rtc_small_step_find PI_STEPS); eauto.
        erewrite <- (rtc_small_step_find PSTEPS); eauto. }
    }
    eauto.
  }

  (* Fence step *)
  { assert (X:= SEMI_WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - econs; eauto.
      - econs; [by rewrite THS, THS4|..]; eauto.
        econs 2. econs 5; eauto.
        eapply local_simul_fence.
        s. rewrite SC0. eauto.
      - s. by rewrite !IdentMap.gss.
      - done.
    }
    eauto.
  }

  (* Syscall step *)
  { assert (X:= SEMI_WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - econs; eauto.
      - econs; [by rewrite THS, THS4|..]; eauto.
        econs 2. econs 6; eauto.
        eapply local_simul_fence.
        s. rewrite SC0. eauto.
      - s. by rewrite !IdentMap.gss.
      - done.
    }
    eauto.
  }

Admitted.

Theorem pi_consistent_pi_step_pi_consistent
      cST1 cST2 tid
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (WF: pi_wf cST1)
      (STEP: rtc (pi_step_evt true tid) cST1 cST2)
      (CONSISTENT2: Configuration.consistent cST2.(snd)):
  pi_consistent cST2.
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  econs. i. 
  destruct (Ident.eq_dec tid0 tid); cycle 1.
  { inv PI_CONSISTENT. 
    exploit CONSIS; cycle 1; eauto.
    etrans; cycle 1; eauto.
    eapply rtc_implies, STEP.
    i. econs; eauto.
  }
  subst. rename cS0 into cS3, cT0 into cT3, lst2 into lst3, lc2 into lc3.

  assert (STEPS_LIFT:=pi_step_lifting loc ts STEPS). des.
  rename M2 into M3. ss.

  exploit rtc_pi_step_future; [eauto|..].
  { eapply rtc_implies, STEP. i. inv PR. eauto. }
  i; des. ss. clear FUTURES FUTURET.

  destruct (IdentMap.find tid (Configuration.threads cT2)) eqn: TH; cycle 1.
  { apply Operators_Properties.clos_rt_rt1n_iff in STEP.
    apply Operators_Properties.clos_rt_rtn1_iff in STEP.
    inv STEP.
    - inv PI_CONSISTENT. exploit CONSIS; eauto.
    - inv H. inv USTEP. inv STEPT. ss. by rewrite IdentMap.gss in TH.
  }
  destruct p as [[lang2 st2] lc2].

  exploit pi_step_lift_except_future; eauto.
  i. des. ss.

  exploit rtc_pi_step_lift_except_find; eauto.
  s; intro EQ; des. clear EQ.
  assert (X:= EQ0); rewrite THREAD, TH in X. depdes X.

  hexploit pf_racefree_steps; [eauto|..].
  { eapply pi_steps_small_steps_fst in STEP. eauto. }
  intro RACEFREE.

  exploit consistent_can_fulfill_promises_future; eauto.
  intro X. inv X.

  exploit FULFILL; eauto.
  i; des. inv FULFILL1.

  eapply rtc_step_union_with_pre in STEPS0. des.
  exploit key_lemma; eauto using write_step_lt.
  { apply can_fulfill_promises_promise_consistent in FULFILL2.
    eapply promise_consistent_rtc_small_step, FULFILL2.
    etrans; [|apply STEPS1]. 
    econs 2; [|reflexivity]. eauto. }
  s; i; des.
  
  exploit small_step_to_program_step_writing; eauto.
  i; des.

  apply with_pre_rtc_step_union in STEPS2.
  exists cS4; esplits; eauto using (pi_steps_small_steps_fst false STEPS2).
  
  exploit rtc_pi_step_except_local_wf; eauto.
  s. intro WF3.
  
  exploit rtc_pi_step_local_wf; eauto.
  intro WF4.

  inv WF4. inv EVENT0.
  econs; eauto.
  by rewrite THS, TH0.
Grab Existential Variables. exact false.
Qed.


(* Lemma promise_small_steps *)
(*       c1 c2 c3 tid loc ts withprm *)
(*       lst1 lc1 from1 msg1  *)
(*       (THREAD1 : IdentMap.find tid (Configuration.threads c1) = Some (lst1, lc1)) *)
(*       (PROMISE1 : Memory.get loc ts (Local.promises lc1) = Some (from1, msg1)) *)
(*       lst3 lc3 from3 msg3  *)
(*       (THREAD3 : IdentMap.find tid (Configuration.threads c3) = Some (lst3, lc3)) *)
(*       (PROMISE3 : Memory.get loc ts (Local.promises lc3) = Some (from3, msg3)) *)
(*       (STEPS1: rtc (small_step_evt withprm tid) c1 c2) *)
(*       (STEPS2: rtc (small_step_evt withprm tid) c2 c3): *)
(*   exists lst2 lc2 from2 msg2,  *)
(*   <<THREAD: IdentMap.find tid (Configuration.threads c2) = Some (lst2, lc2)>> /\ *)
(*   <<PROMISE: Memory.get loc ts (Local.promises lc2) = Some (from2, msg2)>>. *)
(* Proof. *)
(* Admitted. *)


(* Lemma rtc_pi_step_lang_match *)
(*       cST1 cST2 tid withprm *)
(*       (MATCH: option_map fst (IdentMap.find tid cST1.(fst).(Configuration.threads)) = *)
(*        option_map fst (IdentMap.find tid cST1.(snd).(Configuration.threads))) *)
(*       (STEPS: rtc (pi_step_evt withprm tid) cST1 cST2): *)
(*   option_map fst (IdentMap.find tid cST2.(fst).(Configuration.threads)) = *)
(*   option_map fst (IdentMap.find tid cST2.(snd).(Configuration.threads)). *)
(* Proof. *)
(*   induction STEPS; eauto. *)
(*   inv H. inv USTEP. eauto. *)
(* Qed. *)



