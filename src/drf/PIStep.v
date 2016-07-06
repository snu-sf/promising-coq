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

Require Import DRFBase.
Require Import SmallStep.
Require Import ReorderThreadStep.
Require Import Race.
Require Import PromiseConsistent.

Set Implicit Arguments.


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

Inductive pi_step_except withprm (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro tid
    (PI_STEP: pi_step_evt withprm tid cST1 cST2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_except.

Definition remove_promise (th: {lang : Language.t & Language.state lang} * Local.t) :=
  (th.(fst), Local.mk th.(snd).(Local.commit) Memory.bot).

Inductive pi_wf cmp: Configuration.t*Configuration.t -> Prop :=
| pi_wf_intro cS cT
    (WFS: Configuration.wf cS)
    (WFT: Configuration.wf cT)
    (THS: cS.(Configuration.threads) = IdentMap.map remove_promise cT.(Configuration.threads))
    (SC: cS.(Configuration.sc) = cT.(Configuration.sc))
    (LR: forall loc ts from val rel1
           (IN: Memory.get loc ts cS.(Configuration.memory) = Some (from, Message.mk val rel1)),
         <<IN: exists rel2, Memory.get loc ts cT.(Configuration.memory) = Some (from, Message.mk val rel2) /\ <<CMP: cmp loc ts rel1 rel2>>>> /\
         <<NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)>>)
    (RL: forall loc ts from val rel2
           (IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, Message.mk val rel2))
           (NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)),
         exists rel1, Memory.get loc ts cS.(Configuration.memory) = Some (from, Message.mk val rel1) /\ <<CMP: cmp loc ts rel1 rel2>>):
  pi_wf cmp (cS,cT)
.
Hint Constructors pi_wf.

Inductive pi_consistent: Configuration.t*Configuration.t -> Prop :=
| pi_consistent_intro cS1 cT1
  (CONSIS:
    forall tid cS2 cT2 lst2 lc2 loc ts from msg
    (STEPS: rtc (pi_step_except false tid) (cS1,cT1) (cS2,cT2))
    (THREAD: IdentMap.find tid cT2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from, msg))
    (PRCONSIS: forall tid0, promise_consistent_th tid0 cT2),
  exists cS3 e ord,
    <<STEPS: rtc (small_step_evt false tid) cS2 cS3>> /\
    <<PROEVT: Configuration_program_event cS3 tid e>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>):
  pi_consistent (cS1, cT1).
Hint Constructors pi_consistent.

Definition pi_pre_proj (pre: option (Configuration.t*Configuration.t*ThreadEvent.t)) := 
  option_map (fun p => (p.(fst).(snd),p.(snd))) pre.

Lemma pi_step_future
      tid cST1 cST2 withprm cmp
      (WF1: pi_wf cmp cST1)
      (REFL: forall l t r, cmp l t r r)
      (STEP: pi_step_evt withprm tid cST1 cST2):
  <<WF2: pi_wf cmp cST2>> /\
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
    assert (STEPS' :=STEPS).

    generalize STEPT. intro STEPT'.
    destruct cS, cT. inv STEPT. inv STEP; inv STEP0; ss.
    { subst. inv LOCAL. econs; eauto.
      - apply IdentMap.eq_leibniz.
        ii. setoid_rewrite IdentMap.map_add.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. setoid_rewrite IdentMap.Properties.F.map_o.
          rewrite IdentMap.gss, TID. done.
        + by rewrite IdentMap.gso.
      - s. i. exploit LR; eauto. i. des. inv PROMISE.
        + erewrite Memory.add_o; eauto. condtac; ss; i.
          * des. subst. exploit Memory.add_get0; eauto. congr.
          * guardH o. esplits; eauto.
            ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac; ss.
            { i. inv TID0. apply inj_pair2 in H1. subst. ss.
              revert PROMISES0. erewrite Memory.add_o; eauto. condtac; ss. i.
              eapply NOT. econs; eauto.
            }
            { i. eapply NOT. econs; eauto. }
        + erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          * des. subst. exploit Memory.split_get0; eauto. i. des. congr.
          * guardH o. des. subst. esplits; eauto.
            { exfalso. eapply NOT. econs; eauto. eapply Memory.split_get0. eauto. }
            ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac; ss.
            { i. inv TID0. apply inj_pair2 in H1. subst. ss.
              revert PROMISES0. erewrite Memory.split_o; eauto. repeat condtac; ss. i. inv PROMISES0.
              eapply NOT. econs; eauto. eapply Memory.split_get0; eauto.
            }
            { i. eapply NOT. econs; eauto. }
          * guardH o. guardH o0. esplits; eauto.
            ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac; ss.
            { i. inv TID0. apply inj_pair2 in H1. subst. ss.
              revert PROMISES0. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
              eapply NOT. econs; eauto.
            }
            { i. eapply NOT. econs; eauto. }
        + erewrite Memory.lower_o; eauto. condtac; ss; i.
          * des. subst. exploit Memory.lower_get0; try exact PROMISES; eauto. i.
            exfalso. eapply NOT. econs; eauto.
          * guardH o. esplits; eauto.
            ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac; ss.
            { i. inv TID0. apply inj_pair2 in H1. subst. ss.
              revert PROMISES0. erewrite Memory.lower_o; eauto. repeat condtac; ss. i.
              eapply NOT. econs; eauto.
            }
            { i. eapply NOT. econs; eauto. }
      - s. i. revert IN. inv PROMISE.
        + erewrite Memory.add_o; eauto. condtac; ss.
          * i. des. inv IN. exfalso. eapply NOT. econs.
            { rewrite IdentMap.gss. eauto. }
            { s. erewrite Memory.add_o; eauto. condtac; ss. }
          * guardH o. i. eapply RL; eauto. ii. inv H.
            destruct (Ident.eq_dec tid0 tid).
            { subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
              eapply NOT. econs.
              - rewrite IdentMap.gss. eauto.
              - s. erewrite Memory.add_o; eauto. condtac; [|eauto]; ss.
            }
            { eapply NOT. econs; eauto.
              rewrite IdentMap.gso; eauto.
            }
        + erewrite Memory.split_o; eauto. repeat condtac; ss.
          * i. des. inv IN. exfalso. eapply NOT. econs.
            { rewrite IdentMap.gss. eauto. }
            { s. erewrite Memory.split_o; eauto. condtac; ss. }
          * guardH o. i. des. inv IN.
            exfalso. eapply NOT. econs.
            { rewrite IdentMap.gss. eauto. }
            { s. erewrite Memory.split_o; eauto. repeat condtac; [|eauto|]; ss. }
          * guardH o. i. eapply RL; eauto. ii. inv H.
            destruct (Ident.eq_dec tid0 tid).
            { subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
              eapply NOT. econs.
              - rewrite IdentMap.gss. eauto.
              - s. erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            }
            { eapply NOT. econs; eauto.
              rewrite IdentMap.gso; eauto.
            }
        + erewrite Memory.lower_o; eauto. condtac; ss.
          * i. des. inv IN. exfalso. eapply NOT. econs.
            { rewrite IdentMap.gss. eauto. }
            { s. erewrite Memory.lower_o; eauto. condtac; ss. }
          * guardH o. i. eapply RL; eauto. ii. inv H.
            destruct (Ident.eq_dec tid0 tid).
            { subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
              eapply NOT. econs.
              - rewrite IdentMap.gss. eauto.
              - s. erewrite Memory.lower_o; eauto. condtac; [|eauto]; ss.
            }
            { eapply NOT. econs; eauto.
              rewrite IdentMap.gso; eauto.
            }
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
      - ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. econs; eauto. rewrite IdentMap.gss.
          rewrite TID in TID1. inv TID1. eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL. inv LOCAL0. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL. inv LOCAL0.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL. inv LOCAL0.
        ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite TID1 in TID. inv TID. depdes H1. destruct lc1. 
          ss. econs; eauto. 
          - rewrite IdentMap.gss. s. reflexivity. 
          - eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL. inv LOCAL0.
          unfold remove_promise. ss.
          replace promises0 with Memory.bot; eauto.
          exploit (@small_step_promise_decr_bot tid tid); [apply STEPS'|..].
          { ss. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID. }
          { s. rewrite IdentMap.gss. eauto. }
          { s. eauto. }
          eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL. inv LOCAL0. eauto.
      - s. i.
        hexploit writing_small_step_nonpromise_backward; try exact STEPS'; ss; eauto.
        { econs; eauto. s. ii. inv H. revert TID1.
          rewrite IdentMap.gsspec. condtac.
          - i. inv TID1.
            exploit (@small_step_promise_decr_bot tid tid); [apply STEPS'|..].
            { ss. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID. }
            { s. rewrite IdentMap.gss. eauto. }
            { s. eauto. }
            i. rewrite x0 in *. rewrite Memory.bot_get in PROMISES. congr.
          - rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
        }
        i. des.
        + inv H. exploit LR; eauto. i. des.
          hexploit writing_small_step_nonpromise_forward; try exact STEPT'; ss; eauto.
          { econs; eauto. }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_nonpromise_new; try exact STEPT'; ss; eauto.
          i. inv H. esplits; eauto.
      - i.
        hexploit writing_small_step_nonpromise_backward; try exact STEPT'; ss; eauto.
        { econs; eauto. }
        i. des.
        + inv H. exploit RL; eauto. i. des.
          hexploit writing_small_step_nonpromise_forward; try exact STEPS'; ss; eauto.
          { econs; eauto. s. ii. inv H. revert TID1.
            rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
          }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_nonpromise_new; try exact STEPS'; ss; eauto.
          i. inv H. esplits; eauto.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL1. inv LOCAL2. inv LOCAL0. inv LOCAL3.
          unfold remove_promise. ss.
          replace promises0 with Memory.bot; eauto.
          exploit (@small_step_promise_decr_bot tid tid); [apply STEPS'|..].
          { ss. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID. }
          { s. rewrite IdentMap.gss. eauto. }
          { s. eauto. }
          eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL1. inv LOCAL2. inv LOCAL0. inv LOCAL3. eauto.
      - s. i.
        hexploit writing_small_step_nonpromise_backward; try exact STEPS'; ss; eauto.
        { econs; eauto. s. ii. inv H. revert TID1.
          rewrite IdentMap.gsspec. condtac.
          - i. inv TID1.
            exploit (@small_step_promise_decr_bot tid tid); [apply STEPS'|..].
            { ss. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID. }
            { s. rewrite IdentMap.gss. eauto. }
            { s. eauto. }
            i. rewrite x0 in *. rewrite Memory.bot_get in PROMISES. congr.
          - rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
        }
        i. des.
        + inv H. exploit LR; eauto. i. des.
          hexploit writing_small_step_nonpromise_forward; try exact STEPT'; ss; eauto.
          { econs; eauto. }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_nonpromise_new; try exact STEPT'; ss; eauto.
          i. inv H. esplits; eauto.
      - i.
        hexploit writing_small_step_nonpromise_backward; try exact STEPT'; ss; eauto.
        { econs; eauto. }
        i. des.
        + inv H. exploit RL; eauto. i. des.
          hexploit writing_small_step_nonpromise_forward; try exact STEPS'; ss; eauto.
          { econs; eauto. s. ii. inv H. revert TID1.
            rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
          }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_nonpromise_new; try exact STEPS'; ss; eauto.
          i. inv H. esplits; eauto.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL. inv LOCAL0. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL. inv LOCAL0. ss. 
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1. eauto.
      - inv LOCAL. inv LOCAL0.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL. inv LOCAL0.
        ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite TID1 in TID. inv TID. depdes H1. destruct lc1. 
          ss. econs; eauto. 
          - rewrite IdentMap.gss. s. reflexivity. 
          - eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL. inv LOCAL0. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL. inv LOCAL0. ss. 
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1. eauto.
      - inv LOCAL. inv LOCAL0.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL. inv LOCAL0.
        ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite TID1 in TID. inv TID. depdes H1. destruct lc1. 
          ss. econs; eauto. 
          - rewrite IdentMap.gss. s. reflexivity. 
          - eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
Qed.

Lemma rtc_pi_step_future
      cST1 cST2 withprm cmp
      (WF1: pi_wf cmp cST1)
      (REFL: forall l t r, cmp l t r r)
      (STEPS: rtc (pi_step_all withprm) cST1 cST2):
  <<WF2: pi_wf cmp cST2>> /\
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
      tid cST1 cST2 withprm
      (STEP: pi_step_except withprm tid cST1 cST2):
  pi_step_all withprm cST1 cST2.
Proof.
  inv STEP; econs; eauto.
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

Lemma rtc_pi_step_except_find
      tid c1 c2 withprm
      (STEP: rtc (pi_step_except withprm tid) c1 c2):
  IdentMap.find tid c1.(fst).(Configuration.threads) = IdentMap.find tid c2.(fst).(Configuration.threads) /\
  IdentMap.find tid c1.(snd).(Configuration.threads) = IdentMap.find tid c2.(snd).(Configuration.threads).
Proof.
  induction STEP; auto. 
  des. rewrite <-IHSTEP, <-IHSTEP0.
  inv H. inv PI_STEP. inv USTEP.
  split; eauto using small_step_find.
  destruct (ThreadEvent_is_promising e); subst; eauto using small_step_find.
Qed.

Lemma pi_step_except_withoutprm
      tid c1 c2 withprm
      (STEP: pi_step_except false tid c1 c2):
  pi_step_except withprm tid c1 c2.
Proof.
  inv STEP. inv PI_STEP. inv USTEP. inv STEPT.
  destruct withprm; eauto 10.
Qed.

Lemma pi_wf_small_step_is_reading
      e s1 s2 t1
      withprm cmp tid l t v r o
      (PWF: pi_wf cmp (s1, t1))
      (STEP: small_step withprm tid e s1 s2)
      (READING: ThreadEvent.is_reading e = Some (l, t, v, r, o)):
  forall tid', ~ Threads.is_promised tid' l t t1.(Configuration.threads).
Proof.
  inv STEP. inv STEP0; inv STEP; inv READING.
  - inv LOCAL. inv PWF. eapply LR; eauto.
  - inv LOCAL1. inv PWF. eapply LR; eauto.
Qed.

Lemma pi_wf_small_step_is_promising
      e s1 t1 t2
      withprm cmp tid l t
      (PWF: pi_wf cmp (s1, t1))
      (STEP: small_step withprm tid e t1 t2)
      (PROMISING: ThreadEvent_is_promising e = Some (l, t)):
  Threads.is_promised tid l t t2.(Configuration.threads).
Proof.
  inv STEP. inv STEP0; inv STEP; inv PROMISING.
  s. econs.
  - rewrite IdentMap.gss. eauto.
  - inv LOCAL. s. eapply Memory.promise_get2. eauto.
Qed.

Lemma pi_step_except_small_step
      withprm tid a b
      (STEPS: rtc (pi_step_except withprm tid) a b):
  rtc (small_step_all withprm) a.(snd) b.(snd).
Proof.
  induction STEPS; econs; eauto.
  inv H. inv PI_STEP. inv USTEP. econs. eauto.
Qed.

Lemma small_step_is_promised
      withprm tid e c1 c2 x l t loc to
      (STEP: small_step withprm tid e c1 c2)
      (PROMISED: Threads.is_promised x l t c1.(Configuration.threads))
      (PROMISING: ThreadEvent_is_promising e = Some (loc, to)):
  Threads.is_promised x l t c2.(Configuration.threads).
Proof.
  inv PROMISED. destruct msg.
  inv STEP. ss.
  destruct (Ident.eq_dec x tid); cycle 1.
  { econs; eauto. rewrite IdentMap.gso; eauto. }
  subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
  inv STEP0; inv STEP; inv PROMISING.
  inv LOCAL. hexploit Memory.promise_promises_get1; eauto. i. des.
  econs; try rewrite IdentMap.gss; eauto.
Qed.

Lemma pi_step_remove_promises_aux
      n tid tidex cST1 cST2 cST3
      (WF: pi_wf loctmeq cST1)
      (NEQ: tid <> tidex)
      (CONSIS: forall tid0, promise_consistent_th tid0 cST3.(snd))
      (PSTEPS1: pi_step_evt true tid cST1 cST2)
      (PSTEP: rtcn (pi_step_except false tidex) n cST2 cST3):
  exists n' cT3',
    <<N: n' <= S n>> /\
    <<STEPS: rtcn (pi_step_except false tidex) n' cST1 (cST3.(fst),cT3')>> /\
    <<CONSIS: forall tid0, promise_consistent_th tid0 cT3'>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  exploit pi_step_future; eauto. i. des.
  inv PSTEPS1. inv USTEP. revert STEPS. condtac; cycle 1.
  { i. destruct cST3. esplits; cycle 1.
    - econs 2; eauto. econs; eauto. econs. econs; eauto.
      + inv STEPS. inv STEPT. econs; eauto.
      + rewrite COND. ss.
    - ss.
    - omega.
  }
  i. subst. inv PSTEP.
  { esplits; cycle 1.
    - econs.
    - i. destruct (Ident.eq_dec tid0 tid).
      + subst. eapply promise_consistent_th_small_step; eauto. by inv WF.
      + inv STEPT. ss. specialize (CONSIS tid0).
        ii. eapply CONSIS; eauto. s. rewrite IdentMap.gso; eauto.
    - omega.
  }
  inversion A12. inv PI_STEP. inv USTEP.
  assert (E0: ThreadEvent_is_promising e0 = None); [by inv STEPT0|].
  destruct p.
  exploit reorder_promise_small_step; try exact STEPT; eauto.
  { inv WF. auto. }
  { rewrite E0 in *. ii.
    hexploit pi_wf_small_step_is_reading; try exact WF2; eauto. i.
    hexploit pi_wf_small_step_is_promising; eauto.
  }
  { apply rtcn_rtc in A23.
    exploit pi_step_except_small_step; eauto. i. destruct cST3. ss.
    exploit pi_step_future; try exact WF2; eauto. i. des. inv WF0.
    clear -CONSIS WFT x0.
    revert WFT CONSIS. induction x0; eauto. i.
    inv H. inv USTEP. hexploit IHx0; eauto.
    { eapply small_step_future; eauto. }
    i. eapply promise_consistent_th_small_step; eauto.
  }
  i. des. unguardH STEP2. des.
  { destruct cST3. inv STEP2. esplits; cycle 1.
    - econs 2; eauto. econs; eauto. econs. econs; eauto.
      ii. eapply NOWR0; eauto.
      eapply small_step_is_promised; eauto.
    - ss.
    - omega.
  }
  assert (STEP1': pi_step_evt false tid0 (cS2, cT1) (cS0, c1')).
  { econs; eauto. econs; eauto.
    - etrans; eauto. inv STEP0. s. rewrite IdentMap.Facts.add_o. condtac; ss.
      subst. inv STEP; [|by inv STEP0; inv PROMISING]. inv STEP0. ss. inv PROMISING.
      rewrite TID0. eauto.
    - ii. eapply NOWR0; eauto.
      eapply small_step_is_promised; eauto.
  }
  assert (STEP2': pi_step_evt true tid (cS0, c1') (cS0, cT3)).
  { econs. econs; eauto.
    - rewrite PROMISING. ss.
    - destruct (Ident.eq_dec tid0 tid); subst; ss.
      rewrite E0 in *.
      inv STEPS. s. rewrite IdentMap.gso; auto.
      inv STEPT0. s. rewrite IdentMap.gso; auto.
    - ii. destruct e1'; ss.
  }
  exploit IH; try exact STEP2'; eauto.
  { eapply pi_step_future; eauto. }
  i. des. esplits; cycle 1.
  - econs; eauto.
  - ss.
  - omega.
Qed.

Lemma rtc_pi_step_remove_promises_aux
      tid tidex cST1 cST2 cST3
      (WF: pi_wf loctmeq cST1)
      (NEQ: tid <> tidex)
      (CONSIS: forall tid0, promise_consistent_th tid0 cST3.(snd))
      (PSTEPS1: rtc (pi_step_evt true tid) cST1 cST2)
      (PSTEP: rtc (pi_step_except false tidex) cST2 cST3):
  exists cT3',
  rtc (pi_step_except false tidex) cST1 (cST3.(fst),cT3') /\
  forall tid0, promise_consistent_th tid0 cT3'.
Proof.
  revert WF CONSIS PSTEP. induction PSTEPS1; i.
  - destruct cST3. esplits; eauto.
  - exploit IHPSTEPS1; eauto.
    { eapply pi_step_future; eauto. }
    i. des.
    apply rtc_rtcn in x0. des.
    eapply pi_step_remove_promises_aux in x0; eauto. i. des.
    apply rtcn_rtc in STEPS.
    esplits; eauto.
Qed.

Lemma rtc_pi_step_remove_promises
      tid tidex cST1 cST2 cST3
      (WF: pi_wf loctmeq cST1)
      (NEQ: tid <> tidex)
      (CONSIS: forall tid0, promise_consistent_th tid0 cST3.(snd))
      (PSTEPS1: rtc (pi_step_evt true tid) cST1 cST2)
      (PSTEP: rtc (pi_step_except false tidex) cST2 cST3):
  exists cT3',
  rtc (pi_step_except false tidex) cST1 (cST3.(fst),cT3') /\
  forall tid0, promise_consistent_th tid0 cT3'.
Proof.
  exploit rtc_pi_step_remove_promises_aux; eauto.
Qed.

Lemma promise_consistent_th_small_step_forward
      withprm tid e c1 c2
      (STEP: small_step withprm tid e c1 c2)
      (PRCONS: forall tid0, promise_consistent_th tid0 c1)
      (PRCONS2: promise_consistent_th tid c2)
      (WF: Configuration.wf c1):
  forall tid0, promise_consistent_th tid0 c2.
Proof.
  i. s. destruct (Ident.eq_dec tid0 tid) eqn: EQ.
  - subst. eauto.
  - ii. exploit small_step_find; eauto.
    s; intro X. rewrite <-X in THREAD. 
    eapply (PRCONS tid0); eauto.  
Qed.

Lemma rtc_promise_consistent_th_small_step_forward
      withprm tid c1 c2
      (STEP: rtc (small_step_evt withprm tid) c1 c2)
      (PRCONS: forall tid0, promise_consistent_th tid0 c1)
      (PRCONS2: promise_consistent_th tid c2)
      (WF: Configuration.wf c1):
  forall tid0, promise_consistent_th tid0 c2.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEP.
  ginduction STEP; eauto.
  apply Operators_Properties.clos_rt_rtn1_iff,
        Operators_Properties.clos_rt_rt1n_iff in STEP.
  i. inv H. hexploit promise_consistent_th_small_step_forward; eauto; cycle 1.
  { eapply rtc_small_step_future; eauto.
    eapply rtc_implies, STEP. eauto. }
  i. hexploit IHSTEP; eauto.
  eapply promise_consistent_th_small_step; eauto.
  eapply rtc_small_step_future; eauto.
  eapply rtc_implies, STEP. eauto.
Qed.

Lemma promise_consistent_th_small_step_backward
      withprm tid e c1 c2
      (STEP: small_step withprm tid e c1 c2)
      (PRCONS: forall tid0, promise_consistent_th tid0 c2)
      (WF: Configuration.wf c1):
  forall tid0, promise_consistent_th tid0 c1.
Proof.
  i. s. destruct (Ident.eq_dec tid0 tid) eqn: EQ.
  - subst. hexploit promise_consistent_th_small_step; eauto.
  - ii. exploit small_step_find; eauto.
    s; intro X. rewrite X in THREAD. 
    eapply (PRCONS tid0); eauto.  
Qed.

Lemma rtc_promise_consistent_th_small_step_backward
      withprm tid c1 c2
      (STEP: rtc (small_step_evt withprm tid) c1 c2)
      (PRCONS: forall tid0, promise_consistent_th tid0 c2)
      (WF: Configuration.wf c1):
  forall tid0, promise_consistent_th tid0 c1.
Proof.
  ginduction STEP; eauto.
  i. inv H. 
  i. hexploit promise_consistent_th_small_step_backward; eauto.
  i. hexploit IHSTEP; eauto.
  eapply small_step_future; eauto.
Qed.

Lemma pi_step_evt_to_true
      withprm tid cST1 cST2
      (STEP: pi_step_evt withprm tid cST1 cST2):
  pi_step_evt true tid cST1 cST2.
Proof.
  destruct withprm; eauto.
  inv STEP. inv USTEP. inv STEPT.
  econs. econs; eauto.
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (PRCONS: forall tid0, promise_consistent_th tid0 cT3):
  forall loc from to val rel ord tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, val, rel, ord) \/
         ThreadEvent.is_writing e = Some (loc, from, to, val, rel, ord)),
  ~Threads.is_promised tid' loc ts cST2.(snd).(Configuration.threads).
Proof.
  ii. inv H.
  inv PI_CONSISTENT. ss.
  guardH RW. destruct cST2 as [cS2 cT2].

  eapply rtc_implies in PI_STEPS; [|eapply pi_step_evt_to_true].
  exploit (@rtc_pi_step_remove_promises tid); eauto.
  { eapply promise_consistent_th_small_step_backward; eauto.
    exploit rtc_pi_step_future.
    { eauto. }
    { reflexivity. }
    { eapply rtc_implies, PI_STEPS. eauto. }
    intros [WF2 _].
    inv WF2. eauto. 
  }

  intro PI_STEPS'. des. ss.
  exploit CONSIS.
  { eauto. }
  { apply pi_steps_small_steps_snd in PI_STEPS. ss.
    eapply rtc_small_step_find in PI_STEPS; eauto.
    assert (EQ:= rtc_pi_step_except_find PI_STEPS'); des; ss.
    rewrite <-EQ0, PI_STEPS. eauto. }
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
    exploit rtc_pi_step_future; [| |eapply rtc_implies; [eapply (@pi_step_evt_all_incl true)|]|]; eauto.
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
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (FULFILL: promise_consistent_th tid cT3)
      (PRCONSIS: forall tid0, promise_consistent_th tid0 cST1.(snd)):
  exists cS3, pi_step withprm tid e cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  exploit rtc_pi_step_future; [eauto|reflexivity|..].
  { eapply rtc_implies, PI_STEPS. eauto. }
  intros [WF2 _].

  hexploit (promise_consistent_th_rtc_small_step).
  { econs 2; [|reflexivity]. eauto. }
  { inv WF2. eauto. }
  { eauto. }
  intro PCONSIS.

  assert (PRCONSIS3: forall tid0, promise_consistent_th tid0 cT3).
  { i. ss. eapply promise_consistent_th_small_step_forward; eauto; cycle 1.
    { inv WF2; eauto. }
    i. hexploit rtc_promise_consistent_th_small_step_forward.
    { eapply pi_steps_small_steps_snd in PI_STEPS. eauto. }
    { eauto. }
    { eapply promise_consistent_th_small_step; eauto.
      inv WF2; eauto. }
    { inv WF. eauto. }
    eauto.
  }

  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT PI_RACEFREE PI_STEPS STEP PRCONSIS3).

  exploit rtc_pi_step_future; [| |eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
  i; des. destruct cS2. inv WF2. ss. assert (MSTEP:=STEP). inv STEP. inv STEP0.
  - eexists. econs; [by eauto|by inv STEP; s; eauto|..].
    + inv STEP. ss. rewrite IdentMap.gss.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID.
    + i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
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
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 2; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 2; eauto.
          econs; eauto.
          s. hexploit RL; [| |by intro X; des; unfold loctmeq in *; subst; apply X]; eauto.
          i. destruct (Ident.eq_dec tid tid0) eqn: EQ; cycle 1.
          { eapply RW; s; eauto. }
          subst. intro PROMISED. inv PROMISED.
          ss. rewrite TID0 in TID. depdes TID.
          rdes FULFILL. ss. rewrite IdentMap.gss in FULFILL.
          exploit FULFILL; s; eauto.
          intro LT. ss.
          inv READABLE; eauto.
          apply TimeFacts.join_lt_des in LT. des.
          apply TimeFacts.join_lt_des in AC. des.
          revert BC0. unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
          eapply Time.lt_strorder. eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { destruct lc1, lc2. exploit local_simul_write; [| |by eapply LOCAL|..].
      { instantiate (1:= memory). ii. eapply LR in IN.
        des; eauto. }
      { econs. i. destruct msg1. exploit LR; eauto. i. des.
        inv WFT. inv WF1. exploit THREADS; eauto. i. inv x. ss.
        exploit PROMISES; eauto. i.
        destruct (Time.eq_dec to1 to2); cycle 1.
        { destruct (Configuration.memory cT2 loc0).(Cell.WF). splits.
          - eapply DISJOINT0; eauto.
          - ii. inv H. congr.
        }
        subst. exfalso. eapply NOT. econs; eauto.
      }
      intro WRITE; des.
      eexists; econs. 
      - eauto.
      - s. econs; eauto.
        s. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { destruct lc2, lc3. exploit local_simul_write; [| |by eapply LOCAL2|..].
      { instantiate (1:= memory). ii. eapply LR in IN.
        des; eauto. }
      { inv LOCAL1. ss.
        econs. i. destruct msg1. exploit LR; eauto. i. des.
        inv WFT. inv WF1. exploit THREADS; eauto. i. inv x.
        exploit PROMISES; eauto. i.
        destruct (Time.eq_dec to1 to2); cycle 1.
        { destruct (Configuration.memory cT2 loc0).(Cell.WF). splits.
          - eapply DISJOINT0; eauto.
          - ii. inv H. congr.
        }
        subst. exfalso. eapply NOT. econs; eauto.
      }
      intro WRITE; des.

      inv LOCAL1. eexists. econs.
      - econs; eauto. econs 2. econs 4; eauto; econs; eauto.
      - s. econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 4; [by eauto|..].
          { 
            econs; eauto.
            s. hexploit RL; [| |by intro X; des; unfold loctmeq in *; subst; apply X]; eauto.
            i. destruct (Ident.eq_dec tid tid0) eqn: EQ; cycle 1.
            { eapply RW; s; eauto. }
            subst. intro PROMISED. inv PROMISED.
            ss. rewrite TID0 in TID. depdes TID.

            r in FULFILL. hexploit FULFILL.
            { s. rewrite IdentMap.gss. eauto. }
            clear FULFILL. intro FULFILL.

            eapply write_step_promise_consistent in FULFILL; eauto.
            exploit FULFILL; s; eauto.
            intro LT. ss.
            inv READABLE; eauto.
            apply TimeFacts.join_lt_des in LT. des.
            apply TimeFacts.join_lt_des in AC. des.
            revert BC0. unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
            eapply Time.lt_strorder. eauto.
          }
          { eauto. }
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
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
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
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
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
Grab Existential Variables.
  { exact Time.bot. }
  { exact xH. }
  { exact true. }
Qed.

Lemma small_step_evt_to_true
      withprm tid cST1 cST2
      (STEP: small_step_evt withprm tid cST1 cST2):
  small_step_evt true tid cST1 cST2.
Proof.
  destruct withprm; eauto.
  inv STEP. inv USTEP. 
  econs. econs; eauto.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 withprm
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      cT3 pre
      (STEP: with_pre (small_step withprm tid) cST2.(snd) pre cT3)
      (FULFILL: forall tid0, promise_consistent_th tid0 cT3):
  exists cS3 pre', with_pre (pi_step withprm tid) cST2 pre' (cS3,cT3) /\ 
                   pre = pi_pre_proj pre'.
Proof.
  destruct cST2 as [cS2 cT2].
  revert_until STEP. induction STEP.
  { s; i. eauto. }
  s; i.

  exploit IHSTEP; s; eauto.
  { eapply promise_consistent_th_small_step_backward; eauto.
    exploit rtc_pi_step_future.
    { eauto. }
    { reflexivity. }
    { eapply rtc_implies, PI_STEPS. eauto. }
    intros [WF2 _]. inv WF2.

    exploit with_pre_rtc_step_union; eauto.
    i. exploit rtc_small_step_future.
    { eauto. }
    { eapply rtc_implies, x0. eauto. }
    i; des; eauto.
  }

  intro STEPS. des. ss.
  eapply (@pi_consistent_small_step_pi _ _ _ (_,_)) in PSTEP; eauto; cycle 1.
  { etrans; eauto. subst. 
    eapply rtc_implies; [eapply pi_step_evt_to_true|].
    eapply with_pre_rtc_step_union; eauto. }
  { eapply (@rtc_promise_consistent_th_small_step_backward true); try apply FULFILL. 
    - etrans.
      + eapply pi_steps_small_steps_snd. eauto.
      + eapply rtc_implies; [eapply small_step_evt_to_true|].
        eapply with_pre_rtc_step_union; eauto.
    - inv WF. eauto.
  }
  des; esplits; eauto.
Qed.

Theorem pi_consistent_step_pi
      cST1 cT2 e tid
      (WF: pi_wf loctmeq cST1)
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
  { i. eapply consistent_promise_consistent_th; eauto. }
  i; des. eexists. eapply with_pre_rtc_step_union. eauto.
Qed.
