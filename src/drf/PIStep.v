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
Require Import Configuration.
Require Import Progress.

Require Import MemoryRel.
Require Import SmallStep.
Require Import Fulfilled.
Require Import ReorderPromise.
Require Import Race.
Require Import PromiseConsistent.

Set Implicit Arguments.

Inductive pi_step withprm: Ident.t -> ThreadEvent.t -> Configuration.t*Configuration.t -> Configuration.t*Configuration.t -> Prop :=
| pi_step_step
    e tid cS1 cT1 cS2 cT2
    (STEPT: small_step withprm tid e cT1 cT2)
    (STEPS: if ThreadEvent.is_promising e
            then cS1 = cS2
            else small_step false tid e cS1 cS2)
    (LANGMATCH: 
     option_map fst (IdentMap.find tid cS2.(Configuration.threads)) =
     option_map fst (IdentMap.find tid cT2.(Configuration.threads)))
    (NOWR: forall loc from ts val rel ord tid' ts'
             (WRITE: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord) \/
                     ThreadEvent.is_reading e = Some (loc, ts, val, rel, ord))
             (TIDNEQ: tid' <> tid),
           ~ Threads.is_promised tid' loc ts' cT1.(Configuration.threads)):
  pi_step withprm tid e (cS1,cT1) (cS2,cT2)
.
Hint Constructors pi_step.

Definition pi_step_evt withprm tid cST1 cST2: Prop :=
  union (pi_step withprm tid) cST1 cST2.
Hint Unfold pi_step_evt.

Definition pi_step_all withprm cST1 cST2: Prop :=
  union (pi_step_evt withprm) cST1 cST2.
Hint Unfold pi_step_all.

Inductive pi_step_except withprm (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro tid
    (PI_STEP: pi_step_evt withprm tid cST1 cST2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_except.

Definition remove_promise (th: {lang : Language.t & Language.state lang} * Local.t) :=
  (th.(fst), Local.mk th.(snd).(Local.tview) Memory.bot).

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
  exists cS3 e val ord,
    <<STEPS: rtc (small_step_evt false tid) cS2 cS3>> /\
    <<PROEVT: Configuration_program_event cS3 tid e>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, val, ord)>> /\
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
  - destruct (ThreadEvent.is_promising e).
    + subst. ss. econs.
    + eapply small_step_future in STEPS; eauto; des; ss.
  - eapply small_step_future in STEPT; eauto; des; ss.
  - assert (WFT2: Configuration.wf cT2).
    { by eapply small_step_future, STEPT. }
    assert (WFS2: Configuration.wf cS2).
    { destruct (ThreadEvent.is_promising e); [by inv STEPS|].
      by eapply small_step_future, STEPS. }
    assert (STEPS' :=STEPS).

    generalize STEPT. intro STEPT'.
    destruct cS, cT. inv STEPT. guardH PFREE.
    inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
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
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
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
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL0. inv LOCAL1. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL0. inv LOCAL1.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL0. inv LOCAL1.
        ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite TID1 in TID. inv TID. depdes H1. destruct lc1. 
          ss. econs; eauto. 
          - rewrite IdentMap.gss. s. reflexivity. 
          - eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL0. inv LOCAL1.
          unfold remove_promise. ss.
          replace promises0 with Memory.bot; eauto.
          exploit (@small_step_promise_decr_bot tid tid); [apply STEPS'|..].
          { ss. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID. }
          { s. rewrite IdentMap.gss. eauto. }
          { s. eauto. }
          eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL0. inv LOCAL1. eauto.
      - s. i.
        hexploit writing_small_step_fulfilled_backward; try exact STEPS'; ss; eauto.
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
          hexploit writing_small_step_fulfilled_forward; try exact STEPT'; ss; eauto.
          { econs; eauto. }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_fulfilled_new; try exact STEPT'; ss; eauto.
          i. inv H. esplits; eauto.
      - i.
        hexploit writing_small_step_fulfilled_backward; try exact STEPT'; ss; eauto.
        { econs; eauto. }
        i. des.
        + inv H. exploit RL; eauto. i. des.
          hexploit writing_small_step_fulfilled_forward; try exact STEPS'; ss; eauto.
          { econs; eauto. s. ii. inv H. revert TID1.
            rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
          }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_fulfilled_new; try exact STEPS'; ss; eauto.
          i. inv H. esplits; eauto.
    }
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
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
        hexploit writing_small_step_fulfilled_backward; try exact STEPS'; ss; eauto.
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
          hexploit writing_small_step_fulfilled_forward; try exact STEPT'; ss; eauto.
          { econs; eauto. }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_fulfilled_new; try exact STEPT'; ss; eauto.
          i. inv H. esplits; eauto.
      - i.
        hexploit writing_small_step_fulfilled_backward; try exact STEPT'; ss; eauto.
        { econs; eauto. }
        i. des.
        + inv H. exploit RL; eauto. i. des.
          hexploit writing_small_step_fulfilled_forward; try exact STEPS'; ss; eauto.
          { econs; eauto. s. ii. inv H. revert TID1.
            rewrite IdentMap.Properties.F.map_o. unfold remove_promise.
            destruct (UsualFMapPositive.UsualPositiveMap'.find tid0 threads0); ss.
            i. inv TID1. rewrite Memory.bot_get in PROMISES. congr.
          }
          i. inv H. esplits; eauto.
        + inv H.
          hexploit writing_small_step_fulfilled_new; try exact STEPS'; ss; eauto.
          i. inv H. esplits; eauto.
    }
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL0. inv LOCAL1. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL0. inv LOCAL1. ss. 
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1. eauto.
      - inv LOCAL0. inv LOCAL1.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL0. inv LOCAL1.
        ii. exploit RL; eauto. i; des.
        ii. apply (NOT tid0). inv H.
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite TID1 in TID. inv TID. depdes H1. destruct lc1. 
          ss. econs; eauto. 
          - rewrite IdentMap.gss. s. reflexivity. 
          - eauto. }
        econs; eauto. rewrite IdentMap.gso; eauto.
    }
    { inv STEPS.
      inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. rewrite !IdentMap.gss.
          inv LOCAL0. inv LOCAL1. eauto.
        + by rewrite !IdentMap.gso.
      - inv LOCAL0. inv LOCAL1. ss. 
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1. eauto.
      - inv LOCAL0. inv LOCAL1.
        ii. exploit LR; eauto. i; des.
        esplits; eauto.
        ii. eapply (NOT tid0). inv H. 
        destruct (Ident.eq_dec tid0 tid) eqn: EQ.
        { subst. rewrite IdentMap.gss in TID1. inv TID1.
          econs; eauto. }
        rewrite IdentMap.gso in TID1; eauto. econs; eauto.
      - inv LOCAL0. inv LOCAL1.
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

Lemma pi_step_small_step_fst
      tid e cST1 cST2 withprm withprm'
      (PI_STEP: pi_step withprm tid e cST1 cST2):
  small_opt_step withprm' tid e (fst cST1) (fst cST2).
Proof.
  inv PI_STEP.
  destruct (ThreadEvent.is_promising e) eqn:X.
  - subst. ss. destruct e; inv X. econs 1. ss.
  - econs 2. ss. destruct withprm'; ss. inv STEPS; eauto.
Qed.

Lemma tau_pi_steps_tau_small_steps_fst
      tid cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (tau (pi_step withprm tid)) cST1 cST2):
  rtc (tau (small_step withprm' tid)) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. exploit pi_step_small_step_fst; eauto. i. inv x1.
  - rewrite H1. ss.
  - econs; eauto.
Qed.

Lemma pi_steps_small_steps_fst
      tid cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  rtc (small_step_evt withprm' tid) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. 
  destruct (ThreadEvent.is_promising e).
  - subst. eauto.
  - econs; eauto. s. inv STEPS. destruct withprm'; econs; eauto 10. 
Qed.

Lemma pi_step_small_step_snd
      cST1 cST2 withprm tid
      (PI_STEP: pi_step_evt withprm tid cST1 cST2):
  small_step_evt withprm tid (snd cST1) (snd cST2).
Proof.
  inv PI_STEP. inv USTEP. econs. eauto.
Qed.

Lemma pi_steps_all_small_steps_all_snd
      cST1 cST2 withprm
      (PI_STEPS: rtc (pi_step_all withprm) cST1 cST2):
  rtc (small_step_all withprm) (snd cST1) (snd cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. exploit pi_step_small_step_snd; eauto.
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
  destruct (ThreadEvent.is_promising e0) eqn: PROM.
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
  destruct (ThreadEvent.is_promising e); subst; eauto using small_step_find.
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
  inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL]; inv READING.
  - inv LOCAL0. inv PWF. eapply LR; eauto.
  - inv LOCAL1. inv PWF. eapply LR; eauto.
Qed.

Lemma pi_wf_small_step_is_promising
      e s1 t1 t2
      withprm cmp tid l t
      (PWF: pi_wf cmp (s1, t1))
      (STEP: small_step withprm tid e t1 t2)
      (PROMISING: ThreadEvent.is_promising e = Some (l, t)):
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
      (PROMISING: ThreadEvent.is_promising e = Some (loc, to)):
  Threads.is_promised x l t c2.(Configuration.threads).
Proof.
  inv PROMISED. destruct msg.
  inv STEP. guardH PFREE. ss.
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
      + inv STEPS. destruct pf; ss. inv STEPT. clear PFREE0. econs; eauto.
        destruct pf; eauto. inv STEP0; ss. inv STEP1; ss.
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
  destruct p.
  destruct (ThreadEvent.is_lower_none e) eqn: NOTLN.
  { destruct cST3. esplits; eauto.
     econs; eauto.
     econs; try apply NEQ.
     econs; econs; rewrite ?COND; eauto. 
     inv STEPT. destruct pf; eauto.
     inv STEP. inv STEP0. ss. by rewrite NOTLN in PF.
  }

  exploit reorder_promise_small_step; try exact STEPT; eauto.
  { inv WF. auto. }
  { ii. destruct (ThreadEvent.is_promising e0) eqn:E0; [by destruct e0|].
    ii; hexploit pi_wf_small_step_is_reading; try exact WF2; eauto.
    i. hexploit pi_wf_small_step_is_promising; try exact STEPT; eauto.
  }
  { apply rtcn_rtc in A23. inv A12.
    exploit pi_step_except_small_step; eauto. i. destruct cST3. ss.
    exploit pi_step_future; try exact WF2; eauto. i. des. inv WF0.
    clear -CONSIS WFT x0.
    revert WFT CONSIS. induction x0; eauto. i.
    inv H. inv USTEP. hexploit IHx0; eauto.
    { eapply small_step_future; eauto. }
    i. eapply promise_consistent_th_small_step; eauto.
  }
  i. destruct cST3. subst. des.
  { destruct (ThreadEvent.is_promising e0) eqn:E0; subst.
    - exploit IH; try exact A23; try exact WF; eauto.
      { econs; econs; eauto; ii; by des; destruct e2', e0. }
      i. des. esplits; try exact STEPS; eauto.
    - assert (EQ: e2' = e0). 
      { by destruct e2', e0; inv EVENT. }
      subst. esplits; [|econs; try exact A23|]; eauto.
      econs; eauto. econs; econs.
      + instantiate (1 := e0).
        inv STEP. inv STEP0; [by inv STEP|]. econs; eauto.
      + rewrite E0. eauto.
      + eauto.
      + ii. eapply NOWR0; eauto.
        inv H. econs; eauto. rewrite <- TID0.
        symmetry; eapply small_step_find; eauto.
  }
  assert (STEP0': pi_step_except false tidex (cS2, cT1) (cS0,c1')).
  { econs; eauto. econs; econs.
    + eauto.
    + by destruct e2', e0; ss; inv EVENT.
    + rewrite LANGMATCH0. 
      inv STEP2. inv STEP; [|by inv STEP0].
      s. inv STEP0. destruct (Ident.eq_dec tid0 tid).
      * subst. by rewrite IdentMap.gss, TID0.
      * rewrite IdentMap.gso; eauto.
    + ii. eapply NOWR0; eauto.
      * des; destruct e2'; ss; destruct e0; ss; inv EVENT; destruct event0; eauto.
      * eapply small_step_is_promised; eauto.
  }
  assert (STEP2': pi_step_evt true tid (cS0, c1') (cS0, cT3)).
  { econs. econs; eauto.
    - rewrite PROMISING. ss.
    - destruct (Ident.eq_dec tid0 tid); subst; ss.
      rewrite <-(small_step_find STEPT0); eauto.
      rewrite <-LANGMATCH.
      destruct (ThreadEvent.is_promising e0); subst; eauto.
      rewrite (small_step_find STEPS); eauto.
    - ii. by des; destruct e1'.
  }
  assert (STEP1': pi_step_evt false tid0 (cS2, cT1) (cS0, c1')).
  { econs. econs; eauto.
    - by destruct e2', e0; inv EVENT.
    - etrans; eauto. destruct (Ident.eq_dec tid tid0). 
      + subst. inv STEP2. s. rewrite IdentMap.gss. 
        inv STEP; [by inv STEP0; rewrite TID0|by inv STEP0; inv PROMISING].
      + rewrite (small_step_find STEP2); eauto.
    - ii. eapply NOWR0; eauto.
      + des; destruct e2'; ss; destruct e0; ss; inv EVENT; destruct event0; eauto.
      + eapply small_step_is_promised; eauto.
  }

  exploit IH; try exact STEP2'; eauto.
  { eapply pi_step_future; try exact WF; eauto. }
  i. des. esplits; [|econs; try exact STEPS0|]; eauto; omega.
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

Lemma pi_step_evt_to_true
      withprm tid cST1 cST2
      (STEP: pi_step_evt withprm tid cST1 cST2):
  pi_step_evt true tid cST1 cST2.
Proof.
  destruct withprm; eauto.
  inv STEP. inv USTEP. inv STEPT.
  econs. econs; eauto.
Qed.
