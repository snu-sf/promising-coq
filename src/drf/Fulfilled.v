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

Require Import SmallStep.

Set Implicit Arguments.

Inductive fulfilled c l f t msg :=
| fulfilled_intro
    (GET: Memory.get l t c.(Configuration.memory) = Some (f, msg))
    (FULFILLED: forall tid, ~ Threads.is_promised tid l t c.(Configuration.threads))
.

Lemma writing_small_step_fulfilled_forward
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg
    (NP: fulfilled c1 l f t msg),
    fulfilled c2 l f t msg.
Proof.
  inv STEP. guardH PFREE.
  inv STEP0; inv STEP; ss. inv LOCAL; inv WRITING; ss.
  - inv LOCAL0. inv WRITE. inv PROMISE.
    { i. inv NP. econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss.
        des. subst. exploit Memory.add_get0; eauto. congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. exploit Memory.split_get0; eauto. i. des. congr. }
        condtac; ss. guardH o. des. subst.
        exfalso. eapply FULFILLED. econs; eauto.
        hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * guardH o. guardH o0. i. des. inv PROMISES0.
            eapply FULFILLED. econs; eauto.
            hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
          * i. eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst. exfalso. eapply FULFILLED. econs; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          guardH o. guardH o0. i. des. inv PROMISES0.
          eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { i. inv NP. econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss.
        des. subst. exploit Memory.add_get0; eauto. congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. exploit Memory.split_get0; eauto. i. des. congr. }
        condtac; ss. guardH o. des. subst.
        exfalso. eapply FULFILLED. econs; eauto.
        hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * guardH o. guardH o0. i. des. inv PROMISES0.
            eapply FULFILLED. econs; eauto.
            hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
          * i. eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst. exfalso. eapply FULFILLED. econs; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          guardH o. guardH o0. i. des. inv PROMISES0.
          eapply FULFILLED. econs; eauto.
        + i. eapply FULFILLED. econs; eauto.
    }
Qed.

Lemma writing_small_step_fulfilled_new
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  fulfilled c2 loc from to (Message.mk val released).
Proof.
  inv STEP. guardH PFREE.
  inv STEP0; inv STEP; ss. inv LOCAL; inv WRITING; ss.
  - inv LOCAL0. inv WRITE. inv PROMISE.
    { econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.add_get0; eauto. i.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        exfalso. clear -o. des; apply o; auto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.split_get0; eauto. i. des.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.lower_get0; eauto. i.
          inv WF. inv WF0. exploit DISJOINT; eauto. i.
          eapply Memory.disjoint_get; try apply x; eauto.
          eapply Memory.lower_get0. eauto.
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.add_get0; eauto. i.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        exfalso. clear -o. des; apply o; auto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.split_get0; eauto. i. des.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.lower_get0; eauto. i.
          inv WF. inv WF0. exploit DISJOINT; eauto. i.
          eapply Memory.disjoint_get; try apply x; eauto.
          eapply Memory.lower_get0. eauto.
    }
Qed.

Lemma writing_small_step_fulfilled_backward
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg
    (NP: fulfilled c2 l f t msg),
    fulfilled c1 l f t msg \/ (l, f, t, msg) = (loc, from, to, Message.mk val released).
Proof.
  inv STEP. guardH PFREE.
  inv STEP0; inv STEP; ss. inv LOCAL; inv WRITING; ss.
  - inv LOCAL0. inv WRITE. inv PROMISE.
    { i. inv NP. ss. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.add_o; eauto. condtac; [|eauto]. ss.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      guardH o. condtac; ss.
      { i. des. inv GET. exfalso. eapply FULFILLED. econs.
        - rewrite IdentMap.gss. eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto.
          do 2 (condtac; try congr). eauto.
      }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.split_o; eauto. do 2 (condtac; try congr). eauto.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; [|eauto]. ss.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { i. inv NP. ss. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.add_o; eauto. condtac; [|eauto]. ss.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      guardH o. condtac; ss.
      { i. des. inv GET. exfalso. eapply FULFILLED. econs.
        - rewrite IdentMap.gss. eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto.
          do 2 (condtac; try congr). eauto.
      }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.split_o; eauto. do 2 (condtac; try congr). eauto.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply FULFILLED. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; [|eauto]. ss.
        - eapply FULFILLED. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
Qed.

Lemma writing_small_step_fulfilled
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg,
    fulfilled c2 l f t msg <-> fulfilled c1 l f t msg \/ (l, f, t, msg) = (loc, from, to, Message.mk val released).
Proof.
  econs; i.
  - eapply writing_small_step_fulfilled_backward; eauto.
  - des.
    + eapply writing_small_step_fulfilled_forward; eauto.
    + inv H. eapply writing_small_step_fulfilled_new; eauto.
Qed.

Lemma nonwriting_small_step_fulfilled_forward
      tid e c1 c2
      (WF: Configuration.wf c1)
      (STEP: small_step false tid e c1 c2)
      (NONWRITING: ThreadEvent.is_writing e = None):
  forall l f t msg
    (NP: fulfilled c1 l f t msg),
    fulfilled c2 l f t msg.
Proof.
  inv STEP. guardH PFREE.
  inv STEP0; inv STEP; inv LOCAL; inv NONWRITING.
  - unguardH PFREE.
    apply promise_pf_inv in PFREE. des. subst. inv PROMISE.
    i. inv NP. econs; ss.
    + erewrite Memory.lower_o; eauto. condtac; ss. des. subst.
      exfalso. eapply FULFILLED. econs; eauto. eapply Memory.lower_get0. eauto.
    + ii. inv H.
      revert TID0. rewrite IdentMap.gsspec. condtac; ss; i.
      * inv TID0. ss. eapply FULFILLED.
        destruct msg0. hexploit Memory.op_get_inv; eauto.
        { econs 3. eauto. }
        i. des.
        { subst. econs; eauto. eapply Memory.lower_get0. eauto. }
        { econs; eauto. }
      * eapply FULFILLED. econs; eauto.
  - i. inv NP. econs; eauto. ii. inv H. ss.
    revert TID0. rewrite IdentMap.gsspec. condtac; ss; i.
    + inv TID0. eapply FULFILLED. econs; eauto.
    + eapply FULFILLED. econs; eauto.
  - inv LOCAL0.
    i. inv NP. econs; eauto. ii. inv H. ss.
    revert TID0. rewrite IdentMap.gsspec. condtac; ss; i.
    + inv TID0. eapply FULFILLED. econs; eauto.
    + eapply FULFILLED. econs; eauto.
  - inv LOCAL0.
    i. inv NP. econs; eauto. ii. inv H. ss.
    revert TID0. rewrite IdentMap.gsspec. condtac; ss; i.
    + inv TID0. eapply FULFILLED. econs; eauto.
    + eapply FULFILLED. econs; eauto.
  - inv LOCAL0.
    i. inv NP. econs; eauto. ii. inv H. ss.
    revert TID0. rewrite IdentMap.gsspec. condtac; ss; i.
    + inv TID0. eapply FULFILLED. econs; eauto.
    + eapply FULFILLED. econs; eauto.
Qed.
