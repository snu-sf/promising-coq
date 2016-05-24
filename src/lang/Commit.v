Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.

Set Implicit Arguments.


Module Commit <: JoinableType.
  Structure t_ := mk {
    rel: LocFun.t Capability.t;
    cur: Capability.t;
    acq: Capability.t;
  }.
  Definition t := t_.

  Definition elt: t := mk (LocFun.init Capability.elt) Capability.elt Capability.elt.

  Inductive wf (commit:t): Prop :=
  | wf_intro
      (REL: forall loc, Capability.wf (commit.(rel) loc))
      (CUR: Capability.wf commit.(cur))
      (ACQ: Capability.wf commit.(acq))
      (REL_CUR: forall loc, Capability.le (commit.(rel) loc) commit.(cur))
      (CUR_ACQ: Capability.le commit.(cur) commit.(acq))
  .

  Inductive closed (commit:t) (mem:Memory.t): Prop :=
  | closed_intro
      (REL: forall loc, Memory.closed_capability (commit.(rel) loc) mem)
      (CUR: Memory.closed_capability commit.(cur) mem)
      (ACQ: Memory.closed_capability commit.(acq) mem)
  .

  Lemma future_closed
        commit mem1 mem2
        (CLOSED: closed commit mem1)
        (FUTURE: Memory.future mem1 mem2):
    closed commit mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.future_closed_capability; eauto.
  Qed.

  Definition eq := @eq t.

  Inductive le_ (lhs rhs:t): Prop :=
  | le_intro
      (REL: forall (loc:Loc.t), Capability.le (LocFun.find loc lhs.(rel)) (LocFun.find loc rhs.(rel)))
      (CUR: Capability.le lhs.(cur) rhs.(cur))
      (ACQ: Capability.le lhs.(acq) rhs.(acq))
  .
  Definition le := le_.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Definition join (lhs rhs:t): t :=
    mk (fun loc => Capability.join (lhs.(rel) loc) (rhs.(rel) loc))
       (Capability.join lhs.(cur) rhs.(cur))
       (Capability.join lhs.(acq) rhs.(acq)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join. f_equal.
    - extensionality loc. apply Capability.join_comm.
    - apply Capability.join_comm.
    - apply Capability.join_comm.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. s. f_equal.
    - extensionality loc. apply Capability.join_assoc.
    - apply Capability.join_assoc.
    - apply Capability.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    econs.
    - i. apply Capability.join_l.
    - apply Capability.join_l.
    - apply Capability.join_l.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof.
    econs.
    - i. apply Capability.join_r.
    - apply Capability.join_r.
    - apply Capability.join_r.
  Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS. econs.
    - i. apply Capability.join_spec; eauto.
    - apply Capability.join_spec; eauto.
    - apply Capability.join_spec; eauto.
  Qed.

  Inductive read
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Capability.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_intro
      (MON: le commit1 commit2)
      (ACQ: Capability.le released commit2.(acq))
      (UR1: Time.le (commit1.(cur).(Capability.ur) loc) ts)
      (RW1: Ordering.le Ordering.relaxed ord ->
            Time.le (commit1.(cur).(Capability.rw) loc) ts)
      (RW2: Time.le ts (commit2.(cur).(Capability.rw) loc))
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le released commit2.(cur))
      (WF_REL: Capability.wf released)
      (WF: Commit.wf commit2)
  .

  Inductive write
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Capability.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_intro
      (MON: le commit1 commit2)
      (REL: Time.le (released.(Capability.rw) loc) ts)
      (RW1: Time.le (commit1.(cur).(Capability.rw) loc) ts)
      (RW2: Time.le ts (commit2.(cur).(Capability.ur) loc))
      (REL1: Capability.le (commit1.(Commit.rel) loc) released)
      (REL2: Capability.le released (commit2.(Commit.rel) loc))
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le commit1.(Commit.cur) released /\
           Time.le ts (released.(Capability.rw) loc))
      (WF_REL: Capability.wf released)
      (WF: Commit.wf commit2)
  .

  Inductive read_fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_fence_intro
      (MON: le commit1 commit2)
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le commit1.(Commit.acq) commit2.(Commit.cur))
      (WF: Commit.wf commit2)
  .

  Inductive write_fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_fence_intro
      (MON: le commit1 commit2)
      (RA: Ordering.le Ordering.acqrel ord ->
           forall loc, Capability.le commit1.(Commit.cur) (commit2.(Commit.rel) loc))
      (WF: Commit.wf commit2)
  .
End Commit.

Module CommitFacts.
  Ltac tac :=
    repeat
      (try match goal with
           | [|- Capability.le (Capability.join _ _) _] =>
             apply Capability.join_spec
           | [|- Capability.le (Capability.incr_ur _ _ _) _] =>
             apply Capability.incr_ur_spec
           | [|- Capability.le (Capability.incr_rw _ _ _) _] =>
             apply Capability.incr_rw_spec

           | [|- TimeMap.le (TimeMap.incr _ _ _) _] =>
             apply TimeMap.incr_spec
           | [|- Capability.le ?s (Capability.incr_ur _ _ ?s)] =>
             apply Capability.incr_ur_le
           | [|- Capability.le ?s (Capability.incr_rw _ _ ?s)] =>
             apply Capability.incr_rw_le

           | [|- Capability.le ?s (Capability.join _ ?s)] =>
             apply Capability.join_r
           | [|- Capability.le ?s (Capability.join ?s _)] =>
             apply Capability.join_l

           | [|- Capability.le (Capability.join_if _ _ _) _] =>
             apply Capability.join_if_spec
           | [|- Capability.le _ (if _ then _ else _)] =>
             apply Capability.join_if_le

            | [|- Memory.closed_capability (Capability.incr_ur _ _ _) _] =>
              eapply Memory.incr_ur_closed_capability; eauto
            | [|- Memory.closed_capability (Capability.incr_rw _ _ _) _] =>
              eapply Memory.incr_rw_closed_capability; eauto
            | [|- Memory.closed_capability (Capability.join _ _) _] =>
              eapply Memory.join_closed_capability; eauto

            | [|- Time.le (TimeMap.join _ _ _) _] =>
              apply Time.join_spec
           end; subst; ss; i).

  Lemma wf_get
        loc commit1 mem
        (CLOSED: Commit.closed commit1 mem):
    exists msg,
      Memory.get loc (commit1.(Commit.cur).(Capability.rw) loc) mem = Some msg.
  Proof.
    inversion CLOSED. inv CUR.
    specialize (RW loc). des. eauto.
  Qed.

  Lemma read_mon1
        commit1 commit2
        (LE: Commit.le commit1 commit2):
    Commit.read commit2 <5= Commit.read commit1.
  Proof.
    i. inv PR. econs; auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
  Qed.

  Lemma write_mon1
        commit1 commit2
        (LE: Commit.le commit1 commit2):
    Commit.write commit2 <5= Commit.write commit1.
  Proof.
    i. inv PR. econs; auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
    - i. specialize (RA H). des. splits; auto.
      etrans; [apply LE|]. auto.
  Qed.

  Lemma read_fence_mon1
        commit1 commit2
        (LE: Commit.le commit1 commit2):
    Commit.read_fence commit2 <2= Commit.read_fence commit1.
  Proof.
    i. inv PR. econs; auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
  Qed.

  Lemma write_fence_mon1
        commit1 commit2
        (LE: Commit.le commit1 commit2):
    Commit.write_fence commit2 <2= Commit.write_fence commit1.
  Proof.
    i. inv PR. econs; auto.
    - etrans; [apply LE|]. auto.
    - etrans; [apply LE|]. auto.
  Qed.

  Lemma read_mon2
        loc ts released
        ord2 ord3
        commit1 commit2 commit3
        (READ: Commit.read commit1 loc ts released ord2 commit2)
        (ORD: Ordering.le ord3 ord2)
        (LE: Commit.le commit2 commit3)
        (WF: Commit.wf commit3):
    Commit.read commit1 loc ts released ord3 commit3.
  Proof.
    inv READ. econs; eauto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE]. auto.
    - i. apply RW1. etrans; eauto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE].
      apply RA. etrans; eauto.
  Qed.

  Lemma write_mon2
        loc ts released
        ord2 ord3
        commit1 commit2 commit3
        (WRITE: Commit.write commit1 loc ts released ord2 commit2)
        (ORD: Ordering.le ord3 ord2)
        (LE: Commit.le commit2 commit3)
        (WF: Commit.wf commit3):
    Commit.write commit1 loc ts released ord3 commit3.
  Proof.
    inv WRITE. econs; auto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE]. auto.
    - i. apply RA. etrans; eauto.
  Qed.

  Lemma read_fence_mon2
        ord2 ord3
        commit1 commit2 commit3
        (FENCE: Commit.read_fence commit1 ord2 commit2)
        (ORD: Ordering.le ord3 ord2)
        (LE: Commit.le commit2 commit3)
        (WF: Commit.wf commit3):
    Commit.read_fence commit1 ord3 commit3.
  Proof.
    inv FENCE. econs; auto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE].
      apply RA. etrans; eauto.
  Qed.

  Lemma write_fence_mon2
        ord2 ord3
        commit1 commit2 commit3
        (FENCE: Commit.write_fence commit1 ord2 commit2)
        (ORD: Ordering.le ord3 ord2)
        (LE: Commit.le commit2 commit3)
        (WF: Commit.wf commit3):
    Commit.write_fence commit1 ord3 commit3.
  Proof.
    inv FENCE. econs; auto.
    - etrans; [|apply LE]. auto.
    - etrans; [|apply LE]. apply RA. etrans; eauto.
  Qed.

  Definition read_min
             loc ts released ord commit: Commit.t :=
    (Commit.mk commit.(Commit.rel)
               (Capability.join_if
                  (Ordering.le Ordering.acqrel ord)
                  released
                  (Capability.incr_rw loc ts commit.(Commit.cur)))
               (Capability.join
                  released
                  (Capability.incr_rw loc ts commit.(Commit.acq)))).

  Lemma read_min_spec
        loc ts released ord commit
        (UR: Time.le (commit.(Commit.cur).(Capability.ur) loc) ts)
        (RW: Ordering.le Ordering.relaxed ord -> Time.le (commit.(Commit.cur).(Capability.rw) loc) ts)
        (WF1: Commit.wf commit)
        (WF_RELEASED: Capability.wf released):
    Commit.read commit loc ts released ord (read_min loc ts released ord commit).
  Proof.
    unfold read_min. econs; tac.
    - econs; tac; try reflexivity.
      unfold Capability.join_if. condtac; tac.
      + rewrite <- Capability.join_r. tac.
      + rewrite <- Capability.join_r. tac.
    - unfold Capability.join_if. condtac; tac.
      + etrans; [|apply TimeMap.join_r].
        apply TimeMap.incr_ts.
      + apply TimeMap.incr_ts.
    - unfold Capability.join_if. condtac; tac.
    - econs; s.
      + apply WF1.
      + apply Capability.join_if_wf; auto.
        apply Capability.incr_rw_wf; auto.
        apply WF1.
      + apply Capability.join_wf; auto.
        apply Capability.incr_rw_wf; auto.
        apply WF1.
      + i. unfold Capability.join_if. condtac; tac.
        * etrans; [apply WF1|].
          rewrite <- Capability.join_r. tac.
        * etrans; [apply WF1|]. tac.
      + unfold Capability.join_if. condtac; tac.
        * etrans; [apply WF1|].
          rewrite <- Capability.join_r. tac.
        * etrans; [|apply Time.join_r].
          apply TimeMap.incr_ts.
        * etrans; [|apply Time.join_r].
          apply TimeMap.incr_ts.
        * etrans; [apply WF1|].
          rewrite <- Capability.join_r. tac.
        * etrans; [|apply Time.join_r].
          apply TimeMap.incr_ts.
        * etrans; [|apply Time.join_r].
          apply TimeMap.incr_ts.
  Qed.

  Lemma read_min_min
        loc ts released ord commit1 commit2
        (COMMIT2: Commit.read commit1 loc ts released ord commit2):
    Commit.le (read_min loc ts released ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold read_min. econs; tac.
    - apply MON.
    - apply MON.
    - rewrite RW2. apply WF.
    - apply MON.
    - etrans; eauto. apply WF.
    - etrans; eauto. etrans; apply WF.
  Qed.

  Definition write_min
             loc ts released commit: Commit.t :=
    (Commit.mk (LocFun.add loc released commit.(Commit.rel))
               (Capability.join released (Capability.incr_ur loc ts commit.(Commit.cur)))
               (Capability.join released (Capability.incr_ur loc ts commit.(Commit.acq)))).

  Lemma write_min_spec
        loc ts released ord commit
        (RELEASED: Time.le (released.(Capability.rw) loc) ts)
        (RW1: Time.le (commit.(Commit.cur).(Capability.rw) loc) ts)
        (REL1: Capability.le (commit.(Commit.rel) loc) released)
        (RA: Ordering.le Ordering.acqrel ord ->
             Capability.le commit.(Commit.cur) released /\
             Time.le ts (released.(Capability.rw) loc))
        (WF1: Commit.wf commit)
        (WF_RELEASED: Capability.wf released):
    Commit.write commit loc ts released ord (write_min loc ts released commit).
  Proof.
    econs; tac.
    - econs; tac.
      + unfold LocFun.add, LocFun.find. condtac; tac. reflexivity.
      + rewrite <- Capability.join_r. tac.
      + rewrite <- Capability.join_r. tac.
    - etrans; [|apply TimeMap.join_r].
      apply TimeMap.incr_ts.
    - unfold LocFun.add, LocFun.find.
      condtac; [|congruence]. reflexivity.
    - econs; try apply WF1; tac.
      + unfold LocFun.add, LocFun.find. condtac; auto. apply WF1.
      + apply Capability.join_wf; auto.
        apply Capability.incr_ur_wf. apply WF1.
      + apply Capability.join_wf; auto.
        apply Capability.incr_ur_wf. apply WF1.
      + unfold LocFun.add, LocFun.find. condtac; tac.
        rewrite <- Capability.join_r.
        rewrite <- Capability.incr_ur_le.
        apply WF1.
      + rewrite <- Capability.join_r.
        rewrite <- Capability.incr_ur_le.
        apply WF1.
      + etrans; [|apply TimeMap.join_r].
        apply TimeMap.incr_ts.
      + etrans; [|apply TimeMap.join_r].
        apply TimeMap.incr_ts.
      + etrans; [|apply TimeMap.join_r].
        apply TimeMap.incr_ts.
  Qed.

  Lemma write_min_min
        loc ts released ord commit1 commit2
        (COMMIT2: Commit.write commit1 loc ts released ord commit2):
    Commit.le (write_min loc ts released commit1) commit2.
  Proof.
    i. inv COMMIT2.
    econs; tac;
      (try by apply MON);
      (try by etrans; eauto; apply WF).
    - unfold LocFun.add, LocFun.find. condtac; tac.
      apply MON.
    - rewrite RW2. inv WF. etrans; apply CUR.
    - rewrite REL2. etrans; apply WF.
    - rewrite RW2. etrans; apply WF.
    - rewrite RW2. etrans; [apply WF|].
      inv WF. etrans; apply ACQ.
  Qed.

  Definition read_fence_min
             ord commit: Commit.t :=
    Commit.mk commit.(Commit.rel)
              (if Ordering.le Ordering.acqrel ord
               then commit.(Commit.acq)
               else commit.(Commit.cur))
              commit.(Commit.acq).

  Lemma read_fence_min_spec
        ord commit
        (WF1: Commit.wf commit):
    Commit.read_fence commit ord (read_fence_min ord commit).
  Proof.
    unfold read_fence_min. econs; tac; try apply WF1.
    - econs; tac; try reflexivity. apply WF1.
    - reflexivity.
    - econs; s; try apply WF1.
      + condtac; try apply WF1.
      + i. condtac; try apply WF1.
        etrans; apply WF1.
      + condtac; try apply WF1. reflexivity.
  Qed.

  Lemma read_fence_min_min
        ord commit1 commit2
        (WF1: Commit.wf commit1)
        (COMMIT2: Commit.read_fence commit1 ord commit2):
    Commit.le (read_fence_min ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold read_fence_min. econs; tac; try apply MON.
    condtac; try apply MON. eauto.
  Qed.

  Definition write_fence_min
             ord commit: Commit.t :=
    Commit.mk (fun loc =>
                 if Ordering.le Ordering.acqrel ord
                 then commit.(Commit.cur)
                 else (commit.(Commit.rel) loc))
              commit.(Commit.cur)
              commit.(Commit.acq).

  Lemma write_fence_min_spec
        ord commit
        (WF1: Commit.wf commit):
    Commit.write_fence commit ord (write_fence_min ord commit).
  Proof.
    econs; tac; try reflexivity.
    - econs; tac; try reflexivity.
      condtac; try reflexivity.
      apply WF1.
    - econs; tac; try apply WF1.
      + condtac; apply WF1.
      + condtac; try apply WF1. reflexivity.
  Qed.

  Lemma write_fence_min_min
        ord commit1 commit2
        (WF1: Commit.wf commit1)
        (COMMIT2: Commit.write_fence commit1 ord commit2):
    Commit.le (write_fence_min ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold write_fence_min. econs; tac; try apply MON.
    condtac; try apply MON. eauto.
  Qed.
End CommitFacts.

Ltac committac := CommitFacts.tac.
