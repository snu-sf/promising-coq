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
    current: Capability.t;
    released: LocFun.t Capability.t;
    acquirable: Capability.t;
  }.
  Definition t := t_.

  Definition elt: t := mk Capability.elt (LocFun.init Capability.elt) Capability.elt.

  Inductive wf (commit:t): Prop :=
  | wf_intro
      (CURRENT: Capability.wf commit.(current))
      (RELEASED: forall loc, Capability.wf (commit.(released) loc))
      (ACQUIRABLE: Capability.wf commit.(acquirable))
  .

  Inductive closed (commit:t) (mem:Memory.t): Prop :=
  | closed_intro
      (CURRENT: Memory.closed_capability commit.(current) mem)
      (RELEASED: forall loc, Memory.closed_capability (commit.(released) loc) mem)
      (ACQUIRABLE: Memory.closed_capability commit.(acquirable) mem)
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
      (CURRENT: Capability.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Capability.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Capability.le lhs.(acquirable) rhs.(acquirable))
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
    mk (Capability.join lhs.(current) rhs.(current))
       (fun loc => Capability.join (lhs.(released) loc) (rhs.(released) loc))
       (Capability.join lhs.(acquirable) rhs.(acquirable)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join. f_equal.
    - apply Capability.join_comm.
    - extensionality loc. apply Capability.join_comm.
    - apply Capability.join_comm.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. s. f_equal.
    - apply Capability.join_assoc.
    - extensionality loc. apply Capability.join_assoc.
    - apply Capability.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    econs.
    - apply Capability.join_l.
    - i. apply Capability.join_l.
    - apply Capability.join_l.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof.
    econs.
    - apply Capability.join_r.
    - i. apply Capability.join_r.
    - apply Capability.join_r.
  Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS. econs.
    - apply Capability.join_spec; eauto.
    - i. apply Capability.join_spec; eauto.
    - apply Capability.join_spec; eauto.
  Qed.

  Inductive read
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Capability.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_intro
      (MONOTONE: le commit1 commit2)
      (ACQUIRABLE: Capability.le released commit2.(acquirable))
      (UR1: Time.le (commit1.(current).(Capability.ur) loc) ts)
      (RW1: Ordering.le Ordering.relaxed ord ->
            Time.le (commit1.(current).(Capability.rw) loc) ts)
      (RW2: Time.le ts (commit2.(current).(Capability.rw) loc))
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le released commit2.(current))
      (WF_RELEASED: Capability.wf released)
      (WF: Commit.wf commit2)
  .

  Inductive write
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Capability.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_intro
      (MONOTONE: le commit1 commit2)
      (RELEASED: Time.le (released.(Capability.rw) loc) ts)
      (RW1: Time.le (commit1.(current).(Capability.rw) loc) ts)
      (RW2: Time.le ts (commit2.(current).(Capability.ur) loc))
      (REL1: Capability.le (commit1.(Commit.released) loc) released)
      (REL2: Capability.le released (commit2.(Commit.released) loc))
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le commit1.(Commit.current) released /\
           Time.le ts (released.(Capability.rw) loc))
      (WF_RELEASED: Capability.wf released)
      (WF: Commit.wf commit2)
  .

  Inductive read_fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_fence_intro
      (MONOTONE: le commit1 commit2)
      (RA: Ordering.le Ordering.acqrel ord ->
           Capability.le commit1.(Commit.acquirable) commit2.(Commit.current))
      (WF: Commit.wf commit2)
  .

  Inductive write_fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_fence_intro
      (MONOTONE: le commit1 commit2)
      (RLX: Ordering.le Ordering.relaxed ord -> TimeMap.le commit1.(current).(Capability.rw) commit2.(current).(Capability.ur))
      (RA: Ordering.le Ordering.acqrel ord ->
           forall loc, TimeMap.le commit1.(current).(Capability.rw) (commit2.(released) loc).(Capability.ur) /\
                  Capability.le commit1.(Commit.current) (commit2.(Commit.released) loc))
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
    exists ts msg,
      Time.le (commit1.(Commit.current).(Capability.rw) loc) ts /\
      Memory.get loc ts mem = Some msg.
  Proof.
    inversion CLOSED. inv CURRENT.
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
    - i. splits.
      + etrans; [apply LE|]. apply RA. auto.
      + etrans; [apply LE|]. apply RA. auto.
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
    - etrans; [|apply LE].
      apply RLX. etrans; eauto.
    - i. exploit RA.
      { etrans; eauto. }
      i. des. splits.
      + etrans; [|apply LE]. eauto.
      + etrans; [|apply LE]. eauto.
  Qed.

  Definition read_min
             loc ts released ord commit: Commit.t :=
    (Commit.mk (Capability.join_if
                  (Ordering.le Ordering.acqrel ord)
                  released
                  (Capability.incr_rw loc ts commit.(Commit.current)))
               commit.(Commit.released)
               (Capability.join released commit.(Commit.acquirable))).

  Lemma read_min_spec
        loc ts released ord commit
        (UR: Time.le (commit.(Commit.current).(Capability.ur) loc) ts)
        (RW: Ordering.le Ordering.relaxed ord -> Time.le (commit.(Commit.current).(Capability.rw) loc) ts)
        (WF1: Commit.wf commit)
        (WF_RELEASED: Capability.wf released):
    Commit.read commit loc ts released ord (read_min loc ts released ord commit).
  Proof.
    unfold read_min. econs; tac.
    - econs; tac; try reflexivity.
      unfold Capability.join_if. condtac; tac.
      etrans; [|apply Capability.join_r]. tac.
    - unfold Capability.join_if. condtac; tac.
      + etrans; [|apply TimeMap.join_r].
        apply TimeMap.incr_ts.
      + apply TimeMap.incr_ts.
    - unfold Capability.join_if. condtac; tac.
    - econs; s.
      + apply Capability.join_if_wf; auto.
        apply Capability.incr_rw_wf; auto.
        apply WF1.
      + apply WF1.
      + apply Capability.join_wf; auto.
        apply WF1.
  Qed.

  Lemma read_min_min
        loc ts released ord commit1 commit2
        (COMMIT2: Commit.read commit1 loc ts released ord commit2)
        (WF2: Commit.wf commit2):
    Commit.le (read_min loc ts released ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold read_min. econs; tac.
    - apply MONOTONE.
    - rewrite RW2. apply WF2.
    - apply MONOTONE.
    - apply MONOTONE.
  Qed.

  Definition write_min
             loc ts released commit: Commit.t :=
    (Commit.mk (Capability.incr_ur loc ts commit.(Commit.current))
               (LocFun.add loc released commit.(Commit.released))
               commit.(Commit.acquirable)).

  Lemma write_min_spec
        loc ts released ord commit
        (RELEASED: Time.le (released.(Capability.rw) loc) ts)
        (RW1: Time.le (commit.(Commit.current).(Capability.rw) loc) ts)
        (REL1: Capability.le (commit.(Commit.released) loc) released)
        (RA: Ordering.le Ordering.acqrel ord ->
             Capability.le commit.(Commit.current) released /\
             Time.le ts (released.(Capability.rw) loc))
        (WF1: Commit.wf commit)
        (WF_RELEASED: Capability.wf released):
    Commit.write commit loc ts released ord (write_min loc ts released commit).
  Proof.
    econs; tac.
    - econs; tac; try reflexivity.
      unfold LocFun.add, LocFun.find.
      condtac; tac. reflexivity.
    - apply TimeMap.incr_ts.
    - unfold LocFun.add, LocFun.find.
      condtac; [|congruence]. reflexivity.
    - econs; try apply WF1; tac.
      + apply Capability.incr_ur_wf. apply WF1.
      + unfold LocFun.add, LocFun.find.
        condtac; tac. apply WF1.
  Qed.

  Lemma write_min_min
        loc ts released ord commit1 commit2
        (COMMIT2: Commit.write commit1 loc ts released ord commit2)
        (WF2: Commit.wf commit2):
    Commit.le (write_min loc ts released commit1) commit2.
  Proof.
    i. inv COMMIT2. econs; tac; try apply MONOTONE.
    - rewrite RW2. apply WF2.
    - rewrite RW2. etrans; apply WF2.
    - unfold LocFun.add, LocFun.find. condtac; tac.
      apply MONOTONE.
  Qed.

  Definition read_fence_min
             ord commit: Commit.t :=
    Commit.mk (Capability.join_if
                 (Ordering.le Ordering.acqrel ord)
                 commit.(Commit.acquirable)
                 commit.(Commit.current))
              commit.(Commit.released)
              commit.(Commit.acquirable).

  Lemma read_fence_min_spec
        ord commit
        (WF1: Commit.wf commit):
    Commit.read_fence commit ord (read_fence_min ord commit).
  Proof.
    unfold read_fence_min. econs; tac.
    - econs; tac; try reflexivity.
      unfold Capability.join_if. condtac; tac. reflexivity.
    - rewrite H. s. apply Capability.join_l.
    - econs; try apply WF1. s.
      apply Capability.join_if_wf; apply WF1.
  Qed.

  Lemma read_fence_min_min
        ord commit1 commit2
        (COMMIT2: Commit.read_fence commit1 ord commit2):
    Commit.le (read_fence_min ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold read_fence_min. econs; tac; try apply MONOTONE.
  Qed.

  Definition write_fence_min
             ord commit: Commit.t :=
    Commit.mk (Capability.join_if
                 (Ordering.le Ordering.relaxed ord)
                 (Capability.mk commit.(Commit.current).(Capability.rw)
                                commit.(Commit.current).(Capability.rw)
                                commit.(Commit.current).(Capability.sc))
                 commit.(Commit.current))
              (fun loc =>
                 Capability.join_if
                   (Ordering.le Ordering.acqrel ord)
                   (Capability.mk commit.(Commit.current).(Capability.rw)
                                  commit.(Commit.current).(Capability.rw)
                                  commit.(Commit.current).(Capability.sc))
                   (commit.(Commit.released) loc))
              commit.(Commit.acquirable).

  Lemma write_fence_min_spec
        ord commit
        (WF1: Commit.wf commit):
    Commit.write_fence commit ord (write_fence_min ord commit).
  Proof.
    econs; tac.
    - econs; tac; try reflexivity.
      + unfold Capability.join_if. condtac; tac. reflexivity.
      + unfold LocFun.find.
        unfold Capability.join_if. condtac; tac. reflexivity.
    - unfold Capability.join_if. condtac; tac.
      apply TimeMap.join_l.
    - unfold Capability.join_if. condtac; tac. splits.
      + apply TimeMap.join_l.
      + etrans; [|apply Capability.join_l].
        econs; try reflexivity.
        apply WF1.
    - econs; tac; try apply WF1.
      + apply Capability.join_if_wf; try apply WF1.
        econs; s; try apply WF1. reflexivity.
      + apply Capability.join_if_wf; try apply WF1.
        econs; try apply WF1. reflexivity.
  Qed.        

  Lemma write_fence_min_min
        ord commit1 commit2
        (COMMIT2: Commit.write_fence commit1 ord commit2):
    Commit.le (write_fence_min ord commit1) commit2.
  Proof.
    inv COMMIT2. unfold write_fence_min. econs; tac; try apply MONOTONE.
    - econs; tac; try apply MONOTONE. eauto.
    - unfold LocFun.find.
      unfold Capability.join_if. condtac; tac; try apply MONOTONE.
      econs; s.
      + apply RA. auto.
      + apply RA. auto.
      + apply RA. auto.
  Qed.
End CommitFacts.

Ltac committac := CommitFacts.tac.
