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
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module Commit <: JoinableType.
  Structure t_ := mk {
    rel: LocFun.t View.t;
    cur: View.t;
    acq: View.t;
  }.
  Definition t := t_.

  Definition bot: t := mk (LocFun.init View.bot) View.bot View.bot.

  Inductive wf (commit:t): Prop :=
  | wf_intro
      (REL: forall loc, View.wf (commit.(rel) loc))
      (CUR: View.wf commit.(cur))
      (ACQ: View.wf commit.(acq))
      (REL_CUR: forall loc, View.le (commit.(rel) loc) commit.(cur))
      (CUR_ACQ: View.le commit.(cur) commit.(acq))
  .

  Inductive closed (commit:t) (mem:Memory.t): Prop :=
  | closed_intro
      (REL: forall loc, Memory.closed_view (commit.(rel) loc) mem)
      (CUR: Memory.closed_view commit.(cur) mem)
      (ACQ: Memory.closed_view commit.(acq) mem)
  .

  Lemma bot_wf: wf bot.
  Proof.
    econs; i; econs; refl.
  Qed.

  Lemma bot_closed: closed bot Memory.init.
  Proof.
    econs; i; eapply Memory.closed_view_bot; apply Memory.init_closed.
  Qed.
  
  Lemma future_closed
        commit mem1 mem2
        (CLOSED: closed commit mem1)
        (FUTURE: Memory.future mem1 mem2):
    closed commit mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.future_closed_view; eauto.
  Qed.

  Lemma promise_closed
        commit1
        promises1 mem1 loc from to val released promises2 mem2 kind
        (CLOSED: closed commit1 mem1)
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
    closed commit1 mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.promise_closed_view; eauto.
  Qed.

  Definition eq := @eq t.

  Inductive le_ (lhs rhs:t): Prop :=
  | le_intro
      (REL: forall (loc:Loc.t), View.le (LocFun.find loc lhs.(rel)) (LocFun.find loc rhs.(rel)))
      (CUR: View.le lhs.(cur) rhs.(cur))
      (ACQ: View.le lhs.(acq) rhs.(acq))
  .
  Definition le := le_.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Definition join (lhs rhs:t): t :=
    mk (fun loc => View.join (lhs.(rel) loc) (rhs.(rel) loc))
       (View.join lhs.(cur) rhs.(cur))
       (View.join lhs.(acq) rhs.(acq)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join. f_equal.
    - apply LocFun.ext. i. apply View.join_comm.
    - apply View.join_comm.
    - apply View.join_comm.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. s. f_equal.
    - apply LocFun.ext. i. apply View.join_assoc.
    - apply View.join_assoc.
    - apply View.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    econs.
    - i. apply View.join_l.
    - apply View.join_l.
    - apply View.join_l.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof.
    econs.
    - i. apply View.join_r.
    - apply View.join_r.
    - apply View.join_r.
  Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS. econs.
    - i. apply View.join_spec; eauto.
    - apply View.join_spec; eauto.
    - apply View.join_spec; eauto.
  Qed.

  Inductive readable
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:View.t) (ord:Ordering.t): Prop :=
  | readable_intro
      (UR: Time.le (commit1.(cur).(View.pln) loc) ts)
      (RW: Ordering.le Ordering.relaxed ord ->
           Time.le (commit1.(cur).(View.rlx) loc) ts)
      (SC1: Ordering.le Ordering.seqcst ord -> Time.le (commit1.(cur).(View.sc) loc) ts)
      (SC2: Ordering.le Ordering.seqcst ord -> Time.le (released.(View.sc) loc) ts)
  .

  Definition read_commit
             (commit1:t) (loc:Loc.t) (ts:Time.t) (released:View.t) (ord:Ordering.t): t :=
    mk commit1.(rel)
       (View.join
          (View.join
             commit1.(cur)
             (View.singleton_rw loc ts))
          (if Ordering.le Ordering.acqrel ord then released else View.bot))
       (View.join
          (View.join
             commit1.(acq)
             (View.singleton_rw loc ts))
          (if Ordering.le Ordering.relaxed ord then released else View.bot)).

  Inductive writable
            (commit1:t) (sc1:TimeMap.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): Prop :=
  | writable_intro
      (TS: Time.lt (commit1.(cur).(View.rlx) loc) ts)
      (SC1: Ordering.le Ordering.seqcst ord -> Time.lt (commit1.(cur).(View.sc) loc) ts)
      (SC2: Ordering.le Ordering.seqcst ord -> Time.lt (sc1 loc) ts)
  .

  Definition write_commit
             (commit1:t) (sc1:TimeMap.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): t :=
    let cur2 := View.join
                  (View.join
                     commit1.(Commit.cur)
                     (View.singleton_ur loc ts))
                  (if Ordering.le Ordering.seqcst ord then View.mk TimeMap.bot TimeMap.bot sc1 else View.bot)
    in
    let acq2 := View.join
                  (View.join
                     commit1.(Commit.acq)
                     (View.singleton_ur loc ts))
                  (if Ordering.le Ordering.seqcst ord then View.mk TimeMap.bot TimeMap.bot sc1 else View.bot)
    in
    let rel2 := LocFun.add loc
                     (if Ordering.le Ordering.acqrel ord then cur2 else (commit1.(Commit.rel) loc))
                  commit1.(Commit.rel)
    in
    Commit.mk rel2 cur2 acq2.

  Definition write_sc
             (sc1:TimeMap.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): TimeMap.t :=
    TimeMap.join
      sc1
      (if Ordering.le Ordering.seqcst ord then TimeMap.singleton loc ts else TimeMap.bot).

  Definition read_fence_commit
             (commit1:t) (ord:Ordering.t): t :=
    Commit.mk commit1.(Commit.rel)
              (if Ordering.le Ordering.acqrel ord
               then commit1.(Commit.acq)
               else commit1.(Commit.cur))
              commit1.(Commit.acq).

  Definition write_fence_sc
             (commit1:t) (sc1:TimeMap.t) (ord:Ordering.t): TimeMap.t :=
    if Ordering.le Ordering.seqcst ord
    then TimeMap.join sc1 commit1.(Commit.cur).(View.sc)
    else sc1.

  Definition write_fence_commit
             (commit1:t) (sc1:TimeMap.t) (ord:Ordering.t): t :=
    let sc2 := write_fence_sc commit1 sc1 ord in
	  let cur2 := if Ordering.le Ordering.seqcst ord then View.mk sc2 sc2 sc2 else commit1.(Commit.cur)
	  in
	  let acq2 := View.join
                  commit1.(Commit.acq)
				          (if Ordering.le Ordering.seqcst ord then View.mk sc2 sc2 sc2 else View.bot)
	  in
	  let rel2 := fun l => if Ordering.le Ordering.acqrel ord then cur2 else (commit1.(Commit.rel) l)
    in
    Commit.mk rel2 cur2 acq2.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    destruct l, r. inv LR. inv RL. ss. f_equal.
    - apply LocFun.ext. i. apply View.antisym; auto.
    - apply View.antisym; auto.
    - apply View.antisym; auto.
  Qed.
End Commit.

Module CommitFacts.
  Lemma sc_le_view_le
        c tm
        (WF: View.wf c)
        (SC: TimeMap.le c.(View.sc) tm):
    View.le c (View.mk tm tm tm).
  Proof.
    econs; auto.
    - etrans; eauto. etrans; apply WF.
    - etrans; eauto. apply WF.
  Qed.

  Ltac tac :=
    repeat
      (try match goal with
           | [H: ?a <> ?a |- _] => congr
           | [H: Memory.closed ?mem |- Memory.inhabited ?mem] =>
             apply H
           | [|- View.le ?s ?s] =>
             refl
           | [|- TimeMap.le ?s ?s] =>
             refl
           | [|- View.le View.bot ?s] =>
             apply View.bot_spec
           | [|- TimeMap.le TimeMap.bot _] =>
             apply TimeMap.bot_spec
           | [|- Time.le (TimeMap.bot _) _] =>
             apply Time.bot_spec
           | [|- Time.le (LocFun.init Time.bot _) _] =>
             apply Time.bot_spec
           | [|- View.le ?s (View.join _ ?s)] =>
             apply View.join_r
           | [|- View.le ?s (View.join ?s _)] =>
             apply View.join_l
           | [|- TimeMap.le ?s (TimeMap.join _ ?s)] =>
             apply TimeMap.join_r
           | [|- TimeMap.le ?s (TimeMap.join ?s _)] =>
             apply TimeMap.join_l
           | [|- Memory.closed_view View.bot ?m] =>
             apply Memory.closed_view_bot
           | [|- Memory.closed_timemap TimeMap.bot ?m] =>
             apply Memory.closed_timemap_bot
           | [WF: Commit.wf ?c |- View.le (?c.(Commit.rel) ?l) ?c.(Commit.cur)] =>
             apply WF
           | [WF: Commit.wf ?c |- View.le (?c.(Commit.rel) ?l) ?c.(Commit.acq)] =>
             etrans; apply WF
           | [WF: Commit.wf ?c |- View.le ?c.(Commit.cur) ?c.(Commit.acq)] =>
             apply WF
           | [WF: View.wf ?c |- TimeMap.le ?c.(View.pln) ?c.(View.rlx)] =>
             apply WF
           | [WF: View.wf ?c |- TimeMap.le ?c.(View.pln) ?c.(View.sc)] =>
             etrans; apply WF
           | [WF: View.wf ?c |- TimeMap.le ?c.(View.rlx) ?c.(View.sc)] =>
             apply WF

           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.acqrel),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.unordered),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.unordered),
              H2: Ordering.le Ordering.relaxed ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.unordered),
              H2: is_true (Ordering.le Ordering.relaxed ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.unordered),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.acqrel),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: is_true (Ordering.le Ordering.seqcst ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o1 ?o2),
              H2: Ordering.le ?o0 ?o1 = true,
              H3: Ordering.le ?o0 ?o2 = false |- _] =>
               by destruct o1, o2; inv H1; inv H2; inv H3
           | [|- View.wf (View.mk ?tm ?tm ?tm)] =>
               by econs; refl
           | [|- View.wf (View.mk TimeMap.bot TimeMap.bot _)] =>
             econs; apply TimeMap.bot_spec

           | [|- View.le (View.join _ _) _] =>
             apply View.join_spec
           | [|- View.le (View.singleton_ur _ _) _] =>
             apply View.singleton_ur_spec
           | [|- View.le (View.singleton_rw _ _) _] =>
             apply View.singleton_rw_spec
           | [|- View.le (View.singleton_sc _ _) _] =>
             apply View.singleton_sc_spec
           | [|- TimeMap.le (TimeMap.singleton _ _) _] =>
             apply TimeMap.singleton_spec
           | [|- TimeMap.le (TimeMap.join _ _) _] =>
             apply TimeMap.join_spec
           | [|- Time.le (TimeMap.join _ _ _) _] =>
             apply Time.join_spec
           | [|- Time.lt (TimeMap.join _ _ _) _] =>
             apply TimeFacts.join_spec_lt

           | [|- Memory.closed_view (View.join _ _) _] =>
             eapply Memory.join_closed_view; eauto
           | [|- Memory.closed_view (View.singleton_ur _ _) _] =>
             eapply Memory.singleton_ur_closed_view; eauto
           | [|- Memory.closed_view (View.singleton_rw _ _) _] =>
             eapply Memory.singleton_rw_closed_view; eauto
           | [|- Memory.closed_view (View.singleton_sc _ _) _] =>
             eapply Memory.singleton_sc_closed_view; eauto
           | [|- Memory.closed_timemap (TimeMap.join _ _) _] =>
             eapply Memory.join_closed_timemap; eauto
           | [|- Memory.closed_timemap (TimeMap.singleton _ _) _] =>
             eapply Memory.singleton_closed_timemap; eauto

           | [H1: Memory.closed_view ?c ?m1,
              H2: Memory.future ?m1 ?m2 |-
              Memory.closed_view ?c ?m2] =>
             eapply Memory.future_closed_view; [exact H1|exact H2]
           | [H1: Memory.closed_timemap ?tm ?m1,
              H2: Memory.future ?m1 ?m2 |-
              Memory.closed_timemap ?tm ?m2] =>
             eapply Memory.future_closed_timemap; [exact H1|exact H2]

           | [|- View.wf (View.join _ _)] =>
             eapply View.join_wf; eauto
           | [|- View.wf (View.singleton_ur _ _)] =>
             eapply View.singleton_ur_wf; eauto
           | [|- View.wf (View.singleton_rw _ _)] =>
             eapply View.singleton_rw_wf; eauto
           | [|- View.wf (View.singleton_sc _ _)] =>
             eapply View.singleton_sc_wf; eauto
           | [|- View.wf View.bot] =>
             apply View.bot_wf

           | [H: Time.lt ?a ?b |- Time.le ?a ?b] =>
             left; apply H
           | [|- Time.le ?a ?a] =>
             refl
           | [|- View.le (View.mk ?tm1 ?tm1 ?tm1) (View.mk ?tm2 ?tm2 ?tm2)] =>
             apply View.timemap_le_le
           | [|- context[LocFun.find _ (LocFun.add _ _ _)]] =>
             rewrite LocFun.add_spec
           | [|- context[TimeMap.singleton ?l _ ?l]] =>
             unfold TimeMap.singleton
           | [|- context[LocFun.add ?l _ _ ?l]] =>
             unfold LocFun.add;
             match goal with
             | [|- context[Loc.eq_dec ?l ?l]] =>
               destruct (Loc.eq_dec l l); [|congr]
             end
           | [|- context[LocFun.find _ _]] =>
             unfold LocFun.find
           | [|- context[LocFun.add _ _ _]] =>
             unfold LocFun.add

           (* | [H: _ <> _ |- _] => inv H *)
           end; subst; ss; i).

  Ltac aggrtac :=
    repeat
      (tac;
       try match goal with
           | [|- Time.le ?t1 (TimeMap.singleton ?l ?t2 ?l)] =>
             unfold TimeMap.singleton, LocFun.add; condtac; [|congr]
           | [|- View.le _ (View.join _ _)] =>
             try (by rewrite <- View.join_l; aggrtac);
             try (by rewrite <- View.join_r; aggrtac)
           | [|- TimeMap.le _ (TimeMap.join _ _)] =>
             try (by rewrite <- TimeMap.join_l; aggrtac);
             try (by rewrite <- TimeMap.join_r; aggrtac)
           | [|- Time.le _ (TimeMap.join _ _ _)] =>
             try (by etrans; [|by apply Time.join_l]; aggrtac);
             try (by etrans; [|by apply Time.join_r]; aggrtac)

           | [|- View.le _ (View.mk ?tm ?tm ?tm)] =>
             apply sc_le_view_le
           end).

  Lemma read_commit_incr
        commit1 loc ts released ord:
    Commit.le commit1 (Commit.read_commit commit1 loc ts released ord).
  Proof.
    econs; tac.
    - rewrite <- ? View.join_l. refl.
    - rewrite <- ? View.join_l. refl.
  Qed.

  Lemma write_commit_incr
        commit1 sc1 loc ts ord
        (WF1: Commit.wf commit1):
    Commit.le commit1 (Commit.write_commit commit1 sc1 loc ts ord).
  Proof.
    econs; repeat (try condtac; aggrtac).
  Qed.

  Lemma write_sc_incr
        sc1 loc ts ord:
    TimeMap.le sc1 (Commit.write_sc sc1 loc ts ord).
  Proof.
    unfold Commit.write_sc. tac.
  Qed.

  Lemma read_fence_commit_incr
        commit1 ord
        (WF1: Commit.wf commit1):
    Commit.le commit1 (Commit.read_fence_commit commit1 ord).
  Proof.
    econs; tac. condtac; tac.
  Qed.

  Lemma write_fence_commit_incr
        commit1 sc1 ord
        (WF1: Commit.wf commit1):
    Commit.le commit1 (Commit.write_fence_commit commit1 sc1 ord).
  Proof.
    unfold Commit.write_fence_commit, Commit.write_fence_sc.
    econs; repeat (try condtac; aggrtac; try apply WF1).
    rewrite <- TimeMap.join_r. apply WF1.
  Qed.

  Lemma write_fence_sc_incr
        commit1 sc1 ord:
    TimeMap.le sc1 (Commit.write_fence_sc commit1 sc1 ord).
  Proof.
    unfold Commit.write_fence_sc. condtac; tac.
  Qed.

  Lemma readable_mon
        commit1 commit2 loc ts released1 released2 ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (REL: View.le released1 released2)
        (ORD: Ordering.le ord1 ord2)
        (READABLE: Commit.readable commit2 loc ts released2 ord2):
    Commit.readable commit1 loc ts released1 ord1.
  Proof.
    inv READABLE. econs; eauto.
    - etrans; try apply COMMIT; auto.
    - etrans; [apply COMMIT|]. apply RW. etrans; eauto.
    - etrans; [apply COMMIT|]. apply SC1. etrans; eauto.
    - etrans; [apply REL|]. apply SC2. etrans; eauto.
  Qed.

  Lemma writable_mon
        commit1 commit2 sc1 sc2 loc ts ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2)
        (WRITABLE: Commit.writable commit2 sc2 loc ts ord2):
    Commit.writable commit1 sc1 loc ts ord1.
  Proof.
    inv WRITABLE. econs; eauto.
    - eapply TimeFacts.le_lt_lt; try apply COMMIT; auto.
    - i. eapply TimeFacts.le_lt_lt; [apply COMMIT|]. apply SC1. etrans; eauto.
    - i. eapply TimeFacts.le_lt_lt; eauto. apply SC2. etrans; eauto.
  Qed.

  Lemma read_commit_mon
        commit1 commit2 loc ts released1 released2 ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (REL: View.le released1 released2)
        (WF2: Commit.wf commit2)
        (WF_REL2: View.wf released2)
        (ORD: Ordering.le ord1 ord2):
    Commit.le
      (Commit.read_commit commit1 loc ts released1 ord1)
      (Commit.read_commit commit2 loc ts released2 ord2).
  Proof.
    unfold Commit.read_commit.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply COMMIT|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  Qed.

  Lemma write_commit_mon
        commit1 commit2 sc1 sc2 loc ts ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (SC: TimeMap.le sc1 sc2)
        (WF2: Commit.wf commit2)
        (ORD: Ordering.le ord1 ord2):
    Commit.le
      (Commit.write_commit commit1 sc1 loc ts ord1)
      (Commit.write_commit commit2 sc2 loc ts ord2).
  Proof.
    unfold Commit.write_commit.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply COMMIT|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  Qed.

  Lemma write_sc_mon
        sc1 sc2 loc ts ord1 ord2
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2):
    TimeMap.le
      (Commit.write_sc sc1 loc ts ord1)
      (Commit.write_sc sc2 loc ts ord2).
  Proof.
    unfold Commit.write_sc. repeat condtac; aggrtac.
  Qed.

  Lemma read_fence_commit_mon
        commit1 commit2 ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (WF2: Commit.wf commit2)
        (ORD: Ordering.le ord1 ord2):
    Commit.le
      (Commit.read_fence_commit commit1 ord1)
      (Commit.read_fence_commit commit2 ord2).
  Proof.
    unfold Commit.read_fence_commit.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply COMMIT|aggrtac]);
      (try by rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply COMMIT).
  Qed.

  Lemma write_fence_commit_mon
        commit1 commit2 sc1 sc2 ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2)
        (WF1: Commit.wf commit1):
    Commit.le
      (Commit.write_fence_commit commit1 sc1 ord1)
      (Commit.write_fence_commit commit2 sc2 ord2).
  Proof.
    unfold Commit.write_fence_commit, Commit.write_fence_sc.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply COMMIT|aggrtac]);
      (try by rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply COMMIT);
      (try by apply WF1).
    - rewrite <- TimeMap.join_r. etrans; [apply WF1|]. apply COMMIT.
    - etrans; [apply WF1|]. apply COMMIT.
  Qed.

  Lemma write_fence_sc_mon
        commit1 commit2 sc1 sc2 ord1 ord2
        (COMMIT: Commit.le commit1 commit2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2):
    TimeMap.le
      (Commit.write_fence_sc commit1 sc1 ord1)
      (Commit.write_fence_sc commit2 sc2 ord2).
  Proof.
    unfold Commit.write_fence_sc.
    repeat (condtac; aggrtac);
      (try by etrans; [apply COMMIT|aggrtac]);
      (try rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply COMMIT).
  Qed.

  Lemma write_sc_acqrel
        sc loc ts ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    Commit.write_sc sc loc ts ordw = sc.
  Proof.
    unfold Commit.write_sc. condtac; tac.
    apply TimeMap.antisym; tac.
  Qed.

  Lemma write_commit_acqrel
        commit sc1 sc2 loc ts ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    Commit.write_commit commit sc1 loc ts ordw = Commit.write_commit commit sc2 loc ts ordw.
  Proof.
    unfold Commit.write_commit.
    apply Commit.antisym; repeat (condtac; tac; try refl).
  Qed.

  Lemma write_fence_sc_acqrel
        commit sc ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    Commit.write_fence_sc commit sc ordw = sc.
  Proof.
    unfold Commit.write_fence_sc. condtac; tac.
  Qed.

  Lemma write_fence_commit_acqrel
        commit sc1 sc2 ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    Commit.write_fence_commit commit sc1 ordw = Commit.write_fence_commit commit sc2 ordw.
  Proof.
    unfold Commit.write_fence_commit.
    apply Commit.antisym; repeat (condtac; tac; try refl).
  Qed.

  Lemma read_future
        loc from to val released ord commit mem
        (MEM: Memory.closed mem)
        (WF_COMMIT: Commit.wf commit)
        (CLOSED_COMMIT: Commit.closed commit mem)
        (RELEASED: View.wf released)
        (GET: Memory.get loc to mem = Some (from, Message.mk val released)):
    <<WF_COMMIT: Commit.wf (Commit.read_commit commit loc to released ord)>> /\
    <<CLOSED_COMMIT: Commit.closed (Commit.read_commit commit loc to released ord) mem>>.
  Proof.
    splits; tac.
    - econs; repeat (try condtac; tac);
      try by rewrite <- ? View.join_l; apply WF_COMMIT.
      + apply TimeMap.singleton_inv.
        rewrite <- TimeMap.join_l. tac.
      + apply TimeMap.singleton_inv.
        rewrite <- TimeMap.join_l. tac.
      + destruct ord; inv COND; inv COND0.
    - inv MEM. exploit CLOSED; eauto. i. des.
      econs; tac; try apply CLOSED_COMMIT.
      + condtac; tac.
      + condtac; tac.
  Qed.

  Lemma write_future
        loc from to val releasedm ord commit sc mem
        (MEM: Memory.closed mem)
        (WF_COMMIT: Commit.wf commit)
        (CLOSED_COMMIT: Commit.closed commit mem)
        (CLOSED_SC: Memory.closed_timemap sc mem)
        (GET: Memory.get loc to mem = Some (from, Message.mk val releasedm)):
    <<WF_COMMIT: Commit.wf (Commit.write_commit commit sc loc to ord)>> /\
    <<CLOSED_COMMIT: Commit.closed (Commit.write_commit commit sc loc to ord) mem>> /\
    <<CLOSED_SC: Memory.closed_timemap (Commit.write_sc sc loc to ord) mem>>.
  Proof.
    splits; tac.
    - econs; tac; try apply WF_COMMIT.
      + unfold LocFun.add, LocFun.find. repeat condtac; tac; try apply WF_COMMIT.
      + condtac; tac; try apply WF_COMMIT.
      + condtac; tac.
      + unfold LocFun.add, LocFun.find.
        repeat condtac; tac; rewrite <- ? View.join_l; apply WF_COMMIT.
      + repeat condtac; tac; rewrite <- ? View.join_l; apply WF_COMMIT.
      + condtac; tac.
      + apply TimeMap.singleton_inv. rewrite <- TimeMap.join_l. tac.
    - econs; tac; (try by apply CLOSED_COMMIT).
      + unfold LocFun.add. repeat condtac; tac; (try by apply CLOSED_COMMIT).
        econs; tac; apply MEM.
      + condtac; tac. econs; tac.
      + condtac; tac. econs; tac.
    - unfold Commit.write_sc. condtac; tac.
  Qed.

  Lemma read_fence_future
        ord commit mem
        (WF_COMMIT: Commit.wf commit)
        (CLOSED_COMMIT: Commit.closed commit mem):
    <<WF_COMMIT: Commit.wf (Commit.read_fence_commit commit ord)>> /\
    <<CLOSED_COMMIT: Commit.closed (Commit.read_fence_commit commit ord) mem>>.
  Proof.
    splits.
    - econs; tac; try apply WF_COMMIT.
      + condtac; try apply WF_COMMIT.
      + condtac; try apply WF_COMMIT.
        etrans; apply WF_COMMIT.
      + condtac; try apply WF_COMMIT. refl.
    - econs; tac; try apply CLOSED_COMMIT.
      condtac; try apply CLOSED_COMMIT.
  Qed.

  Lemma write_fence_future
        ord commit sc mem
        (MEM: Memory.closed mem)
        (WF_COMMIT: Commit.wf commit)
        (CLOSED_COMMIT: Commit.closed commit mem)
        (CLOSED_SC: Memory.closed_timemap sc mem):
    <<WF_COMMIT: Commit.wf (Commit.write_fence_commit commit sc ord)>> /\
    <<CLOSED_COMMIT: Commit.closed (Commit.write_fence_commit commit sc ord) mem>> /\
    <<CLOSED_SC: Memory.closed_timemap (Commit.write_fence_sc commit sc ord) mem>>.
  Proof.
    splits; tac.
    - econs; tac; try apply WF_COMMIT.
      + repeat condtac; tac; try apply WF_COMMIT.
      + repeat condtac; tac; try apply WF_COMMIT.
      + repeat condtac; tac.
      + repeat (try condtac; aggrtac; try apply WF_COMMIT).
        unfold Commit.write_fence_sc. condtac; tac.
        rewrite <- TimeMap.join_r. apply WF_COMMIT.
      + repeat condtac; tac; rewrite <- View.join_l; apply WF_COMMIT.
    - econs; tac; try apply CLOSED_COMMIT.
      + unfold Commit.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_COMMIT.
        econs; tac; try apply CLOSED_COMMIT.
      + unfold Commit.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_COMMIT.
        econs; tac; try apply CLOSED_COMMIT.
      + unfold Commit.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_COMMIT.
        econs; tac; try apply CLOSED_COMMIT.
    - unfold Commit.write_fence_sc.
      condtac; tac; try apply CLOSED_COMMIT.
  Qed.
End CommitFacts.

Ltac viewtac := CommitFacts.tac.
Ltac aggrtac := CommitFacts.aggrtac.
