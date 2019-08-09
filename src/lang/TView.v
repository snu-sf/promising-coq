Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.

Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module TView <: JoinableType.
  Structure t_ := mk {
    rel: LocFun.t View.t;
    cur: View.t;
    acq: View.t;
  }.
  Definition t := t_.

  Definition bot: t := mk (LocFun.init View.bot) View.bot View.bot.

  Inductive wf (tview:t): Prop :=
  | wf_intro
      (REL: forall loc, View.wf (tview.(rel) loc))
      (CUR: View.wf tview.(cur))
      (ACQ: View.wf tview.(acq))
      (REL_CUR: forall loc, View.le (tview.(rel) loc) tview.(cur))
      (CUR_ACQ: View.le tview.(cur) tview.(acq))
  .

  Inductive closed (tview:t) (mem:Memory.t): Prop :=
  | closed_intro
      (REL: forall loc, Memory.closed_view (tview.(rel) loc) mem)
      (CUR: Memory.closed_view tview.(cur) mem)
      (ACQ: Memory.closed_view tview.(acq) mem)
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
        tview mem1 mem2
        (CLOSED: closed tview mem1)
        (FUTURE: Memory.future mem1 mem2):
    closed tview mem2.
  Proof.
    inv CLOSED. econs; i; eapply Memory.future_closed_view; eauto.
  Qed.

  Lemma promise_closed
        tview1
        promises1 mem1 loc from to val released promises2 mem2 kind
        (CLOSED: closed tview1 mem1)
        (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
    closed tview1 mem2.
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
            (view1:View.t) (loc:Loc.t) (ts:Time.t) (released:option View.t) (ord:Ordering.t): Prop :=
  | readable_intro
      (PLN: Time.le (view1.(View.pln) loc) ts)
      (RLX: Ordering.le Ordering.relaxed ord ->
            Time.le (view1.(View.rlx) loc) ts)
  .

  Definition read_tview
             (tview1:t) (loc:Loc.t) (ts:Time.t) (released:option View.t) (ord:Ordering.t): t :=
    mk tview1.(rel)
       (View.join
          (View.join
             tview1.(cur)
             (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc ts))
          (if Ordering.le Ordering.acqrel ord then released.(View.unwrap) else View.bot))
       (View.join
          (View.join
             tview1.(acq)
             (View.singleton_ur_if (Ordering.le Ordering.relaxed ord) loc ts))
          (if Ordering.le Ordering.relaxed ord then released.(View.unwrap) else View.bot)).

  Inductive writable
            (view1:View.t) (sc1:TimeMap.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): Prop :=
  | writable_intro
      (TS: Time.lt (view1.(View.rlx) loc) ts)
  .

  Definition write_tview
             (tview1:t) (sc1:TimeMap.t) (loc:Loc.t) (ts:Time.t) (ord:Ordering.t): t :=
    let cur2 := View.join
                  tview1.(cur)
                  (View.singleton_ur loc ts)
    in
    let acq2 := View.join
                  tview1.(acq)
                  (View.singleton_ur loc ts)
    in
    let rel2 := LocFun.add loc
                     (if Ordering.le Ordering.acqrel ord then cur2 else View.join (tview1.(rel) loc) (View.singleton_ur loc ts))
                  tview1.(rel)
    in
    mk rel2 cur2 acq2.

  Definition write_released tview sc loc ts releasedm ord :=
    if Ordering.le Ordering.relaxed ord
    then Some (View.join
                 releasedm.(View.unwrap)
                 ((write_tview tview sc loc ts ord).(rel) loc))
    else None.

  Definition read_fence_tview
             (tview1:t) (ord:Ordering.t): t :=
    mk tview1.(rel)
                (if Ordering.le Ordering.acqrel ord
                 then tview1.(acq)
                 else tview1.(cur))
                tview1.(acq).

  Definition write_fence_sc
             (tview1:t) (sc1:TimeMap.t) (ord:Ordering.t): TimeMap.t :=
    if Ordering.le Ordering.seqcst ord
    then TimeMap.join sc1 tview1.(cur).(View.rlx)
    else sc1.

  Definition write_fence_tview
             (tview1:t) (sc1:TimeMap.t) (ord:Ordering.t): t :=
    let sc2 := write_fence_sc tview1 sc1 ord in
	  let cur2 := if Ordering.le Ordering.seqcst ord then View.mk sc2 sc2 else tview1.(cur)
	  in
	  let acq2 := View.join
                  tview1.(acq)
				          (if Ordering.le Ordering.seqcst ord then View.mk sc2 sc2 else View.bot)
	  in
	  let rel2 := fun l => if Ordering.le Ordering.acqrel ord then cur2 else (tview1.(rel) l)
    in
    mk rel2 cur2 acq2.

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
End TView.

Module TViewFacts.
  Lemma rlx_le_view_le
        c tm
        (WF: View.wf c)
        (SC: TimeMap.le c.(View.rlx) tm):
    View.le c (View.mk tm tm).
  Proof.
    econs; auto.
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
           | [WF: TView.wf ?c |- View.le (?c.(TView.rel) ?l) ?c.(TView.cur)] =>
             apply WF
           | [WF: TView.wf ?c |- View.le (?c.(TView.rel) ?l) ?c.(TView.acq)] =>
             etrans; apply WF
           | [WF: TView.wf ?c |- View.le ?c.(TView.cur) ?c.(TView.acq)] =>
             apply WF
           | [WF: View.wf ?c |- TimeMap.le ?c.(View.pln) ?c.(View.rlx)] =>
             apply WF
           | [WF: View.opt_wf ?released |- View.wf (View.unwrap ?released)] =>
             apply View.unwrap_opt_wf
           | [WF: View.opt_le ?rel1 ?rel2 |- View.le (View.unwrap ?rel1) (View.unwrap ?rel2)] =>
             apply View.unwrap_opt_le
           | [WF: Memory.closed_opt_view ?view ?mem |- Memory.closed_view ?view.(View.unwrap) ?mem] =>
             apply Memory.unwrap_closed_opt_view
           | [|- View.opt_wf None] =>
             econs
           | [|- Memory.closed_opt_view None ?mem] =>
             econs

           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.relaxed),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.acqrel),
              H2: Ordering.le Ordering.seqcst ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.plain),
              H2: Ordering.le Ordering.acqrel ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.plain),
              H2: Ordering.le Ordering.relaxed ?o = true |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.plain),
              H2: is_true (Ordering.le Ordering.relaxed ?o) |- _] =>
               by destruct o; inv H1; inv H2
           | [H1: is_true (Ordering.le ?o Ordering.plain),
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
           | [|- View.wf (View.mk ?tm ?tm)] =>
               by econs; refl
           | [|- View.wf (View.mk TimeMap.bot TimeMap.bot _)] =>
             econs; apply TimeMap.bot_spec

           | [|- View.le (View.join _ _) _] =>
             apply View.join_spec
           | [|- View.le (View.singleton_ur _ _) _] =>
             apply View.singleton_ur_spec
           | [|- View.le (View.singleton_rw _ _) _] =>
             apply View.singleton_rw_spec
           | [|- View.le (View.singleton_ur_if _ _ _) _] =>
             apply View.singleton_ur_if_spec
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
           | [|- Memory.closed_view (View.singleton_ur_if _ _ _) _] =>
             eapply Memory.singleton_ur_if_closed_view; eauto
           | [|- Memory.closed_timemap (TimeMap.join _ _) _] =>
             eapply Memory.join_closed_timemap; eauto
           | [|- Memory.closed_timemap (TimeMap.singleton _ _) _] =>
             eapply Memory.singleton_closed_timemap; eauto

           | [H1: Memory.closed_view ?c ?m1,
              H2: Memory.future ?m1 ?m2 |-
              Memory.closed_view ?c ?m2] =>
             eapply Memory.future_closed_view; [exact H1|exact H2]
           | [H1: Memory.closed_opt_view ?c ?m1,
              H2: Memory.future ?m1 ?m2 |-
              Memory.closed_opt_view ?c ?m2] =>
             eapply Memory.future_closed_opt_view; [exact H1|exact H2]
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
           | [|- View.wf (View.singleton_ur_if _ _ _)] =>
             eapply View.singleton_ur_if_wf; eauto
           | [|- View.wf View.bot] =>
             apply View.bot_wf

           | [H: Time.lt ?a ?b |- Time.le ?a ?b] =>
             left; apply H
           | [|- Time.le ?a ?a] =>
             refl
           | [|- View.le (View.mk ?tm1 ?tm1) (View.mk ?tm2 ?tm2)] =>
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

           | [|- View.le _ (View.mk ?tm ?tm)] =>
             apply rlx_le_view_le
           end).

  Lemma read_tview_incr
        tview1 loc ts released ord:
    TView.le tview1 (TView.read_tview tview1 loc ts released ord).
  Proof.
    econs; tac.
    - rewrite <- ? View.join_l. refl.
    - rewrite <- ? View.join_l. refl.
  Qed.

  Lemma write_tview_incr
        tview1 sc1 loc ts ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.write_tview tview1 sc1 loc ts ord).
  Proof.
    econs; repeat (try condtac; aggrtac).
  Qed.

  Lemma read_fence_tview_incr
        tview1 ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.read_fence_tview tview1 ord).
  Proof.
    econs; tac. condtac; tac.
  Qed.

  Lemma write_fence_tview_incr
        tview1 sc1 ord
        (WF1: TView.wf tview1):
    TView.le tview1 (TView.write_fence_tview tview1 sc1 ord).
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; aggrtac; try apply WF1).
    - etrans; [apply WF1|]. tac.
  Qed.

  Lemma write_fence_sc_incr
        tview1 sc1 ord:
    TimeMap.le sc1 (TView.write_fence_sc tview1 sc1 ord).
  Proof.
    unfold TView.write_fence_sc. condtac; tac.
  Qed.

  Lemma readable_mon
        view1 view2 loc ts released1 released2 ord1 ord2
        (VIEW: View.le view1 view2)
        (REL: View.opt_le released1 released2)
        (ORD: Ordering.le ord1 ord2)
        (READABLE: TView.readable view2 loc ts released2 ord2):
    TView.readable view1 loc ts released1 ord1.
  Proof.
    inv READABLE. econs; eauto.
    - etrans; try apply VIEW; auto.
    - etrans; [apply VIEW|]. apply RLX. etrans; eauto.
  Qed.

  Lemma writable_mon
        view1 view2 sc1 sc2 loc ts ord1 ord2
        (VIEW: View.le view1 view2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2)
        (WRITABLE: TView.writable view2 sc2 loc ts ord2):
    TView.writable view1 sc1 loc ts ord1.
  Proof.
    inv WRITABLE. econs; eauto.
    - eapply TimeFacts.le_lt_lt; try apply VIEW; auto.
  Qed.

  Lemma read_tview_mon
        tview1 tview2 loc ts released1 released2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (REL: View.opt_le released1 released2)
        (WF2: TView.wf tview2)
        (WF_REL2: View.opt_wf released2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_tview tview1 loc ts released1 ord1)
      (TView.read_tview tview2 loc ts released2 ord2).
  Proof.
    unfold TView.read_tview, View.singleton_ur_if.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  Qed.

  Lemma write_tview_mon
        tview1 tview2 sc1 sc2 loc ts ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
        (WF2: TView.wf tview2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.write_tview tview1 sc1 loc ts ord1)
      (TView.write_tview tview2 sc2 loc ts ord2).
  Proof.
    unfold TView.write_tview, View.singleton_ur_if.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  Qed.

  Lemma write_released_mon
        tview1 tview2 sc1 sc2 loc ts releasedm1 releasedm2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
        (WF2: TView.wf tview2)
        (RELM_LE: View.opt_le releasedm1 releasedm2)
        (RELM_WF2: View.opt_wf releasedm2)
        (ORD: Ordering.le ord1 ord2):
    View.opt_le
      (TView.write_released tview1 sc1 loc ts releasedm1 ord1)
      (TView.write_released tview2 sc2 loc ts releasedm2 ord2).
  Proof.
    unfold TView.write_released, TView.write_tview.
    destruct (Ordering.le Ordering.relaxed ord1) eqn:ORD1,
             (Ordering.le Ordering.relaxed ord2) eqn:ORD2; tac;
      try econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try by rewrite <- ? TimeMap.join_l; apply RELM);
      (try by rewrite <- TimeMap.join_r, <- ? TimeMap.join_l; etrans; [apply TVIEW|apply WF2]);
      (try apply WF2).
  Qed.

  Lemma read_fence_tview_mon
        tview1 tview2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (WF2: TView.wf tview2)
        (ORD: Ordering.le ord1 ord2):
    TView.le
      (TView.read_fence_tview tview1 ord1)
      (TView.read_fence_tview tview2 ord2).
  Proof.
    unfold TView.read_fence_tview.
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply TVIEW).
  Qed.

  Lemma write_fence_tview_mon
        tview1 tview2 sc1 sc2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2)
        (WF1: TView.wf tview1):
    TView.le
      (TView.write_fence_tview tview1 sc1 ord1)
      (TView.write_fence_tview tview2 sc2 ord2).
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (condtac; aggrtac).
    all: try by etrans; [apply TVIEW|aggrtac].
    all: try by apply WF1.
    all: try by rewrite <- ? View.join_r; aggrtac;
      (rewrite <- ? TimeMap.join_r; apply TVIEW);
      (try by apply WF1).
    - rewrite <- TimeMap.join_r. etrans; [apply WF1|]. apply TVIEW.
    - etrans; [apply WF1|]. apply TVIEW.
  Qed.

  Lemma write_fence_sc_mon
        tview1 tview2 sc1 sc2 ord1 ord2
        (TVIEW: TView.le tview1 tview2)
        (SC: TimeMap.le sc1 sc2)
        (ORD: Ordering.le ord1 ord2):
    TimeMap.le
      (TView.write_fence_sc tview1 sc1 ord1)
      (TView.write_fence_sc tview2 sc2 ord2).
  Proof.
    unfold TView.write_fence_sc.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try rewrite <- ? View.join_r; aggrtac;
       rewrite <- ? TimeMap.join_r; apply TVIEW).
  Qed.

  Lemma write_tview_acqrel
        tview sc1 sc2 loc ts ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    TView.write_tview tview sc1 loc ts ordw = TView.write_tview tview sc2 loc ts ordw.
  Proof.
    unfold TView.write_tview.
    apply TView.antisym; repeat (condtac; tac; try refl).
  Qed.

  Lemma write_fence_sc_acqrel
        tview sc ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    TView.write_fence_sc tview sc ordw = sc.
  Proof.
    unfold TView.write_fence_sc. condtac; tac.
  Qed.

  Lemma write_fence_tview_acqrel
        tview sc1 sc2 ordw
        (ORDW: Ordering.le ordw Ordering.acqrel):
    TView.write_fence_tview tview sc1 ordw = TView.write_fence_tview tview sc2 ordw.
  Proof.
    unfold TView.write_fence_tview.
    apply TView.antisym; repeat (condtac; tac; try refl).
  Qed.

  Lemma write_fence_tview_strong_relaxed
        tview sc o (ORD: Ordering.le o Ordering.strong_relaxed):
    TView.write_fence_tview tview sc o = tview.
  Proof.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    destruct tview. ss.
    f_equal; repeat (condtac; aggrtac); try by destruct o.
    rewrite View.join_comm, View.join_bot_l. ss.
  Qed.

  Lemma read_future1
        loc from to val released ord tview mem
        (WF_TVIEW: TView.wf tview)
        (RELEASED: View.opt_wf released)
        (GET: Memory.get loc to mem = Some (from, Message.mk val released)):
    <<WF_TVIEW: TView.wf (TView.read_tview tview loc to released ord)>>.
  Proof.
    econs; repeat (try condtac; tac);
        try by rewrite <- ? View.join_l; apply WF_TVIEW.
    - apply TimeMap.singleton_inv.
      rewrite <- TimeMap.join_l. tac.
    - apply TimeMap.singleton_inv.
      rewrite <- TimeMap.join_l. tac.
    - destruct ord; inv COND; inv COND0.
  Qed.

  Lemma read_future
        loc from to val released ord tview mem
        (MEM: Memory.closed mem)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem)
        (RELEASED: View.opt_wf released)
        (GET: Memory.get loc to mem = Some (from, Message.mk val released)):
    <<WF_TVIEW: TView.wf (TView.read_tview tview loc to released ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.read_tview tview loc to released ord) mem>>.
  Proof.
    splits; try eapply read_future1; eauto.
    inv MEM. exploit CLOSED; eauto. i. des.
    econs; tac; try apply CLOSED_TVIEW; condtac; tac.
  Qed.

  Lemma op_closed_tview
        mem1 tview1 sc1 loc from to val released ord mem2 kind
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (OP: Memory.op mem1 loc from to val released mem2 kind):
    TView.closed (TView.write_tview tview1 sc1 loc to ord) mem2.
  Proof.
    hexploit Memory.op_future0; eauto; try by tac. i. des.
    unfold TView.write_tview.
    econs; repeat (try condtac; tac);
      (try by eapply Memory.op_closed_view; eauto; apply CLOSED2);
      (try by econs; tac; eapply Memory.op_closed_timemap; eauto; apply CLOSED0);
      (try by eapply Memory.op_get2; eauto).
  Qed.

  Lemma op_closed_sc
        mem1 sc1 loc from to val released mem2 kind
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (OP: Memory.op mem1 loc from to val released mem2 kind):
    Memory.closed_timemap sc1 mem2.
  Proof.
    hexploit Memory.op_future0; eauto; try by tac. i. des.
    eapply Memory.op_closed_timemap; eauto.
  Qed.

  Lemma op_closed_released
        mem1 tview1 sc1 loc from to val releasedm released ord mem2 kind
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (CLOSED3: Memory.closed_opt_view releasedm mem1)
        (OP: Memory.op mem1 loc from to val released mem2 kind):
    Memory.closed_opt_view (TView.write_released tview1 sc1 loc to releasedm ord) mem2.
  Proof.
    hexploit Memory.op_future0; eauto; try by tac. i. des.
    unfold TView.write_released. condtac; econs.
    apply Memory.join_closed_view.
    - eapply Memory.op_closed_view; eauto.
      apply Memory.unwrap_closed_opt_view; tac.
    - eapply op_closed_tview; eauto.
  Qed.

  Lemma get_closed_tview
        mem1 tview1 sc1 loc from to val released ord
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (GET: Memory.get loc to mem1 = Some (from, Message.mk val released)):
    TView.closed (TView.write_tview tview1 sc1 loc to ord) mem1.
  Proof.
    econs; tac; (try by apply CLOSED2).
    - unfold LocFun.add. repeat condtac; tac; (try by apply CLOSED2).
  Qed.

  Lemma get_closed_released
        mem1 tview1 sc1 loc from to val releasedm released ord
        (CLOSED0: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (CLOSED2: TView.closed tview1 mem1)
        (CLOSED3: Memory.closed_opt_view releasedm mem1)
        (GET: Memory.get loc to mem1 = Some (from, Message.mk val released)):
    Memory.closed_opt_view (TView.write_released tview1 sc1 loc to releasedm ord) mem1.
  Proof.
    unfold TView.write_released. condtac; econs.
    apply Memory.join_closed_view.
    - apply Memory.unwrap_closed_opt_view; tac.
    - eapply get_closed_tview; eauto.
  Qed.

  Lemma write_future0
        loc to releasedm ord tview sc
        (WF_TVIEW: TView.wf tview)
        (WF_RELM: View.opt_wf releasedm):
    <<WF_TVIEW: TView.wf (TView.write_tview tview sc loc to ord)>> /\
    <<WF_RELEASED: View.opt_wf (TView.write_released tview sc loc to releasedm ord)>>.
  Proof.
    splits; tac.
    - econs; tac; try apply WF_TVIEW.
      + unfold LocFun.add, LocFun.find. repeat condtac; tac; try apply WF_TVIEW.
      + repeat condtac; aggrtac; rewrite <- ? View.join_l; try apply WF_TVIEW.
      + repeat condtac; tac; rewrite <- ? View.join_l; apply WF_TVIEW.
    - unfold TView.write_released. condtac; econs. repeat (try condtac; aggrtac; try apply WF_TVIEW).
  Qed.

  Lemma write_future
        loc from to val releasedm ord tview sc mem1 mem2 kind
        (MEM: Memory.closed mem1)
        (WF_TVIEW: TView.wf tview)
        (WF_RELM: View.opt_wf releasedm)
        (CLOSED_TVIEW: TView.closed tview mem1)
        (CLOSED_SC: Memory.closed_timemap sc mem1)
        (CLOSED_RELM: Memory.closed_opt_view releasedm mem1)
        (OP: Memory.op mem1 loc from to val
                       (TView.write_released tview sc loc to releasedm ord)
                       mem2 kind):
    <<WF_TVIEW: TView.wf (TView.write_tview tview sc loc to ord)>> /\
    <<WF_RELEASED: View.opt_wf (TView.write_released tview sc loc to releasedm ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.write_tview tview sc loc to ord) mem2>> /\
    <<CLOSED_SC: Memory.closed_timemap sc mem2>> /\
    <<CLOSED_RELEASED: Memory.closed_opt_view (TView.write_released tview sc loc to releasedm ord) mem2>>.
  Proof.
    exploit write_future0; eauto. i. des. splits; eauto.
    - eapply op_closed_tview; eauto.
    - eapply op_closed_sc; eauto.
    - eapply op_closed_released; eauto.
  Qed.

  Lemma write_future_fulfill
        loc from to val releasedm released ord tview sc mem
        (MEM: Memory.closed mem)
        (WF_TVIEW: TView.wf tview)
        (WF_RELM: View.opt_wf releasedm)
        (CLOSED_TVIEW: TView.closed tview mem)
        (CLOSED_SC: Memory.closed_timemap sc mem)
        (CLOSED_RELM: Memory.closed_opt_view releasedm mem)
        (GET: Memory.get loc to mem = Some (from, Message.mk val released)):
    <<WF_TVIEW: TView.wf (TView.write_tview tview sc loc to ord)>> /\
    <<WF_RELEASED: View.opt_wf (TView.write_released tview sc loc to releasedm ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.write_tview tview sc loc to ord) mem>> /\
    <<CLOSED_SC: Memory.closed_timemap sc mem>> /\
    <<CLOSED_RELEASED: Memory.closed_opt_view (TView.write_released tview sc loc to releasedm ord) mem>>.
  Proof.
    exploit write_future0; eauto. i. des. splits; eauto.
    - eapply get_closed_tview; eauto.
    - eapply get_closed_released; eauto.
  Qed.

  Lemma read_fence_future
        ord tview mem
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem):
    <<WF_TVIEW: TView.wf (TView.read_fence_tview tview ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.read_fence_tview tview ord) mem>>.
  Proof.
    splits.
    - econs; tac; try apply WF_TVIEW.
      + condtac; try apply WF_TVIEW.
      + condtac; try apply WF_TVIEW.
        etrans; apply WF_TVIEW.
      + condtac; try apply WF_TVIEW. refl.
    - econs; tac; try apply CLOSED_TVIEW.
      condtac; try apply CLOSED_TVIEW.
  Qed.

  Lemma write_fence_future
        ord tview sc mem
        (MEM: Memory.closed mem)
        (WF_TVIEW: TView.wf tview)
        (CLOSED_TVIEW: TView.closed tview mem)
        (CLOSED_SC: Memory.closed_timemap sc mem):
    <<WF_TVIEW: TView.wf (TView.write_fence_tview tview sc ord)>> /\
    <<CLOSED_TVIEW: TView.closed (TView.write_fence_tview tview sc ord) mem>> /\
    <<CLOSED_SC: Memory.closed_timemap (TView.write_fence_sc tview sc ord) mem>>.
  Proof.
    splits; tac.
    - econs; tac; try apply WF_TVIEW.
      + repeat condtac; tac; try apply WF_TVIEW.
      + repeat condtac; tac; try apply WF_TVIEW.
      + repeat condtac; tac.
      + repeat (try condtac; aggrtac; try apply WF_TVIEW).
        unfold TView.write_fence_sc. condtac; tac.
        rewrite <- TimeMap.join_r. apply WF_TVIEW.
      + repeat condtac; tac; rewrite <- View.join_l; apply WF_TVIEW.
    - econs; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
        econs; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
        econs; tac; try apply CLOSED_TVIEW.
      + unfold TView.write_fence_sc.
        repeat condtac; tac; try apply CLOSED_TVIEW.
        econs; tac; try apply CLOSED_TVIEW.
    - unfold TView.write_fence_sc.
      condtac; tac; try apply CLOSED_TVIEW.
  Qed.
End TViewFacts.

Ltac viewtac := TViewFacts.tac.
Ltac aggrtac := TViewFacts.aggrtac.
