Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.

Set Implicit Arguments.


Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    Cell.get ts (mem loc).

  Lemma ext
        lhs rhs
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. i.
    apply Cell.ext. i.
    apply EXT.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc to from msg
      (LHS: get loc to lhs = Some (from, msg)),
      get loc to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc to1 to2 from1 from2 msg1 msg2
                   (GET1: get loc to1 lhs = Some (from1, msg1))
                   (GET2: get loc to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2) /\
          (to1, to2) <> (Time.bot, Time.bot))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. exploit DISJOINT; eauto. i. des. splits.
    - symmetry. auto.
    - ii. inv H. congr.
  Qed.

  Lemma disjoint_get
        lhs rhs
        loc froml fromr to msgl msgr
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc to lhs = Some (froml, msgl))
        (RMSG: get loc to rhs = Some (fromr, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. i. des.
    destruct (Time.eq_dec to Time.bot).
    - subst. congr.
    - eapply x.
      + apply Interval.mem_ub. destruct (lhs loc).(Cell.WF).
        exploit VOLUME; eauto. i. des; auto. inv x1. congr.
      + apply Interval.mem_ub. destruct (rhs loc).(Cell.WF).
        exploit VOLUME; eauto. i. des; auto. inv x1. congr.
  Qed.

  Lemma disjoint_get'
        lhs rhs
        loc ts0 ts1 ts2 ts3 msgl msgr
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc ts2 lhs = Some (ts0, msgl))
        (RMSG: get loc ts3 rhs = Some (ts1, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. i. des.
    destruct (Time.le_lt_dec ts2 ts0).
    - destruct (lhs loc).(Cell.WF). exploit VOLUME; eauto. i. des.
      + inv x1. inv TS12.
      + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    - eapply x.
      + eapply Interval.mem_ub. auto.
      + econs; auto. left. auto.
  Qed.

  (* Inductive disjoint (lhs rhs:t): Prop := *)
  (* | disjoint_intro *)
  (*     (DISJOINT: forall loc, Cell.disjoint (lhs loc) (rhs loc)) *)
  (* . *)

  (* Global Program Instance disjoint_Symmetric: Symmetric disjoint. *)
  (* Next Obligation. *)
  (*   econs. ii. symmetry. apply H. *)
  (* Qed. *)

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof. unfold get. apply Cell.bot_get. Qed.

  Lemma bot_le mem: le bot mem.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in *. inv GET1.
  Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t)
             (LT: Time.lt from to): t :=
    (LocFun.add loc (Cell.singleton val released LT)
                (fun _ => Cell.bot)).

  Lemma singleton_get
        loc from to val released (LT:Time.lt from to)
        l t:
    get l t (singleton loc val released LT) =
    if Loc.eq_dec l loc
    then if Time.eq_dec t to
         then Some (from, Message.mk val released)
         else None
    else None.
  Proof.
    unfold get, singleton. unfold LocFun.add, LocFun.find.
    repeat condtac; subst.
    - rewrite Cell.singleton_get. condtac; [|congr]. auto.
    - rewrite Cell.singleton_get. condtac; [congr|]. auto.
    - apply Cell.bot_get.
  Qed.

  Definition init: t := fun _ => Cell.init.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists from val released, get loc (times loc) mem = Some (from, Message.mk val released).

  Inductive closed_capability (capability:Capability.t) (mem:t): Prop :=
  | closed_capability_intro
      (UR: closed_timemap capability.(Capability.ur) mem)
      (RW: closed_timemap capability.(Capability.rw) mem)
      (SC: closed_timemap capability.(Capability.sc) mem)
  .

  Definition inhabited (mem:t): Prop :=
    forall loc, get loc Time.bot mem = Some (Time.bot, Message.elt).

  Inductive closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to val released (MSG: get loc to mem = Some (from, Message.mk val released)),
          <<WF: Capability.wf released>> /\
          <<TS: Time.le (released.(Capability.rw) loc) to>> /\
          <<CLOSED: closed_capability released mem>>)
      (INHABITED: inhabited mem)
  .

  Lemma closed_timemap_bot
        mem
        (INHABITED: inhabited mem):
    closed_timemap TimeMap.bot mem.
  Proof. ii. esplits. eapply INHABITED. Qed.

  Lemma closed_capability_bot
        mem
        (INHABITED: inhabited mem):
    closed_capability Capability.bot mem.
  Proof. econs; apply closed_timemap_bot; auto. Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    unfold get, init, Cell.get, Cell.init in MSG. ss.
    unfold Cell.Raw.singleton in MSG. ss. apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
    splits; ss.
    - apply Capability.bot_wf.
    - refl.
    - unfold init. econs; s.
      + ii. esplits. ss.
      + ii. esplits. ss.
      + ii. esplits. ss.
  Qed.

  Inductive add (mem1:t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t): forall (mem2:t), Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from to val released r):
      add mem1 loc from to val released (LocFun.add loc r mem1)
  .

  Inductive split (mem1:t) (loc:Loc.t) (ts1 ts2 ts3:Time.t) (val2 val3:Const.t) (released2 released3:Capability.t): forall (mem2:t), Prop :=
  | split_intro
      r
      (SPLIT: Cell.split (mem1 loc) ts1 ts2 ts3 val2 val3 released2 released3 r):
      split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 (LocFun.add loc r mem1)
  .

  Inductive lower (mem1:t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released1 released2:Capability.t): forall (mem2:t), Prop :=
  | lower_intro
      r
      (LOWER: Cell.lower (mem1 loc) from to val released1 released2 r):
      lower mem1 loc from to val released1 released2 (LocFun.add loc r mem1)
  .

  Inductive remove (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (val1:Const.t) (released1:Capability.t): forall (mem2:t), Prop :=
  | remove_intro
      r
      (REMOVE: Cell.remove (mem1 loc) from1 to1 val1 released1 r):
      remove mem1 loc from1 to1 val1 released1 (LocFun.add loc r mem1)
  .

  Inductive future_imm (mem1 mem2:t): Prop :=
  | future_imm_add
      loc from to val released
      (ADD: add mem1 loc from to val released mem2)
      (CLOSED: closed_capability released mem2)
      (TS: Time.le (Capability.rw released loc) to)
  | future_imm_split
      loc ts1 ts2 ts3 val2 val3 released2 released3
      (SPLIT: split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2)
      (CLOSED: closed_capability released2 mem2)
      (TS: Time.le (Capability.rw released2 loc) ts2)
  | future_imm_lower
      loc from to val released1 released2
      (LOWER: lower mem1 loc from to val released1 released2 mem2)
      (CLOSED: closed_capability released2 mem2)
      (TS: Time.le (Capability.rw released2 loc) to)
  .

  Definition future := rtc future_imm.

  Inductive promise_kind :=
  | promise_kind_add
  | promise_kind_split (ts3:Time.t)
  | promise_kind_lower (released1:Capability.t)
  .

  Inductive promise
            (promises1 mem1:t)
            (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t)
            (promises2 mem2:t): forall (kind:promise_kind), Prop :=
  | promise_add
      (PROMISES: add promises1 loc from to val released promises2)
      (MEM: add mem1 loc from to val released mem2)
      (TS: Time.le (Capability.rw released loc) to):
      promise promises1 mem1 loc from to val released promises2 mem2 promise_kind_add
  | promise_update
      ts3 val3 released3
      (PROMISES: split promises1 loc from to ts3 val val3 released released3 promises2)
      (MEM: split mem1 loc from to ts3 val val3 released released3 mem2)
      (TS: Time.le (Capability.rw released loc) to):
      promise promises1 mem1 loc from to val released promises2 mem2 (promise_kind_split ts3)
  | promise_lower
      released0
      (PROMISES: lower promises1 loc from to val released0 released promises2)
      (MEM: lower mem1 loc from to val released0 released mem2)
      (TS: Time.le (Capability.rw released loc) to):
      promise promises1 mem1 loc from to val released promises2 mem2 (promise_kind_lower released0)
  .

  Inductive write
            (promises1 mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (val1:Const.t) (released1:Capability.t)
            (promises3 mem2:t) (kind:promise_kind): Prop :=
  | write_intro
      promises2
      (PROMISE: promise promises1 mem1 loc from1 to1 val1 released1 promises2 mem2 kind)
      (REMOVE: remove promises2 loc from1 to1 val1 released1 promises3)
  .


  (* Lemmas on add, split, lower & remove *)

  Lemma add_o
        mem2 mem1 loc from to val released
        l t
        (ADD: Memory.add mem1 loc from to val released mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, Message.mk val released)
    else Memory.get l t mem1.
  Proof.
    inv ADD. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.add_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.      

  Lemma split_o
        mem2 mem1 loc ts1 ts2 ts3 val2 val3 released2 released3
        l t
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, ts2)
    then Some (ts1, Message.mk val2 released2)
    else if loc_ts_eq_dec (l, t) (loc, ts3)
         then Some (ts2, Message.mk val3 released3)
         else Memory.get l t mem1.
  Proof.
    inv SPLIT. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.split_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.      

  Lemma lower_o
        mem2 mem1 loc from to val released1 released2
        l t
        (LOWER: Memory.lower mem1 loc from to val released1 released2 mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, Message.mk val released2)
    else Memory.get l t mem1.
  Proof.
    inv LOWER. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.lower_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma remove_o
        mem2 mem1 loc from to val released
        l t
        (REMOVE: Memory.remove mem1 loc from to val released mem2):
    Memory.get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else Memory.get l t mem1.
  Proof.
    inv REMOVE. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.remove_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma add_get0
        mem1 loc from1 to1 val1 released1 mem2
        (ADD: add mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv ADD. eapply Cell.add_get0; eauto.
  Qed.

  Lemma split_get0
        mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    <<GET2: get loc ts2 mem1 = None>> /\
    <<GET3: get loc ts3 mem1 = Some (ts1, Message.mk val3 released3)>>.
  Proof.
    inv SPLIT. eapply Cell.split_get0; eauto.
  Qed.

  Lemma lower_get0
        mem1 loc from to val released1 released2 mem2
        (LOWER: lower mem1 loc from to val released1 released2 mem2):
    get loc to mem1 = Some (from, Message.mk val released1).
  Proof.
    inv LOWER. eapply Cell.lower_get0; eauto.
  Qed.

  Lemma remove_get0
        mem1 loc from1 to1 val1 released1 mem2
        (REMOVE: remove mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem1 = Some (from1, Message.mk val1 released1).
  Proof.
    inv REMOVE. eapply Cell.remove_get0; eauto.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc from to val released
        (ADD: add mem1 loc from to val released mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma split_inhabited
        mem1 mem2 loc ts1 ts2 ts3 val2 val3 released2 released3
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite split_o; eauto. repeat (condtac; ss).
    - des. subst. inv SPLIT. inv SPLIT0. inv TS12.
    - des; subst; try congr. inv SPLIT. inv SPLIT0. inv TS23.
  Qed.

  Lemma lower_inhabited
        mem1 mem2 loc from to val released1 released2
        (LOWER: Memory.lower mem1 loc from to val released1 released2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. inv LOWER. inv LOWER0. inv TS.
  Qed.

  Lemma future_get
        loc from to val released mem1 mem2
        (LE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, Message.mk val released)):
    exists from' released',
      <<GET: get loc to mem2 = Some (from', Message.mk val released')>> /\
      <<FROM: Time.le from from'>> /\
      <<RELEASED: Capability.le released' released>>.
  Proof.
    revert from released GET. induction LE.
    { i. esplits; eauto; refl. }
    i. inv H.
    - revert IHLE. erewrite add_o; eauto.
      condtac; ss.
      + des. subst. erewrite add_get0 in GET; eauto. congr.
      + i. eapply IHLE; eauto.
    - revert IHLE. erewrite split_o; eauto.
      repeat condtac; ss.
      + des. subst. exploit split_get0; eauto. i. des. congr.
      + des; subst; try congr. exploit split_get0; eauto. i. des.
        rewrite GET3 in GET. inv GET.
        exploit IHLE; eauto. i. des. esplits; eauto.
        etrans; eauto. inv SPLIT. inv SPLIT0. left. auto.
      + i. eapply IHLE; eauto.
    - revert IHLE. erewrite lower_o; eauto.
      condtac; ss.
      + des. subst. erewrite lower_get0 in GET; try exact LOWER; eauto. inv GET.
        i. exploit IHLE; eauto. i. des. esplits; eauto.
        etrans; eauto. inv LOWER. inv LOWER0. auto.
      + i. eapply IHLE; eauto.
  Qed.      


  (* Lemmas on closedness *)

  Lemma join_closed_timemap
        lhs rhs mem
        (LHS: closed_timemap lhs mem)
        (RHS: closed_timemap rhs mem):
    closed_timemap (TimeMap.join lhs rhs) mem.
  Proof.
    ii. unfold TimeMap.join.
    destruct (Time.join_cases (lhs loc) (rhs loc)) as [X|X]; rewrite X.
    - apply LHS.
    - apply RHS.
  Qed.

  Lemma join_closed_capability
        lhs rhs mem
        (LHS: closed_capability lhs mem)
        (RHS: closed_capability rhs mem):
    closed_capability (Capability.join lhs rhs) mem.
  Proof.
    econs.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
  Qed.

  Lemma add_closed_timemap
        times
        mem1 loc from to val released mem2
        (CLOSED: closed_timemap times mem1)
        (ADD: add mem1 loc from to val released mem2):
    closed_timemap times mem2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. esplits; eauto.
  Qed.

  Lemma add_closed_capability
        capability
        mem1 loc from to val released mem2
        (CLOSED: closed_capability capability mem1)
        (ADD: add mem1 loc from to val released mem2):
    closed_capability capability mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply add_closed_timemap; eauto.
    - eapply add_closed_timemap; eauto.
    - eapply add_closed_timemap; eauto.
  Qed.

  Lemma add_closed
        mem1 loc from to val released mem2
        (CLOSED: closed mem1)
        (REL_CLOSED: closed_capability released mem2)
        (REL_TS: Time.le (Capability.rw released loc) to)
        (ADD: add mem1 loc from to val released mem2):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto. inv ADD. inv ADD0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply add_closed_capability; eauto.
    - eapply add_inhabited; eauto.
  Qed.

  Lemma split_closed_timemap
        times
        mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2
        (CLOSED: closed_timemap times mem1)
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    closed_timemap times mem2.
  Proof.
    ii. erewrite split_o; eauto. repeat condtac; ss.
    - des. subst. esplits; eauto.
    - guardH o. des. subst. esplits; eauto.
  Qed.

  Lemma split_closed_capability
        capability
        mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2
        (CLOSED: closed_capability capability mem1)
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    closed_capability capability mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
  Qed.

  Lemma split_closed
        mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2
        (CLOSED: closed mem1)
        (REL_CLOSED: closed_capability released2 mem2)
        (REL_TS: Time.le (Capability.rw released2 loc) ts2)
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. i. inv MSG.
        splits; eauto. inv SPLIT. inv SPLIT0. auto.
      + guardH o. des. subst. i. inv MSG.
        exploit split_get0; eauto. i. des. exploit CLOSED0; eauto. i. des.
        splits; eauto.
        eapply split_closed_capability; eauto.
      + guardH o. guardH o0. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply split_closed_capability; eauto.
    - eapply split_inhabited; eauto.
  Qed.

  Lemma lower_closed_timemap
        times
        mem1 loc from to val released1 released2 mem2
        (CLOSED: closed_timemap times mem1)
        (LOWER: lower mem1 loc from to val released1 released2 mem2):
    closed_timemap times mem2.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. esplits; eauto.
  Qed.

  Lemma lower_closed_capability
        capability
        mem1 loc from to val released1 released2 mem2
        (CLOSED: closed_capability capability mem1)
        (LOWER: lower mem1 loc from to val released1 released2 mem2):
    closed_capability capability mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply lower_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma lower_closed
        mem1 loc from to val released1 released2 mem2
        (CLOSED: closed mem1)
        (REL_CLOSED: closed_capability released2 mem2)
        (REL_TS: Time.le (Capability.rw released2 loc) to)
        (LOWER: lower mem1 loc from to val released1 released2 mem2):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite lower_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto. inv LOWER. inv LOWER0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply lower_closed_capability; eauto.
    - eapply lower_inhabited; eauto.
  Qed.

  Lemma promise_closed_timemap
        times
        promises1 mem1 loc from to val released promises2 mem2 kind
        (CLOSED: closed_timemap times mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    closed_timemap times mem2.
  Proof.
    inv PROMISE.
    - eapply add_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma promise_closed_capability
        capability
        promises1 mem1 loc from to val released promises2 mem2 kind
        (CLOSED: closed_capability capability mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    closed_capability capability mem2.
  Proof.
    inv PROMISE.
    - eapply add_closed_capability; eauto.
    - eapply split_closed_capability; eauto.
    - eapply lower_closed_capability; eauto.
  Qed.

  Lemma future_closed_timemap
        times mem1 mem2
        (CLOSED: closed_timemap times mem1)
        (FUTURE: future mem1 mem2):
    closed_timemap times mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    - eapply add_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma future_closed_capability
        capability mem1 mem2
        (CLOSED: closed_capability capability mem1)
        (FUTURE: future mem1 mem2):
    closed_capability capability mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    - eapply add_closed_capability; eauto.
    - eapply split_closed_capability; eauto.
    - eapply lower_closed_capability; eauto.
  Qed.

  Lemma future_closed
        mem1 mem2
        (CLOSED: closed mem1)
        (FUTURE: future mem1 mem2):
    closed mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i. apply IHFUTURE.
    inv H.
    - eapply add_closed; eauto.
    - eapply split_closed; eauto.
    - eapply lower_closed; eauto.
  Qed.

  Lemma singleton_closed_timemap
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.mk val released))
        (INHABITED: inhabited mem):
    closed_timemap (TimeMap.singleton loc to) mem.
  Proof.
    unfold TimeMap.singleton, LocFun.add, LocFun.find. ii. condtac.
    - subst. eauto.
    - apply closed_timemap_bot. auto.
  Qed.

  Lemma singleton_ur_closed_capability
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.mk val released))
        (INHABITED: inhabited mem):
    closed_capability (Capability.singleton_ur loc to) mem.
  Proof.
    econs; s.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_rw_closed_capability
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.mk val released))
        (INHABITED: inhabited mem):
    closed_capability (Capability.singleton_rw loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_sc_closed_capability
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.mk val released))
        (INHABITED: inhabited mem):
    closed_capability (Capability.singleton_sc loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
  Qed.


  (* Lemmas on promise & remove *)

  Lemma promise_get1
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: get l t mem1 = Some (f, Message.mk v r)):
    exists f' r',
      <<GET: get l t mem2 = Some (f', Message.mk v r')>> /\
      <<RELEASED: Capability.le r' r>>.
  Proof.
    inv PROMISE.
    - erewrite add_o; eauto. condtac; ss.
      + des. subst. erewrite add_get0 in GET; eauto. congr.
      + esplits; eauto. refl.
    - exploit split_get0; eauto. i. des.
      erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. rewrite GET3 in GET. inv GET.
        esplits; eauto. refl.
      + esplits; eauto. refl.
    - erewrite lower_o; eauto. condtac; ss.
      + des. subst. erewrite lower_get0 in GET; eauto. inv GET.
        esplits; eauto. inv MEM. inv LOWER. auto.
      + esplits; eauto. refl.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    get loc to promises2 = Some (from, Message.mk val released).
  Proof.
    inv PROMISE.
    - erewrite add_o; eauto. condtac; ss. des; congr.
    - erewrite split_o; eauto. repeat condtac; ss.
      + guardH o. des. subst. congr.
      + guardH o0. des; congr.
    - erewrite lower_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma promise_promises_get1
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: get l t promises1 = Some (f, Message.mk v r)):
    exists f' r',
      <<GET: get l t promises2 = Some (f', Message.mk v r')>> /\
      <<RELEASED: Capability.le r' r>>.
  Proof.
    inv PROMISE.
    - erewrite add_o; eauto. condtac; ss.
      + des. subst. erewrite add_get0 in GET; eauto. congr.
      + esplits; eauto. refl.
    - exploit split_get0; try exact PROMISES; eauto. i. des.
      erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. congr.
      + guardH o. des. subst. rewrite GET3 in GET. inv GET.
        esplits; eauto. refl.
      + esplits; eauto. refl.
    - erewrite lower_o; eauto. condtac; ss.
      + des. subst. erewrite lower_get0 in GET; eauto. inv GET.
        esplits; eauto. inv MEM. inv LOWER. auto.
      + esplits; eauto. refl.
  Qed.

  Lemma promise_future0
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (INHABITED1: inhabited mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<INHABITED2: inhabited mem2>>.
  Proof.
    inv PROMISE.
    - splits; eauto.
      + ii. revert LHS.
        erewrite add_o; eauto. erewrite (@add_o mem2); try exact MEM; eauto.
        condtac; ss. auto.
      + eapply add_inhabited; eauto.
    - splits; eauto.
      + ii. revert LHS.
        erewrite split_o; eauto. erewrite (@split_o mem2); try exact MEM; eauto.
        repeat condtac; ss. auto.
      + eapply split_inhabited; eauto.
    - splits; eauto.
      + ii. revert LHS.
        erewrite lower_o; eauto. erewrite (@lower_o mem2); try exact MEM; eauto.
        condtac; ss. auto.
      + eapply lower_inhabited; eauto.
  Qed.

  Lemma promise_future
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (CLOSED_REL: closed_capability released mem2)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    exploit promise_future0; try apply CLOSED1; eauto. i. des. splits; auto.
    - inv PROMISE.
      + eapply add_closed; eauto.
      + eapply split_closed; eauto.
      + eapply lower_closed; eauto.
    - econs 2; eauto. inv PROMISE.
      + econs 1; eauto.
      + econs 2; eauto.
      + econs 3; eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to val released promises2 mem2 ctx kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_PROMISES: le ctx mem2>>.
  Proof.
    exploit promise_future0; try apply PROMISE; try apply CLOSED1; eauto. i. des.
    inv PROMISE.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite add_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. splits.
          { inv MEM. inv ADD. eauto. }
          { ii. inv H. inv MEM. inv ADD. inv TO. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite add_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. inv MEM. inv ADD. eapply DISJOINT0; eauto.
        * apply Interval.mem_ub. auto.
        * apply Interval.mem_ub.
          destruct (mem1 loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
          inv x. inv TO.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite split_o; eauto. repeat condtac; ss.
        * des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [refl|].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS12. }
        * guardH o. des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [|refl].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS23. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { eapply split_get0. eauto. }
          i. des. eapply x.
          { inv MEM. inv SPLIT. econs. eauto. left. auto. }
          { apply Interval.mem_ub.
            destruct (mem1 loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS12.
          }
        * guardH o. des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { eapply split_get0. eauto. }
          i. des. eapply x.
          { apply Interval.mem_ub. inv MEM. inv SPLIT. etrans; eauto. }
          { apply Interval.mem_ub.
            destruct (ctx loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS23.
          }
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite lower_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. eapply DISJOINT0; eauto.
          eapply lower_get0. eauto.
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite lower_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply disjoint_get; eauto. eapply lower_get0. eauto.
  Qed.

  Lemma remove_future
        promises1 mem1 loc from to val released promises2
        (LE_PROMISES1: le promises1 mem1)
        (REMOVE: remove promises1 loc from to val released promises2):
    <<LE_PROMISES2: le promises2 mem1>>.
  Proof.
    ii. revert LHS. erewrite remove_o; eauto. condtac; ss. eauto.
  Qed.

  Lemma remove_disjoint
        promises1 mem1 loc from to val released promises2 ctx
        (LE_PROMISES1: le promises1 mem1)
        (REMOVE: remove promises1 loc from to val released promises2)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>>.
  Proof.
    econs. i. revert GET1. erewrite remove_o; eauto. condtac; ss.
    i. eapply DISJOINT; eauto.
  Qed.

  Lemma write_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        (PROMISES: le promises1 mem1)
        (MEM: inhabited mem1)
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind):
    get loc to mem2 = Some (from, Message.mk val released).
  Proof.
    inv WRITE.
    exploit promise_future0; try apply PROMISE; eauto. i. des.
    apply LE_PROMISES2. eapply promise_get2. eauto.
  Qed.

  Lemma write_future0
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (INHABITED1: inhabited mem1)
        (PROMISE: write promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<INHABITED2: inhabited mem2>>.
  Proof.
    inv PROMISE.
    hexploit promise_future0; eauto. i. des.
    hexploit remove_future; eauto.
  Qed.

  Lemma write_future
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (CLOSED2: closed_capability released mem2)
        (PROMISE: write promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv PROMISE.
    hexploit promise_future; eauto. i. des.
    hexploit remove_future; eauto.
  Qed.

  Lemma write_disjoint
        promises1 mem1 loc from to val released promises2 mem2 ctx kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_PROMISES: le ctx mem2>>.
  Proof.
    inv PROMISE.
    hexploit promise_future0; try apply PROMISE0; try apply CLOSED1; eauto. i. des.
    hexploit remove_future; try apply REMOVE; eauto. i. des.
    hexploit promise_disjoint; try apply PROMISE0; eauto. i. des.
    hexploit remove_disjoint; try apply REMOVE; eauto.
  Qed.

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (mem loc).

  Lemma max_ts_spec
        loc ts from msg mem
        (GET: get loc ts mem = Some (from, msg)):
    <<GET: exists from val released, get loc (max_ts loc mem) mem = Some (from, Message.mk val released)>> /\
    <<MAX: Time.le ts (max_ts loc mem)>>.
  Proof. eapply Cell.max_ts_spec; eauto. Qed.

  Lemma max_ts_spec2
        tm mem loc
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) (max_ts loc mem).
  Proof.
    exploit CLOSED. i. des.
    eapply max_ts_spec. eauto.
  Qed.

  Definition max_timemap (mem:t): TimeMap.t :=
    fun loc => max_ts loc mem.

  Lemma max_timemap_closed
        mem
        (INHABITED: inhabited mem):
    closed_timemap (max_timemap mem) mem.
  Proof.
    ii. specialize (INHABITED loc). des.
    eapply max_ts_spec. eauto.
  Qed.

  Lemma max_timemap_spec tm mem
        (TIMEMAP: closed_timemap tm mem)
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. specialize (INHABITED loc). des.
    exploit TIMEMAP. i. des.
    eapply max_ts_spec; eauto.
  Qed.

  Lemma max_timemap_spec' tm mem
        (TIMEMAP: forall loc, exists from to val released, Time.le (tm loc) to /\ get loc to mem = Some (from, Message.mk val released))
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. exploit TIMEMAP; eauto. i. des.
    etrans; eauto. eapply max_ts_spec; eauto.
  Qed.

  Lemma future_max_timemap
        mem1 mem2
        (CLOSED1: closed mem1)
        (CLOSED2: closed mem2)
        (FUTURE: future mem1 mem2):
    TimeMap.le (max_timemap mem1) (max_timemap mem2).
  Proof.
    apply max_timemap_spec; try apply CLOSED2.
    ii. exploit max_timemap_closed; try apply CLOSED1; eauto. i. des.
    exploit future_get; eauto. i. des.
    eauto.
  Qed.

  Definition max_capability (mem:t): Capability.t :=
    Capability.mk (max_timemap mem) (max_timemap mem) (max_timemap mem).

  Lemma max_capability_wf mem: Capability.wf (max_capability mem).
  Proof. econs. refl. refl. Qed.

  Lemma max_capability_closed
        mem
        (INHABITED: inhabited mem):
    closed_capability (max_capability mem) mem.
  Proof. econs; apply max_timemap_closed; auto. Qed.

  Lemma max_capability_spec tm mem
        (CAPABILITY: closed_capability tm mem)
        (INHABITED: inhabited mem):
    Capability.le tm (max_capability mem).
  Proof.
    econs; apply max_timemap_spec; try apply CAPABILITY; auto.
  Qed.

  Lemma add_max_timemap
        mem1 mem2 loc from to val released
        (ADD: add mem1 loc from to val released mem2)
        (INHABITED: inhabited mem1):
    max_timemap mem2 = TimeMap.join (max_timemap mem1) (TimeMap.singleton loc to).
  Proof.
    hexploit add_inhabited; eauto. i. des.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_timemap_closed; eauto. instantiate (1 := l). i. des.
      revert x0. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv x0. etrans; [|apply TimeMap.join_r].
        apply TimeMap.singleton_inv. refl.
      + i. etrans; [|apply TimeMap.join_l].
        eapply max_ts_spec; eauto.
    - apply TimeMap.join_spec.
      + apply max_timemap_spec; auto.
        eapply add_closed_timemap; eauto.
        apply max_timemap_closed. auto.
      + apply TimeMap.singleton_spec. eapply max_ts_spec.
        erewrite add_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma add_max_capability
        mem1 mem2 loc from to val released
        (ADD: add mem1 loc from to val released mem2)
        (INHABITED: inhabited mem1):
    max_capability mem2 = Capability.join (max_capability mem1) (Capability.singleton_ur loc to).
  Proof.
    apply Capability.ext; s.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
  Qed.

  Lemma closed_timemap_add
        loc from to val released mem tm
        (GET: get loc to mem = Some (from, Message.mk val released))
        (CLOSED: closed_timemap tm mem):
    closed_timemap (TimeMap.add loc to tm) mem.
  Proof.
    ii. unfold TimeMap.add. condtac.
    - subst. esplits; eauto.
    - apply CLOSED.
  Qed.

  Definition max_released
             mem loc ts :=
    let sc := TimeMap.join (max_timemap mem) (TimeMap.singleton loc ts) in
    let rw := TimeMap.add loc ts sc in
    Capability.mk rw rw sc.

  Lemma  max_released_wf
         mem1 loc to:
    Capability.wf (max_released mem1 loc to).
  Proof.
    econs; [refl|]. s.
    ii. unfold TimeMap.join, TimeMap.singleton, TimeMap.add, TimeMap.get, LocFun.add. condtac.
    - subst. etrans; [|apply Time.join_r]. refl.
    - refl.
  Qed.

  Lemma max_released_closed
        mem1 loc from to val released mem2
        (CLOSED: Memory.closed mem1)
        (ADD: add mem1 loc from to val released mem2):
    <<CLOSED: closed_capability (max_released mem1 loc to) mem2>> /\
    <<REL_TS: Time.le (Capability.rw (max_released mem1 loc to) loc) to>>.
  Proof.
    splits.
    - unfold max_released.
      erewrite <- add_max_timemap; eauto; cycle 1.
      { apply CLOSED. }
      hexploit add_inhabited; try apply CLOSED; eauto. i. des.
      econs; ss.
      + eapply closed_timemap_add.
        * erewrite add_o; eauto. condtac; ss. des; congr.
        * apply max_timemap_closed. auto.
      + eapply closed_timemap_add.
        * erewrite add_o; eauto. condtac; ss. des; congr.
        * apply max_timemap_closed. auto.
      + apply max_timemap_closed. auto.
    - ss. unfold TimeMap.add. condtac; [|congr]. refl.
  Qed.

  Lemma max_released_spec
        mem1 loc from to val released mem2
        (CLOSED: Memory.closed mem1)
        (ADD: add mem1 loc from to val released mem2)
        (REL_CLOSED: closed_capability released mem2)
        (REL_TS: Time.le (Capability.rw released loc) to):
    Capability.le released (max_released mem1 loc to).
  Proof.
    hexploit add_inhabited; try apply CLOSED; eauto. i. des.
    exploit max_capability_spec; eauto. i.
    erewrite add_max_capability in x0; try apply CLOSED; eauto.
    inv x0. ss.
    unfold max_released. econs; ss.
    - ii. unfold TimeMap.add. destruct (Loc.eq_dec loc0 loc); eauto.
      subst. etrans; [|exact REL_TS].
      inv ADD. inv ADD0. apply WF.
    - ii. unfold TimeMap.add. destruct (Loc.eq_dec loc0 loc); eauto.
      subst. auto.
  Qed.

  Lemma add_exists
        mem1 loc from to val released
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get loc to2 mem1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (WF: Capability.wf released):
    exists mem2, add mem1 loc from to val released mem2.
  Proof.
    exploit Cell.add_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        mem1 loc to val released
        (TS: Time.lt (max_ts loc mem1) to)
        (WF: Capability.wf released):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to val released mem2.
  Proof.
    eapply add_exists; eauto.
    i. exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO0. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 mem1 loc from to val released mem2
        (LE: le promises1 mem1)
        (ADD: add mem1 loc from to val released mem2):
    exists promises2, add promises1 loc from to val released promises2.
  Proof.
    inv ADD.
    exploit Cell.add_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma promise_add_exists
        promises1 mem1 loc from to val released mem2
        (LE_PROMISES1: le promises1 mem1)
        (ADD: add mem1 loc from to val released mem2)
        (REL: closed_capability released mem2)
        (TS: Time.le (Capability.rw released loc) to):
    exists promises2,
      promise promises1 mem1 loc from to val released promises2 mem2 promise_kind_add.
  Proof.
    exploit add_exists_le; eauto. i. des.
    eexists. econs 1; s; eauto.
  Qed.

  Lemma split_exists
        mem1 loc ts1 ts2 ts3 val2 val3 released2 released3
        (GET2: get loc ts3 mem1 = Some (ts1, Message.mk val3 released3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (REL_WF: Capability.wf released2):
    exists mem2, split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2.
  Proof.
    exploit Cell.split_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma split_exists_le
        promises1 mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 promises2
        (LE: le promises1 mem1)
        (SPLIT: split promises1 loc ts1 ts2 ts3 val2 val3 released2 released3 promises2):
    exists mem2, split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2.
  Proof.
    inv SPLIT.
    exploit Cell.split_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists
        mem1 loc from to val released1 released2
        (GET: get loc to mem1 = Some (from, Message.mk val released1))
        (TS: Time.lt from to)
        (REL_WF: Capability.wf released2)
        (REL_LE: Capability.le released2 released1):
    exists mem2, lower mem1 loc from to val released1 released2 mem2.
  Proof.
    exploit Cell.lower_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 mem1 loc from to val released1 released2 promises2
        (LE: le promises1 mem1)
        (LOWER: lower promises1 loc from to val released1 released2 promises2):
    exists mem2, lower mem1 loc from to val released1 released2 mem2.
  Proof.
    inv LOWER.
    exploit Cell.lower_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_same
        mem1 loc from to val released
        (GET: get loc to mem1 = Some (from, Message.mk val released))
        (TS: Time.lt from to)
        (REL_WF: Capability.wf released):
    lower mem1 loc from to val released released mem1.
  Proof.
    exploit lower_exists; eauto; try refl. i. des.
    cut (mem2 = mem1).
    { i. subst. auto. }
    apply ext. i.
    erewrite lower_o; eauto. condtac; ss. des. subst. auto.
  Qed.

  Lemma promise_exists_same
        promises1 mem1 loc from to val released
        (REL_WF: Capability.wf released)
        (LE: le promises1 mem1)
        (MEM: closed mem1)
        (GET: get loc to promises1 = Some (from, Message.mk val released))
        (LT: Time.lt from to):
    promise promises1 mem1 loc from to val released promises1 mem1 (promise_kind_lower released).
  Proof.
    exploit lower_exists_same; eauto. i.
    exploit lower_exists_same; try apply LE; eauto. i.
    econs; eauto.
    eapply MEM. eauto.
  Qed.

  Lemma remove_singleton
        loc from to val released (LT:Time.lt from to):
    remove (singleton loc val released LT) loc from to val released bot.
  Proof.
    assert (bot = LocFun.add loc Cell.bot (singleton loc val released LT)).
    { apply ext. i. rewrite bot_get.
      unfold get, LocFun.add, LocFun.find. condtac.
      - rewrite Cell.bot_get. auto.
      - unfold singleton, LocFun.add, LocFun.find. condtac; [congr|].
        rewrite Cell.bot_get. auto.
    }
    rewrite H. econs.
    unfold singleton, LocFun.add, LocFun.find. condtac; [|congr].
    eapply Cell.remove_singleton.
  Qed.

  Lemma remove_exists
        mem1 loc from to val released
        (GET: get loc to mem1 = Some (from, Message.mk val released)):
    exists mem2, remove mem1 loc from to val released mem2.
  Proof.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs. eauto.
  Qed.
End Memory.
