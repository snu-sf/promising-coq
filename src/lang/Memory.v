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

Set Implicit Arguments.


Module TimeMap <: JoinableType.
  Definition t := Loc.t -> Time.t.
  Definition elt: t := fun _ => Time.elt.

  Definition eq := @eq t.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (lhs loc) (rhs loc).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. refl. Qed.
  Next Obligation. ii. etrans; eauto. Qed.

  Definition get (loc:Loc.t) (c:t) := c loc.

  Definition join (lhs rhs:t): t :=
    fun loc => Time.join (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. apply LocFun.ext. i. apply Time.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply LocFun.ext. i. apply Time.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof. ii. apply Time.join_l. Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. ii. apply Time.join_r. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof. unfold join. ii. apply Time.join_spec; auto. Qed.

  Definition incr loc ts c :=
    LocFun.add loc (Time.join (c loc) ts) c.

  Lemma incr_mon loc ts c1 c2
        (LE: le c1 c2):
    le (incr loc ts c1) (incr loc ts c2).
  Proof.
    ii. unfold incr, LocFun.add, LocFun.find. condtac; ss.
    apply Time.join_spec.
    - etrans; [apply LE|]. apply Time.join_l.
    - apply Time.join_r.
  Qed.

  Lemma incr_le loc ts c:
    le c (incr loc ts c).
  Proof.
    unfold incr, LocFun.add, LocFun.find. ii. condtac; ss.
    - subst. apply Time.join_l.
    - refl.
  Qed.

  Lemma incr_ts loc ts c:
    Time.le ts (get loc (incr loc ts c)).
  Proof.
    unfold get, incr, LocFun.add, LocFun.find.
    rewrite Loc.eq_dec_eq. apply Time.join_r.
  Qed.

  Lemma incr_spec loc ts c1 c2
        (LE: le c1 c2)
        (TS: Time.le ts (get loc c2)):
    TimeMap.le (incr loc ts c1) c2.
  Proof.
    ii. unfold get, incr, LocFun.add, LocFun.find. condtac; ss.
    subst. apply Time.join_spec; auto.
  Qed.

  Lemma incr_nop
        loc ts tm
        (TS: Time.le ts (tm loc)):
    incr loc ts tm = tm.
  Proof.
    unfold incr. apply LocFun.ext. i.
    rewrite LocFun.add_spec. condtac; auto. subst.
    unfold LocFun.find. unfold Time.join. condtac; auto.
    apply Time.le_lteq in TS. des; auto.
    exploit TimeFacts.lt_le_lt; eauto. i.
    apply Time.lt_strorder in x0. inv x0.
  Qed.

  Lemma le_join_l l r
        (LE: le r l):
    join l r = l.
  Proof.
    apply LocFun.ext. i.
    unfold join, Time.join, LocFun.find. condtac; auto.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma le_join_r l r
        (LE: le l r):
    join l r = r.
  Proof.
    apply LocFun.ext. i.
    unfold join, Time.join, LocFun.find. condtac; auto.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
  Qed.
End TimeMap.

Module Capability <: JoinableType.
  Structure t_ := mk {
    ur: TimeMap.t;
    rw: TimeMap.t;
    sc: TimeMap.t;
  }.
  Definition t := t_.

  Inductive wf (capability:t): Prop :=
  | wf_intro
      (UR_RW: TimeMap.le capability.(ur) capability.(rw))
      (RW_SC: TimeMap.le capability.(rw) capability.(sc))
  .

  Definition elt: t := mk TimeMap.elt TimeMap.elt TimeMap.elt.

  Lemma elt_wf: wf elt.
  Proof. econs; refl. Qed.

  Definition eq := @eq t.

  Inductive le_ (lhs rhs:t): Prop :=
  | le_intro
      (UR: TimeMap.le lhs.(ur) rhs.(ur))
      (RW: TimeMap.le lhs.(rw) rhs.(rw))
      (SC: TimeMap.le lhs.(sc) rhs.(sc))
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
    mk (TimeMap.join lhs.(ur) rhs.(ur))
       (TimeMap.join lhs.(rw) rhs.(rw))
       (TimeMap.join lhs.(sc) rhs.(sc)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. unfold join. f_equal; apply TimeMap.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. ss. f_equal.
    - apply TimeMap.join_assoc.
    - apply TimeMap.join_assoc.
    - apply TimeMap.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof. econs; apply TimeMap.join_l. Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. econs; apply TimeMap.join_r. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS.
    econs; apply TimeMap.join_spec; eauto.
  Qed.

  Lemma join_wf
        lhs rhs
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (join lhs rhs).
  Proof.
    econs.
    - apply TimeMap.join_spec.
      + etrans; [apply LHS|]. apply TimeMap.join_l.
      + etrans; [apply RHS|]. apply TimeMap.join_r.
    - apply TimeMap.join_spec.
      + etrans; [apply LHS|]. apply TimeMap.join_l.
      + etrans; [apply RHS|]. apply TimeMap.join_r.
  Qed.

  Definition join_if (cond:bool) (a b:t): t :=
    if cond then join a b else b.

  Lemma join_if_wf
        cond lhs rhs
        (LHS: wf lhs)
        (RHS: wf rhs):
    wf (join_if cond lhs rhs).
  Proof.
    destruct cond; ss. apply join_wf; auto.
  Qed.

  Lemma join_if_spec
        (cond:bool) a b c
        (A: cond -> le a c)
        (B: le b c):
    le (join_if cond a b) c.
  Proof. destruct cond; auto. apply join_spec; auto. Qed.

  Lemma join_if_le
        (cond:bool) a b c
        (A: cond -> le c a)
        (B: ~cond -> le c b):
    le c (if cond then a else b).
  Proof. destruct cond; auto. Qed.

  Definition incr_ur loc ts s :=
    mk (TimeMap.incr loc ts s.(ur))
       (TimeMap.incr loc ts s.(rw))
       (TimeMap.incr loc ts s.(sc)).

  Lemma incr_ur_wf loc ts s
        (WF: wf s):
    wf (incr_ur loc ts s).
  Proof.
    econs; s.
    - apply TimeMap.incr_mon. apply WF.
    - apply TimeMap.incr_mon. apply WF.
  Qed.

  Lemma incr_ur_le
        loc ts s:
    le s (incr_ur loc ts s).
  Proof.
    econs; ss.
    - apply TimeMap.incr_le.
    - apply TimeMap.incr_le.
    - apply TimeMap.incr_le.
  Qed.

  Lemma incr_ur_spec
        loc ts s1 s2
        (LE: le s1 s2)
        (UR: Time.le ts (s2.(ur) loc))
        (RW: Time.le ts (s2.(rw) loc))
        (SC: Time.le ts (s2.(sc) loc)):
    le (incr_ur loc ts s1) s2.
  Proof.
    inv LE. econs; ss.
    - apply TimeMap.incr_spec; ss.
    - apply TimeMap.incr_spec; ss.
    - apply TimeMap.incr_spec; ss.
  Qed.

  Lemma incr_ur_inv
        loc ts s1 s2
        (LE: le (incr_ur loc ts s1) s2):
    <<LE:le s1 s2>> /\
    <<UR: Time.le ts (s2.(ur) loc)>> /\
    <<RW: Time.le ts (s2.(rw) loc)>> /\
    <<SC: Time.le ts (s2.(sc) loc)>>.
  Proof.
    inv LE. splits.
    - econs; ss; etrans; eauto; apply TimeMap.incr_le.
    - etrans; eauto. apply TimeMap.incr_ts.
    - etrans; eauto. apply TimeMap.incr_ts.
    - etrans; eauto. apply TimeMap.incr_ts.
  Qed.

  Lemma incr_ur_mon loc ts s1 s2
        (LE: le s1 s2):
    le (incr_ur loc ts s1) (incr_ur loc ts s2).
  Proof.
    apply incr_ur_spec.
    - etrans; eauto. apply incr_ur_le.
    - apply TimeMap.incr_ts.
    - apply TimeMap.incr_ts.
    - apply TimeMap.incr_ts.
  Qed.

  Definition incr_rw loc ts s :=
    mk s.(ur)
       (TimeMap.incr loc ts s.(rw))
       (TimeMap.incr loc ts s.(sc)).

  Lemma incr_rw_wf loc ts s
        (WF: wf s):
    wf (incr_rw loc ts s).
  Proof.
    econs; s.
    - etrans; [|apply TimeMap.incr_le]. apply WF.
    - apply TimeMap.incr_mon. apply WF.
  Qed.

  Lemma incr_rw_le
        loc ts s:
    le s (incr_rw loc ts s).
  Proof.
    econs; ss.
    - refl.
    - apply TimeMap.incr_le.
    - apply TimeMap.incr_le.
  Qed.

  Lemma incr_rw_spec
        loc ts s1 s2
        (LE: le s1 s2)
        (RW: Time.le ts (s2.(rw) loc))
        (SC: Time.le ts (s2.(sc) loc)):
    le (incr_rw loc ts s1) s2.
  Proof.
    inv LE. econs; ss.
    - apply TimeMap.incr_spec; ss.
    - apply TimeMap.incr_spec; ss.
  Qed.

  Lemma incr_rw_inv
        loc ts s1 s2
        (LE: le (incr_rw loc ts s1) s2):
    <<LE:le s1 s2>> /\
    <<RW: Time.le ts (s2.(rw) loc)>> /\
    <<SC: Time.le ts (s2.(sc) loc)>>.
  Proof.
    inv LE. splits.
    - econs; ss; etrans; eauto; apply TimeMap.incr_le.
    - etrans; eauto. apply TimeMap.incr_ts.
    - etrans; eauto. apply TimeMap.incr_ts.
  Qed.

  Lemma incr_rw_mon loc ts s1 s2
        (LE: le s1 s2):
    le (incr_rw loc ts s1) (incr_rw loc ts s2).
  Proof.
    apply incr_rw_spec.
    - etrans; eauto. apply incr_rw_le.
    - apply TimeMap.incr_ts.
    - apply TimeMap.incr_ts.
  Qed.

  Lemma incr_rw_nop
        loc ts cur
        (WF: Capability.wf cur)
        (TS: Time.le ts (cur.(Capability.rw) loc)):
    incr_rw loc ts cur = cur.
  Proof.
    destruct cur. unfold incr_rw. ss. f_equal.
    - apply TimeMap.incr_nop. auto.
    - apply TimeMap.incr_nop. etrans; eauto. apply WF.
  Qed.

  Lemma le_join_l l r
        (LE: le r l):
    join l r = l.
  Proof.
    unfold join. destruct l. ss.
    f_equal; apply TimeMap.le_join_l; apply LE.
  Qed.

  Lemma le_join_r l r
        (LE: le l r):
    join l r = r.
  Proof.
    unfold join. destruct r. ss.
    f_equal; apply TimeMap.le_join_r; apply LE.
  Qed.
End Capability.

Module Message.
  Structure t := mk {
    val: Const.t;
    released: Capability.t;
  }.
  Definition elt: t := mk 0 Capability.elt.
End Message.

Module Cell.
  Module Raw.
    Definition t := DOMap.t (DenseOrder.t * Message.t).

    Inductive wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            Time.lt from to)
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 cell = Some (from1, msg1))
                     (GET2: DOMap.find to2 cell = Some (from2, msg2))
                     (NEQ: to1 <> to2),
            Interval.disjoint (from1, to1) (from2, to2))
    .

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      DOMap.singleton to (from, msg).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Inductive add (cell1:t) (from to:Time.t) (msg:Message.t): forall (rhs:t), Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                     (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            to <> from2 /\ Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to):
        add cell1 from to msg (DOMap.add to (from, msg) cell1)
    .

    Lemma add_wf
          cell1 from to msg rhs
          (ADD: add cell1 from to msg rhs)
          (CELL1: wf cell1):
      wf rhs.
    Proof.
      inv ADD. inv CELL1. econs; i.
      - rewrite DOMap.Facts.add_o in *.
        revert GET. condtac; i.
        + inv GET. auto.
        + eapply VOLUME. eauto.
      - rewrite DOMap.Facts.add_o in *.
        revert GET1 GET2. repeat condtac; i; repeat subst.
        + congr.
        + inv GET1. eapply DISJOINT; eauto.
        + inv GET2. symmetry. eapply DISJOINT; eauto.
        + eapply DISJOINT0; eauto.
    Qed.

    Inductive split (cell1:t) (from to1 to2:Time.t) (msg1:Message.t): forall (rhs:t), Prop :=
    | split_intro
        msg2
        (GET2: DOMap.find to2 cell1 = Some (from, msg2))
        (TO1: Time.lt from to1)
        (TO2: Time.lt to1 to2):
        split cell1 from to1 to2 msg1
              (DOMap.add to1 (from, msg1) (DOMap.add to2 (to1, msg2) cell1))
    .

    Lemma split_wf
          cell1 from1 to1 to2 msg1 cell2
          (SPLIT: split cell1 from1 to1 to2 msg1 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv SPLIT. inv CELL1. econs; i.
      - rewrite ? DOMap.Facts.add_o in *.
        revert GET. repeat condtac; i; try by inv GET.
        eapply VOLUME. eauto.
      - rewrite ? DOMap.Facts.add_o in *.
        revert GET1 GET0. repeat condtac; i; repeat subst; try congr;
          (repeat match goal with
                 | [H: Some _ = Some _ |- _] => inv H
                  end);
          (try by eapply DISJOINT; eauto).
        + apply Interval.disjoint_imm.
        + ii. eapply (DISJOINT to3 to2); eauto.
          eapply Interval.le_mem; try apply LHS.
          econs; s. refl. apply Time.le_lteq. auto.
        + symmetry. apply Interval.disjoint_imm.
        + ii. eapply (DISJOINT to3 to0); eauto.
          eapply Interval.le_mem; try apply LHS.
          econs; s. apply Time.le_lteq. auto. refl.
        + ii. eapply (DISJOINT to0 to2); eauto.
          eapply Interval.le_mem; try apply RHS.
          econs; s. refl. apply Time.le_lteq. auto.
        + ii. eapply (DISJOINT to0 to3); eauto.
          eapply Interval.le_mem; try apply RHS.
          econs; s. apply Time.le_lteq. auto. refl.
    Qed.

    Inductive remove (cell1:t) (from to:Time.t) (msg:Message.t): forall (rhs:t), Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, msg)):
        remove cell1 from to msg (DOMap.remove to cell1)
    .

    Lemma remove_wf
          cell1 from to msg rhs
          (REMOVE: remove cell1 from to msg rhs)
          (CELL1: wf cell1):
      wf rhs.
    Proof.
      inv REMOVE. inv CELL1. econs; i.
      - revert GET0. rewrite DOMap.Facts.remove_o.
        condtac; eauto. congr.
      - revert GET1 GET2. rewrite ? DOMap.Facts.remove_o.
        repeat condtac; i; try congr.
        eapply DISJOINT; eauto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option (Time.t * Message.t) := DOMap.find ts cell.(raw).

  Lemma ext
        (lhs rhs:t)
        (EXT: forall ts, get ts lhs = get ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    assert (raw0 = raw1).
    { apply DOMap.eq_leibniz. ii. apply EXT. }
    subst raw1. f_equal. apply proof_irrelevance.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg
      (LHS: get to lhs = Some (from, msg)),
      get to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                   (GET1: get to1 lhs = Some (from1, msg1))
                   (GET2: get to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. symmetry. eapply DISJOINT; eauto.
  Qed.

  Lemma disjoint_get
        lhs rhs
        ts lmsg rmsg
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get ts lhs = Some lmsg)
        (RMSG: get ts rhs = Some rmsg):
    False.
  Proof.
    destruct lmsg, rmsg. unfold get in *.
    destruct (DOMap.find ts lhs.(raw)) as [[]|] eqn:LHS; inv LMSG.
    destruct (DOMap.find ts rhs.(raw)) as [[]|] eqn:RHS; inv RMSG.
    eapply DISJOINT; eauto.
    - apply Interval.mem_ub. eapply WF. eauto.
    - apply Interval.mem_ub. eapply WF. eauto.
  Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint cell: disjoint bot cell.
  Proof. econs. ii. rewrite bot_get in GET1. congr. Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    mk (Raw.singleton_wf msg LT).

  Lemma singleton_get
        from to msg (LT:Time.lt from to)
        t:
    get t (singleton msg LT) =
    if Loc.eq_dec t to
    then Some (from, msg)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition init: t :=
    singleton (Message.mk 0 Capability.elt)
              (Time.decr_spec Time.elt).

  Definition add (cell1:t) (from1 to1:Time.t) (msg1:Message.t) (cell2:t): Prop :=
    Raw.add cell1 from1 to1 msg1 cell2.

  Definition split (cell1:t) (from1 to1 to2:Time.t) (msg1:Message.t) (cell2:t): Prop :=
    Raw.split cell1 from1 to1 to2 msg1 cell2.

  Definition remove (cell1:t) (from1 to1:Time.t) (msg1:Message.t) (cell2:t): Prop :=
    Raw.remove cell1 from1 to1 msg1 cell2.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key _ cell.(raw).

  Lemma max_ts_spec
        cell:
    <<GET: get Time.elt cell <> None -> exists from msg, get (max_ts cell) cell = Some (from, msg)>> /\
    <<MAX: forall ts (GET: get ts cell <> None), Time.le ts (max_ts cell)>>.
  Proof.
    generalize (DOMap.max_key_spec _ cell.(Cell.raw)). i. des. splits; eauto. i.
    destruct (DOMap.find
                (DOMap.max_key (DenseOrder.t * Message.t) (Cell.raw cell))
                (Cell.raw cell)) as [[]|] eqn:X.
    - eexists _, _. eauto.
    - exfalso. apply FIND; auto.
  Qed.

  Lemma raw_add_exists_max_ts
        cell1 to val released
        (TO: Time.lt (max_ts cell1) to)
        (WF: Capability.wf released):
    exists cell2, Raw.add cell1 (max_ts cell1) to (Message.mk val released) cell2.
  Proof.
    generalize (max_ts_spec cell1). i. des.
    destruct cell1. ss.
    eexists. i. econs; ss.
    i. exploit MAX.
    { unfold get. s. rewrite GET2. congr. }
    i.
    splits.
    - ii. subst. inversion WF0. exploit VOLUME; eauto. i.
      rewrite x0 in TO. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    - ii. inv LHS. inv RHS. ss.
      rewrite x in TO1. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to val released
        (TO: Time.lt (max_ts cell1) to)
        (WF: Capability.wf released):
    exists cell2, add cell1 (max_ts cell1) to (Message.mk val released) cell2.
  Proof.
    exploit raw_add_exists_max_ts; eauto. i. des.
    destruct (classic (Capability.wf released)).
    - eexists (mk _). eauto.
    - exists cell1. congr.
  Grab Existential Variables.
    { eapply Raw.add_wf; eauto. apply Cell.WF. }
  Qed.

  Lemma raw_add_exists_le
        promises1 mem1 from to msg mem2
        (LE: le promises1 mem1)
        (ADD: Raw.add mem1 from to msg mem2):
    exists promises2, Raw.add promises1 from to msg promises2.
  Proof.
    inv ADD. eexists. econs; eauto.
  Qed.

  Lemma add_exists_le
        promises1 mem1 from to msg mem2
        (LE: le promises1 mem1)
        (ADD: add mem1 from to msg mem2):
    exists promises2, add promises1 from to msg promises2.
  Proof.
    exploit raw_add_exists_le; eauto. i. des.
    eexists (mk _). unfold add. s.  eauto.
  Grab Existential Variables.
    { eapply Raw.add_wf; eauto. apply Cell.WF. }
  Qed.

  (* Lemmas on add, split & remove *)

  Lemma add_disjoint
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    get to1 cell1 = None.
  Proof.
    inv ADD. unfold get.
    destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
    exfalso. eapply DISJOINT; eauto.
    - apply Interval.mem_ub. auto.
    - apply Interval.mem_ub. eapply WF. eauto.
  Qed.

  Lemma add_get1
        cell1 from1 to1 msg1 cell2
        t f m
        (ADD: add cell1 from1 to1 msg1 cell2)
        (GET: get t cell1 = Some (f, m)):
    get t cell2 = Some (f, m).
  Proof.
    exploit add_disjoint; eauto. i.
    unfold get in *. inv ADD.
    rewrite DOMap.gsspec. condtac; auto. subst.
    congr.
  Qed.

  Lemma add_get2
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    get to1 cell2 = Some (from1, msg1).
  Proof.
    unfold get in *. inv ADD.
    rewrite DOMap.gss. auto.
  Qed.

  Lemma add_get_inv
        cell1 from1 to1 msg1 cell2
        t f m
        (ADD: add cell1 from1 to1 msg1 cell2)
        (GET: get t cell2 = Some (f, m)):
    (t = to1 /\ f = from1 /\ m = msg1) \/
    (~ t = to1 /\
     get t cell1 = Some (f, m)).
  Proof.
    unfold get in *. inv ADD.
    revert GET. rewrite <- H0. rewrite DOMap.gsspec. condtac; auto.
    i. inv GET. auto.
  Qed.

  Lemma add_inhabited
        cell1 cell2 to msg
        (ADD: add cell1 (max_ts cell1) to msg cell2)
        (INHABITED: get Time.elt cell1 <> None):
    <<INHABITED: get Time.elt cell2 <> None>>.
  Proof.
    ii. eapply INHABITED.
    destruct (get Time.elt cell1) as [[]|] eqn:X; auto.
    exploit add_get1; eauto. i. congr.
  Qed.

  Lemma add_max_ts
        cell1 to msg cell2
        (INHABITED: get Time.elt cell1 <> None)
        (ADD: add cell1 (max_ts cell1) to msg cell2):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    generalize (max_ts_spec cell1). i. des.
    generalize (max_ts_spec cell2). i. des.
    specialize (GET0 H). des.
    exploit add_get_inv; eauto. i. des.
    - subst. auto.
    - exploit MAX0; i.
      { erewrite add_get2; eauto. congr. }
      exploit MAX; i.
      { rewrite x1. congr. }
      inv ADD. exploit TimeFacts.lt_le_lt; eauto. i.
      exploit TimeFacts.lt_le_lt; eauto. i.
      exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma remove_singleton
        from to msg (LT:Time.lt from to):
    remove (singleton msg LT) from to msg bot.
  Proof.
    assert (Raw.bot = DOMap.remove to ((singleton msg LT).(raw))).
    { apply DOMap.eq_leibniz. ii.
      unfold Raw.bot. rewrite DOMap.gempty.
      rewrite DOMap.grspec. condtac; auto.
      unfold singleton, Raw.singleton, raw.
      rewrite DOMap.singleton_neq; auto.
    }
    unfold remove. s. rewrite H. econs. s.
    unfold Raw.singleton. rewrite DOMap.singleton_eq. auto.
  Qed.    

  Lemma remove_exists
        cell1 from to msg
        (GET: get to cell1 = Some (from, msg)):
    exists cell2, remove cell1 from to msg cell2.
  Proof.
    eexists (mk _). destruct cell1. ss.
    Grab Existential Variables.
    { eapply Raw.remove_wf.
      - econs. eauto.
      - apply WF.
    }
  Qed.
End Cell.

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
      (DISJOINT: forall loc, Cell.disjoint (lhs loc) (rhs loc))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. ii. symmetry. apply H.
  Qed.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof. unfold get. apply Cell.bot_get. Qed.

  Lemma bot_le mem: le bot mem.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof. econs. i. apply Cell.bot_disjoint. Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    (LocFun.add loc (Cell.singleton msg LT)
                (fun _ => Cell.bot)).

  Lemma singleton_get
        loc from to msg (LT:Time.lt from to)
        l t:
    get l t (singleton loc msg LT) =
    if Loc.eq_dec l loc
    then if Time.eq_dec t to
         then Some (from, msg)
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
    forall loc, exists from msg, get loc (times loc) mem = Some (from, msg).

  Inductive closed_capability (capability:Capability.t) (mem:t): Prop :=
  | closed_capability_intro
      (UR: closed_timemap capability.(Capability.ur) mem)
      (RW: closed_timemap capability.(Capability.rw) mem)
      (SC: closed_timemap capability.(Capability.sc) mem)
  .

  Inductive closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to msg (MSG: get loc to mem = Some (from, msg)),
          <<WF: Capability.wf msg.(Message.released)>> /\
          <<TS: Time.le (msg.(Message.released).(Capability.rw) loc) to>> /\
          <<CLOSED: closed_capability msg.(Message.released) mem>>)
      (ELT: forall loc, get loc Time.elt mem <> None)
  .

  Lemma timemap_elt_closed: closed_timemap TimeMap.elt init.
  Proof.
    econs. unfold TimeMap.elt.
    unfold get, init, Cell.get, Cell.init. s.
    unfold Cell.Raw.singleton. rewrite DOMap.singleton_eq. eauto.
  Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    unfold get, init, Cell.get, Cell.init in MSG. ss.
    unfold Cell.Raw.singleton in MSG. ss. apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
    splits; ss.
    - apply Capability.elt_wf.
    - refl.
    - econs; apply timemap_elt_closed.
  Qed.

  Inductive add (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t): forall (mem2:t), Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from1 to1 msg1 r)
      (WF: Capability.wf msg1.(Message.released)):
      add mem1 loc from1 to1 msg1 (LocFun.add loc r mem1)
  .

  Inductive split (mem1:t) (loc:Loc.t) (from1 to1 to2:Time.t) (msg1:Message.t): forall (mem2:t), Prop :=
  | split_intro
      r
      (SPLIT: Cell.split (mem1 loc) from1 to1 to2 msg1 r)
      (WF: Capability.wf msg1.(Message.released)):
      split mem1 loc from1 to1 to2 msg1 (LocFun.add loc r mem1)
  .

  Inductive remove (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t): forall (mem2:t), Prop :=
  | remove_intro
      r
      (REMOVE: Cell.remove (mem1 loc) from1 to1 msg1 r):
      remove mem1 loc from1 to1 msg1 (LocFun.add loc r mem1)
  .

  Inductive future_imm (mem1 mem2:t): Prop :=
  | future_imm_add
      loc from1 to1 msg1
      (ADD: add mem1 loc from1 to1 msg1 mem2)
  | future_imm_split
      loc from1 to1 to2 msg1
      (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
  .

  Inductive splits_imm (mem1 mem2:t): Prop :=
  | splits_imm_intro
      loc from1 to1 to2 msg1
      (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
      (CLOSED: closed mem2)
  .

  Definition future := rtc future_imm.
  Definition splits := rtc splits_imm.

  Lemma splits_future: splits <2= future.
  Proof.
    i. induction PR.
    - econs 1.
    - econs 2; eauto. inv H. econs 2; eauto.
  Qed.

  Inductive promise_kind :=
  | promise_kind_add
  | promise_kind_split
  .

  Inductive promise
            (promises1 mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t)
            (promises2 mem2:t): forall (kind:promise_kind), Prop :=
  | promise_add
      (PROMISES: add promises1 loc from1 to1 msg1 promises2)
      (MEM: add mem1 loc from1 to1 msg1 mem2)
      (CLOSED: closed_capability msg1.(Message.released) mem2)
      (TS: Time.le (Capability.rw (Message.released msg1) loc) to1):
      promise promises1 mem1 loc from1 to1 msg1 promises2 mem2 promise_kind_add
  | promise_split
      to2
      (PROMISES: split promises1 loc from1 to1 to2 msg1 promises2)
      (MEM: split mem1 loc from1 to1 to2 msg1 mem2)
      (CLOSED: closed_capability msg1.(Message.released) mem2)
      (TS: Time.le (Capability.rw (Message.released msg1) loc) to1):
      promise promises1 mem1 loc from1 to1 msg1 promises2 mem2 promise_kind_split
  .

  Inductive fulfill
            (promises1:t)
            (loc:Loc.t) (from to:Time.t) (msg:Message.t)
            (promises2:t): Prop :=
  | fulfill_intro
      (REMOVE: remove promises1 loc from to msg promises2)
  .


  (* Lemmas on add, split & remove *)

  Lemma add_disjoint
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv ADD. exploit Cell.add_disjoint; eauto.
  Qed.

  Lemma add_get1
        mem1 loc from1 to1 msg1 mem2
        l t f m
        (ADD: add mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    get l t mem2 = Some (f, m).
  Proof.
    inv ADD. unfold get, LocFun.add, LocFun.find. condtac; auto. subst.
    exploit Cell.add_get1; eauto.
  Qed.

  Lemma add_get2
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem2 = Some (from1, msg1).
  Proof.
    inv ADD. unfold get, LocFun.add, LocFun.find. condtac; [|congr].
    exploit Cell.add_get2; eauto.
  Qed.

  Lemma add_get_inv
        mem1 loc from1 to1 msg1 mem2
        l t f m
        (ADD: add mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem2 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = msg1) \/
    (~ (l = loc /\ t = to1) /\
     get l t mem1 = Some (f, m)).
  Proof.
    inv ADD. revert GET. unfold get, LocFun.add, LocFun.find. condtac; i.
    - subst. exploit Cell.add_get_inv; eauto. i. des.
      + subst. left. auto.
      + right. splits; auto. contradict x0. des. auto.
    - right. splits; auto. clear COND. contradict n. des. auto.
  Qed.

  Lemma split_disjoint
        mem1 loc from1 to1 to2 msg1 mem2
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv SPLIT. inv SPLIT0. destruct r. ss. subst.
    unfold get, Cell.get.
    destruct (DOMap.find to1 (Cell.raw (mem1 loc))) as [[]|] eqn:X; auto.
    destruct (mem1 loc).(Cell.WF).
    exfalso. eapply DISJOINT; [apply GET2|apply X| | |].
    - ii. subst. eapply Time.lt_strorder. eauto.
    - econs; eauto. apply Time.le_lteq. auto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
  Qed.

  Lemma split_get1
        mem1 loc from1 to1 to2 msg1 mem2
        l t f m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    (l = loc /\ f = from1 /\ t = to2 /\ get l t mem2 = Some (to1, m)) \/
    (~ (l = loc /\ t = to2) /\
     get l t mem2 = Some (f, m)).
  Proof.
    unfold get, Cell.get in *. inv SPLIT. inv SPLIT0.
    unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite ? DOMap.gsspec. repeat condtac; subst; ss.
    - destruct (DOMap.find to1 (Cell.raw (mem1 loc))) as [[]|] eqn:X; inv GET.
      destruct (mem1 loc).(Cell.WF).
      exfalso. eapply DISJOINT; [apply GET2|apply X| | |].
      + ii. subst. eapply Time.lt_strorder. eauto.
      + econs; eauto. apply Time.le_lteq. auto.
      + apply Interval.mem_ub. eapply VOLUME. eauto.
    - rewrite GET2 in *. inv GET. eauto.
    - rewrite GET. right. splits; eauto. ii. des. congr.
    - rewrite GET. right. splits; eauto. ii. des. congr.
  Qed.

  Lemma split_get1'
        mem1 loc from1 to1 to2 msg1 mem2
        l t f m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    exists f', get l t mem2 = Some (f', m).
  Proof.
    exploit split_get1; eauto. i. des; eauto.
  Qed.

  Lemma split_get2
        mem1 loc from1 to1 to2 msg1 mem2
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2):
    get loc to1 mem2 = Some (from1, msg1).
  Proof.
    unfold get, Cell.get in *. inv SPLIT. inv SPLIT0.
    unfold LocFun.add, LocFun.find. condtac; [|congr].
    rewrite <- H0. rewrite DOMap.gss. auto.
  Qed.

  Lemma split_get_inv
        mem1 loc from1 to1 to2 msg1 mem2
        l t f m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem2 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = msg1) \/
    (l = loc /\ t = to2 /\ f = to1 /\ get l t mem1 = Some (from1, m)) \/
    (~ (l = loc /\ t = to1) /\
     ~ (l = loc /\ t = to2) /\
     get l t mem1 = Some (f, m)).
  Proof.
    unfold get, Cell.get in *. inv SPLIT. inv SPLIT0.
    revert GET. unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite ? DOMap.gsspec. repeat condtac; subst; ss; auto.
    - i. inv GET. auto.
    - i. inv GET. rewrite GET2. right. left. auto.
    - right. right. splits; auto.
      + ii. des. congr.
      + ii. des. congr.
    - right. right. splits; auto.
      + ii. des. congr.
      + ii. des. congr.
  Qed.

  Lemma split_get_inv'
        mem1 loc from1 to1 to2 msg1 mem2
        l t f m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem2 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = msg1) \/ exists f', get l t mem1 = Some (f', m).
  Proof.
    exploit split_get_inv; eauto. i. des; eauto.
  Qed.

  Lemma remove_disjoint
        mem1 loc from1 to1 msg1 mem2
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem1 = Some (from1, msg1).
  Proof.
    inv REMOVE. inv REMOVE0. destruct r. ss.
  Qed.

  Lemma remove_get1
        mem1 loc from1 to1 msg1 mem2
        l t f m
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = msg1) \/ get l t mem2 = Some (f, m).
  Proof.
    exploit remove_disjoint; eauto. i.
    unfold get, Cell.get in *. inv REMOVE. inv REMOVE0.
    unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite DOMap.grspec. condtac; auto. subst.
    rewrite x0 in GET. inv GET. left. auto.
  Qed.

  Lemma remove_get2
        mem1 loc from1 to1 msg1 mem2
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem2 = None.
  Proof.
    unfold get, Cell.get in *. inv REMOVE. inv REMOVE0.
    unfold LocFun.add, LocFun.find. condtac; [|congr].
    rewrite <- H0. rewrite DOMap.grs. auto.
  Qed.

  Lemma remove_get_inv
        mem1 loc from1 to1 msg1 mem2
        l t f m
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem2 = Some (f, m)):
    ~ (l = loc /\ t = to1) /\
    get l t mem1 = Some (f, m).
  Proof.
    unfold get, Cell.get in *. inv REMOVE. inv REMOVE0.
    revert GET. unfold LocFun.add, LocFun.find. condtac.
    - subst. rewrite <- H0, DOMap.grspec. condtac; [congr|].
      i. splits; auto. ii. des. congr.
    - i. splits; auto. ii. des. congr.
  Qed.

  Lemma future_get
        loc from to msg mem1 mem2
        (LE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg)):
    exists from', get loc to mem2 = Some (from', msg).
  Proof.
    revert from GET. induction LE; eauto.
    i. inv H.
    - exploit add_get1; eauto.
    - exploit split_get1'; eauto. i. des.
      eapply IHLE; eauto.
  Qed.

  Lemma splits_get
        loc from to msg mem1 mem2
        (LE: splits mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg)):
    exists from', get loc to mem2 = Some (from', msg).
  Proof.
    revert from GET. induction LE; eauto.
    i. inv H. exploit split_get1'; eauto. i. des.
    eapply IHLE; eauto.
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

  Lemma future_closed_timemap
        times mem1 mem2
        (CLOSED: closed_timemap times mem1)
        (FUTURE: future mem1 mem2):
    closed_timemap times mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    exploit future_get; eauto. i. des.
    eexists _, _. splits; eauto.
  Qed.

  Lemma future_closed_capability
        capability mem1 mem2
        (CLOSED: closed_capability capability mem1)
        (FUTURE: future mem1 mem2):
    closed_capability capability mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply future_closed_timemap; eauto.
    - eapply future_closed_timemap; eauto.
    - eapply future_closed_timemap; eauto.
  Qed.

  Lemma incr_closed_timemap
        loc s from to msg mem
        (CLOSED: closed_timemap s mem)
        (GET: get loc to mem = Some (from, msg)):
    closed_timemap (TimeMap.incr loc to s) mem.
  Proof.
    unfold TimeMap.incr, LocFun.add, LocFun.find. ii. condtac.
    - subst. destruct (Time.join_cases (s loc) to) as [X|X]; rewrite X; eauto.
    - apply CLOSED.
  Qed.

  Lemma incr_ur_closed_capability
        loc from to s msg mem
        (CLOSED: closed_capability s mem)
        (GET: get loc to mem = Some (from, msg)):
    closed_capability (Capability.incr_ur loc to s) mem.
  Proof.
    inv CLOSED. econs; s.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
  Qed.

  Lemma incr_rw_closed_capability
        loc from to s msg mem
        (CLOSED: closed_capability s mem)
        (GET: get loc to mem = Some (from, msg)):
    closed_capability (Capability.incr_rw loc to s) mem.
  Proof.
    inv CLOSED. econs; s.
    - auto.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
  Qed.


  (* Lemmas on promise & fulfill *)

  Lemma promise_get1
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t mem1 = Some (f, m)):
    exists f', get l t mem2 = Some (f', m).
  Proof.
    inv PROMISE.
    - exploit add_get1; eauto.
    - eapply split_get1'; eauto.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    get loc to promises2 = Some (from, msg).
  Proof.
    inv PROMISE.
    - eapply add_get2; eauto.
    - eapply split_get2; eauto.
  Qed.

  Lemma promise_promises_get1
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t promises1 = Some (f, m)):
    exists f', get l t promises2 = Some (f', m).
  Proof.
    inv PROMISE.
    - exploit add_get1; try apply PROMISES; eauto.
    - eapply split_get1'; eauto.
  Qed.

  Lemma promise_promises_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t promises2 = Some (f, m)):
    (l = loc /\ t = to /\ f = from /\ m = msg /\ get l t promises1 = None) \/
    (~ (l = loc /\ t = to) /\ exists f', get l t promises1 = Some (f', m)).
  Proof.
    inv PROMISE.
    - exploit add_get_inv; try apply PROMISES; eauto. i. des.
      + subst. left. splits; auto.
        eapply add_disjoint. eauto.
      + right. splits; auto. eexists. eauto.
    - exploit split_get_inv; try apply PROMISES; eauto. i. des.
      + subst. left. splits; auto.
        eapply split_disjoint. eauto.
      + subst. right. splits.
        * ii. des. subst. inv PROMISES. inv SPLIT.
          eapply Time.lt_strorder. eauto.
        * eexists. eauto.
      + right. splits; auto. eexists. eauto.
  Qed.

  Lemma promise_future
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv PROMISE.
    - splits; eauto.
      + ii. eapply add_get_inv in LHS; eauto. des.
        * subst. eapply add_get2. eauto.
        * eapply add_get1; eauto.
      + econs.
        * ii. eapply add_get_inv in MSG; eauto. des.
          { inv MSG1. inv MEM. eauto. }
          { inv CLOSED1. exploit CLOSED0; eauto. i. des. splits; auto.
            eapply future_closed_capability; eauto.
            econs 2; eauto. econs 1. eauto.
          }
        * ii. eapply CLOSED1. instantiate (1 := loc0).
          destruct (get loc0 Time.elt mem1) as [[]|] eqn:X; auto.
          exploit add_get1; eauto. i. congr.
      + econs 2; eauto. econs 1; eauto.
    - splits; eauto.
      + ii. eapply split_get_inv in LHS; eauto. des.
        * subst. eapply split_get2. eauto.
        * subst. exploit split_get1; try apply MEM; eauto. i. des; auto.
          contradict x0. auto.
        * exploit split_get1; try apply MEM; eauto. i. des; auto.
          subst. contradict LHS0. auto.
      + econs.
        * ii. eapply split_get_inv' in MSG; eauto. des.
          { subst. inv MEM. eauto. }
          { inv CLOSED1. exploit CLOSED0; eauto. i. des. splits; auto.
            eapply future_closed_capability; eauto.
            econs 2; eauto. econs 2. eauto.
          }
        * ii. eapply CLOSED1. instantiate (1 := loc0).
          destruct (get loc0 Time.elt mem1) as [[]|] eqn:X; auto.
          exploit split_get1; eauto. i. des; congr.
      + econs 2; eauto. econs 2; eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: Memory.disjoint promises1 ctx):
    <<DISJOINT: Memory.disjoint promises2 ctx>> /\
    <<LE_PROMISES: le ctx mem2>>.
  Proof.
    exploit promise_future; try apply PROMISE; eauto. i. des.
    inv PROMISE.
    - splits.
      + econs. i. econs. i.
        eapply add_get_inv in GET1; eauto. des.
        * subst. exploit LE_PROMISES; eauto. i.
          exploit add_get1; eauto. i.
          exploit add_get2; eauto. i.
          eapply Cell.WF; eauto.
          ii. subst. exploit add_disjoint; eauto. congr.
        * eapply DISJOINT; eauto.
      + ii. eapply add_get1; eauto.
    - splits.
      + econs. i. econs. i.
        eapply split_get_inv in GET1; eauto. des.
        * subst. inv PROMISES. inv SPLIT.
          eapply Interval.le_disjoint.
          { eapply DISJOINT; eauto. }
          { econs; s; try refl. apply Time.le_lteq. auto. }
        * subst. inv PROMISES. inv SPLIT.
          eapply Interval.le_disjoint.
          { eapply DISJOINT; eauto. }
          { econs; s; try refl. apply Time.le_lteq. auto. }
        * eapply DISJOINT; eauto.
      + ii. exploit split_get1; eauto. i. des; auto. subst.
        inv PROMISES. inv SPLIT.
        exfalso. eapply Cell.disjoint_get; [apply DISJOINT| |]; eauto.
  Qed.

  Lemma fulfill_future
        promises1 mem1 loc from to msg promises2
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (FULFILL: fulfill promises1 loc from to msg promises2):
    <<LE_PROMISES2: le promises2 mem1>>.
  Proof.
    inv FULFILL. ii. eapply remove_get_inv in LHS; eauto. des. auto.
  Qed.

  Lemma fulfill_disjoint
        promises1 mem1 loc from to msg promises2 ctx
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (FULFILL: fulfill promises1 loc from to msg promises2)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>>.
  Proof.
    inv FULFILL. econs. i. econs. i.
    eapply remove_get_inv in GET1; eauto. des.
    eapply DISJOINT; eauto.
  Qed.

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (mem loc).

  Lemma max_ts_spec
        loc mem
        (INHABITED: get loc Time.elt mem <> None):
    <<GET: exists from msg, get loc (max_ts loc mem) mem = Some (from, msg)>> /\
    <<MAX: forall ts (GET: get loc ts mem <> None), Time.le ts (max_ts loc mem)>>.
  Proof.
    exploit Cell.max_ts_spec; eauto. i. des.
    splits; eauto.
  Qed.

  Definition max_timemap (mem:t): TimeMap.t :=
    fun loc => max_ts loc mem.

  Lemma max_timemap_closed
        mem
        (INHABITED: forall loc, get loc Time.elt mem <> None):
    closed_timemap (max_timemap mem) mem.
  Proof.
    ii. apply max_ts_spec; auto.
  Qed.

  Lemma max_timemap_spec tm mem
        (TIMEMAP: closed_timemap tm mem)
        (INHABITED: forall loc, get loc Time.elt mem <> None):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. apply max_ts_spec; auto.
    exploit TIMEMAP. i. des. rewrite x. congr.
  Qed.

  Definition max_capability (mem:t): Capability.t :=
    Capability.mk (max_timemap mem) (max_timemap mem) (max_timemap mem).

  Lemma max_capability_wf mem: Capability.wf (max_capability mem).
  Proof. econs. refl. refl. Qed.

  Lemma max_capability_closed
        mem
        (INHABITED: forall loc, get loc Time.elt mem <> None):
    closed_capability (max_capability mem) mem.
  Proof. econs; apply max_timemap_closed; auto. Qed.

  Lemma max_capability_spec tm mem
        (CAPABILITY: closed_capability tm mem)
        (INHABITED: forall loc, get loc Time.elt mem <> None):
    Capability.le tm (max_capability mem).
  Proof.
    econs; apply max_timemap_spec; try apply CAPABILITY; auto.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc to msg
        (ADD: add mem1 loc (max_ts loc mem1) to msg mem2)
        (INHABITED: forall loc, get loc Time.elt mem1 <> None):
    <<INHABITED: forall loc, get loc Time.elt mem2 <> None>>.
  Proof.
    ii. eapply INHABITED. instantiate (1 := loc0).
    destruct (get loc0 Time.elt mem1) as [[]|] eqn:X; auto.
    exploit add_get1; eauto. i. congr.
  Qed.

  Lemma add_max_timemap
        mem1 mem2 loc to msg
        (ADD: add mem1 loc (max_ts loc mem1) to msg mem2)
        (INHABITED: forall loc, get loc Time.elt mem1 <> None):
    max_timemap mem2 = TimeMap.incr loc to (max_timemap mem1).
  Proof.
    hexploit add_inhabited; eauto. i. des.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_timemap_closed; eauto. instantiate (1 := l). i. des.
      exploit add_get_inv; eauto. i. des.
      + subst. apply TimeMap.incr_ts.
      + etrans; [|apply TimeMap.incr_le].
        inv ADD. unfold LocFun.add, LocFun.find.
        unfold max_timemap, max_ts. condtac; [|refl].
        subst. contradict x1. splits; auto.
        unfold LocFun.add, LocFun.find.
        unfold max_timemap, max_ts. condtac; [|congr].
        eapply Cell.add_max_ts; eauto.
    - apply max_timemap_spec; auto.
      exploit add_get2; eauto. i.
      eapply incr_closed_timemap; eauto.
      eapply future_closed_timemap.
      + apply max_timemap_closed. auto.
      + econs 2; [|econs 1]. econs 1. eauto.
  Qed.

  Lemma add_max_capability
        mem1 mem2 loc to msg
        (ADD: add mem1 loc (max_ts loc mem1) to msg mem2)
        (INHABITED: forall loc, get loc Time.elt mem1 <> None):
    max_capability mem2 = Capability.incr_ur loc to (max_capability mem1).
  Proof.
    unfold max_capability, Capability.incr_ur. s. f_equal.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
  Qed.

  Lemma add_exists
        mem1 loc from to msg:
    exists mem2, add mem1 loc from to msg mem2.
  Proof.
  Admitted.

  Lemma add_exists_max_ts
        mem1 loc to val
        (TS: Time.lt (max_ts loc mem1) to)
        (CLOSED: closed mem1):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to (Message.mk val (max_capability mem2)) mem2.
  Proof.
    exploit Cell.add_exists_max_ts; eauto.
    { instantiate (1 := Capability.incr_ur loc to (max_capability mem1)).
      apply Capability.incr_ur_wf. apply max_capability_wf.
    }
    i. des. eexists. erewrite add_max_capability; eauto.
    - econs; eauto. s.
      apply Capability.incr_ur_wf. apply max_capability_wf.
    - econs; eauto. s.
      apply Capability.incr_ur_wf. apply max_capability_wf.
    - apply CLOSED.
  Qed.

  Lemma add_exists_le
        promises1 mem1 loc from to msg mem2
        (LE: le promises1 mem1)
        (ADD: add mem1 loc from to msg mem2):
    exists promises2, add promises1 loc from to msg promises2.
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
        (ADD: add mem1 loc from to (Message.mk val released) mem2)
        (REL: closed_capability released mem2)
        (TS: Time.le (Capability.rw released loc) to):
    exists promises2,
      promise promises1 mem1 loc from to (Message.mk val released) promises2 mem2 promise_kind_add.
  Proof.
    exploit add_exists_le; eauto. i. des.
    eexists _. econs 1; s; eauto.
  Qed.

  Lemma promise_add_exists_max_ts
        promises1 mem1 loc to val
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (TS: Time.lt (max_ts loc mem1) to):
    exists promises2 mem2,
      promise promises1 mem1 loc (max_ts loc mem1) to (Message.mk val (max_capability mem2)) promises2 mem2 promise_kind_add.
  Proof.
    exploit add_exists_max_ts; eauto. i. des.
    hexploit add_inhabited; try apply CLOSED1; eauto. i. des.
    exploit promise_add_exists; eauto.
    { apply max_capability_closed. auto. }
    { erewrite add_max_capability; try apply CLOSED1; eauto. ss.
      unfold TimeMap.incr, LocFun.add, LocFun.find. condtac; [|congr].
      apply Time.join_spec; [|refl]. apply Time.le_lteq. eauto.
    }
    i. des. eexists _, _. eauto.
  Qed.

  Lemma remove_singleton
        loc from to msg (LT:Time.lt from to):
    remove (singleton loc msg LT) loc from to msg bot.
  Proof.
    assert (bot = LocFun.add loc Cell.bot (singleton loc msg LT)).
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
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg)):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs. eauto.
  Qed.
End Memory.
