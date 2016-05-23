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


Module Promises.
  Definition t := Loc.t -> DOSet.t.

  Definition mem loc ts (promises:t) := DOSet.mem ts (promises loc).

  Lemma ext lhs rhs
        (EXT: forall loc ts, mem loc ts lhs = mem loc ts rhs):
    lhs = rhs.
  Proof.
    extensionality loc.
    apply DOSet.eq_leibniz. ii.
    specialize (EXT loc a). unfold mem in *. econs; i.
    - apply DOSet.mem_spec. erewrite <- EXT.
      apply DOSet.mem_spec. auto.
    - apply DOSet.mem_spec. erewrite EXT.
      apply DOSet.mem_spec. auto.
  Qed.

  Definition bot: t := fun _ => DOSet.empty.

  Lemma bot_spec loc ts: mem loc ts bot = false.
  Proof.
    unfold mem, bot. apply DOSet.Facts.empty_b.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc ts, mem loc ts lhs -> mem loc ts rhs.

  Definition join (lhs rhs:t): t :=
    fun loc => DOSet.union (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    unfold join. extensionality loc.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. extensionality loc.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    unfold join. ii. unfold mem in *.
    rewrite DOSet.Facts.union_b, H. auto.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. rewrite join_comm. apply join_l. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    unfold join. ii.
    unfold mem in *. rewrite DOSet.Facts.union_b in *.
    apply Bool.orb_true_iff in H. des; eauto.
  Qed.

  Definition set (loc:Loc.t) (ts:Time.t) (promises:t) :=
    LocFun.add loc (DOSet.add ts (promises loc)) promises.

  Lemma set_o loc1 ts1 loc2 ts2 promises:
    mem loc1 ts1 (set loc2 ts2 promises) =
    if andb (if Loc.eq_dec loc1 loc2 then true else false) (if Time.eq_dec ts1 ts2 then true else false)
    then true
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, set, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec loc1 loc2); subst; ss.
    destruct (Time.eq_dec ts1 ts2); subst; ss.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts2); auto.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts1); ss.
      congruence.
  Qed.

  Lemma set_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (set loc2 ts2 promises)):
    (loc1 = loc2 /\ ts1 = ts2) \/ mem loc1 ts1 promises.
  Proof.
    rewrite set_o in MEM.
    destruct (Loc.eq_dec loc1 loc2); ss; auto.
    destruct (Time.eq_dec ts1 ts2); ss; auto.
  Qed.

  Definition unset (loc:Loc.t) (ts:Time.t) (promises:t) :=
    LocFun.add loc (DOSet.remove ts (promises loc)) promises.

  Lemma unset_o loc1 ts1 loc2 ts2 promises:
    mem loc1 ts1 (unset loc2 ts2 promises) =
    if andb (if Loc.eq_dec loc1 loc2 then true else false) (if Time.eq_dec ts1 ts2 then true else false)
    then false
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, unset, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec loc1 loc2); subst; ss.
    destruct (Time.eq_dec ts1 ts2); subst; ss.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts2); [|congruence].
      apply Bool.andb_false_iff. auto.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts1); ss; [congruence|].
      apply Bool.andb_true_r.
  Qed.

  Lemma unset_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (unset loc2 ts2 promises)):
    ~ (loc1 = loc2 /\ ts1 = ts2) /\ mem loc1 ts1 promises.
  Proof.
    rewrite unset_o in MEM.
    destruct (Loc.eq_dec loc1 loc2), (Time.eq_dec ts1 ts2); ss; splits; auto.
    - contradict n. des. auto.
    - contradict n. des. auto.
    - contradict n. des. auto.
  Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc ts
                   (LHS: mem loc ts lhs)
                   (RHS: mem loc ts rhs),
          False).

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. ii. eapply H; eauto.
  Qed.
End Promises.

Module TimeMap <: JoinableType.
  Definition t := Loc.t -> Time.t.
  Definition elt: t := fun _ => Time.elt.

  Definition eq := @eq t.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (lhs loc) (rhs loc).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. reflexivity. Qed.
  Next Obligation. ii. etrans; eauto. Qed.

  Definition get (loc:Loc.t) (c:t) := c loc.

  Definition join (lhs rhs:t): t :=
    fun loc => Time.join (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. unfold join. extensionality loc. apply Time.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    extensionality loc. unfold join.
    apply Time.join_assoc.
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
    ii. unfold incr, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec loc0 loc); auto.
    apply Time.join_spec.
    - etrans; [apply LE|]. apply Time.join_l.
    - apply Time.join_r.
  Qed.

  Lemma incr_le loc ts c:
    le c (incr loc ts c).
  Proof.
    unfold incr, LocFun.add, LocFun.find. ii.
    destruct (Loc.eq_dec loc0 loc).
    - subst. apply Time.join_l.
    - reflexivity.
  Qed.

  Lemma incr_ts loc ts c:
    Time.le ts (get loc (incr loc ts c)).
  Proof.
    unfold get, incr, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec loc loc); [|congruence].
    apply Time.join_r.
  Qed.

  Lemma incr_spec loc ts c1 c2
        (LE: le c1 c2)
        (TS: Time.le ts (get loc c2)):
    TimeMap.le (incr loc ts c1) c2.
  Proof.
    ii. unfold get, incr, LocFun.add, LocFun.find.
    destruct (Loc.eq_dec loc0 loc); auto. subst.
    apply Time.join_spec; auto.
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
    ii. econs; reflexivity.
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
    - reflexivity.
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

    Definition get (ts:Time.t) (cell:t): option Message.t :=
      option_map snd (DOMap.find ts cell).

    Inductive le (lhs rhs:t): Prop :=
    | le_intro
        (LE: forall from to msg
               (GET: DOMap.find to lhs = Some (from, msg)),
            DOMap.find to rhs = Some (from, msg))
    .

    Global Program Instance le_PreOrder: PreOrder le.
    Next Obligation.
      econs. i. auto.
    Qed.
    Next Obligation.
      econs. i. apply H0. apply H. auto.
    Qed.

    Inductive disjoint (lhs rhs:t): Prop :=
    | disjoint_intro
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 lhs = Some (from1, msg1))
                     (GET2: DOMap.find to2 rhs = Some (from2, msg2)),
            Interval.disjoint (from1, to1) (from2, to2))
    .

    Global Program Instance disjoint_Symmetric: Symmetric disjoint.
    Next Obligation.
      inv H. econs. i. symmetry. eapply DISJOINT; eauto.
    Qed.

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Lemma bot_le cell: le bot cell.
    Proof. econs. i. rewrite DOMap.gempty in GET. inv GET. Qed.

    Lemma bot_disjoint cell: disjoint bot cell.
    Proof. econs. i. rewrite DOMap.gempty in GET1. inv GET1. Qed.

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
        congruence.
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
        destruct (DOMap.Facts.eq_dec to to0).
        + inv GET. auto.
        + eapply VOLUME. eauto.
      - rewrite DOMap.Facts.add_o in *.
        destruct (DOMap.Facts.eq_dec to to1),
                 (DOMap.Facts.eq_dec to to2); repeat subst.
        + congruence.
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
        destruct (DOMap.Facts.eq_dec to1 to).
        { inv GET. auto. }
        destruct (DOMap.Facts.eq_dec to2 to).
        { inv GET. auto. }
        eapply VOLUME. eauto.
      - rewrite ? DOMap.Facts.add_o in *.
        destruct (DOMap.Facts.eq_dec to1 to0),
                 (DOMap.Facts.eq_dec to1 to3),
                 (DOMap.Facts.eq_dec to2 to0),
                 (DOMap.Facts.eq_dec to2 to3);
          (repeat subst);
          (try congruence);
          (repeat match goal with
                 | [H: Some _ = Some _ |- _] => inv H
                  end);
          (try by eapply DISJOINT; eauto).
        + apply Interval.disjoint_imm.
        + ii. eapply (DISJOINT to3 to2); eauto.
          eapply Interval.le_mem; try apply LHS.
          econs; s. reflexivity. apply Time.le_lteq. auto.
        + symmetry. apply Interval.disjoint_imm.
        + ii. eapply (DISJOINT to0 to2); eauto.
          eapply Interval.le_mem; try apply RHS.
          econs; s. reflexivity. apply Time.le_lteq. auto.
        + ii. eapply (DISJOINT to3 to0); eauto.
          eapply Interval.le_mem; try apply LHS.
          econs; s. apply Time.le_lteq. auto. reflexivity.
        + ii. eapply (DISJOINT to0 to3); eauto.
          eapply Interval.le_mem; try apply RHS.
          econs; s. apply Time.le_lteq. auto. reflexivity.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Lemma ext
        (lhs rhs:t)
        (EXT: lhs.(raw) = rhs.(raw)):
    lhs = rhs.
  Proof.
    destruct lhs, rhs. ss. subst.
    f_equal. apply proof_irrelevance.
  Qed.

  Definition get (ts:Time.t) (cell:t): option Message.t := Raw.get ts cell.

  Definition le (lhs rhs:t): Prop := Raw.le lhs rhs.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    unfold le. ii. reflexivity.
  Qed.
  Next Obligation.
    unfold le. ii. etrans; eauto.
  Qed.

  Definition disjoint (lhs rhs:t): Prop := Raw.disjoint lhs rhs.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    unfold disjoint in *. symmetry. auto.
  Qed.

  Lemma disjoint_get
        lhs rhs
        ts lmsg rmsg
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get ts lhs = Some lmsg)
        (RMSG: get ts rhs = Some rmsg):
    False.
  Proof.
    destruct lmsg, rmsg. unfold get, Raw.get in *.
    destruct (DOMap.find ts lhs.(raw)) as [[]|] eqn:LHS; inv LMSG.
    destruct (DOMap.find ts rhs.(raw)) as [[]|] eqn:RHS; inv RMSG.
    eapply DISJOINT; eauto.
    - apply Interval.mem_ub. eapply WF. eauto.
    - apply Interval.mem_ub. eapply WF. eauto.
  Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_le cell: le bot cell.
  Proof. apply Raw.bot_le. Qed.

  Lemma bot_disjoint cell: disjoint bot cell.
  Proof. apply Raw.bot_disjoint. Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    mk (Raw.singleton_wf msg LT).

  Definition init: t :=
    singleton (Message.mk 0 Capability.elt)
              (Time.decr_spec Time.elt).

  Definition add (cell1:t) (from1 to1:Time.t) (msg1:Message.t) (cell2:t): Prop :=
    Raw.add cell1 from1 to1 msg1 cell2.

  Definition split (cell1:t) (from1 to1 to2:Time.t) (msg1:Message.t) (cell2:t): Prop :=
    Raw.split cell1 from1 to1 to2 msg1 cell2.
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option Message.t :=
    Cell.get ts (mem loc).

  Definition le (lhs rhs:t): Prop :=
    forall loc, Cell.le (lhs loc) (rhs loc).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. reflexivity.
  Qed.
  Next Obligation.
    ii. etrans; eauto.
  Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc, Cell.disjoint (lhs loc) (rhs loc))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. ii. symmetry. apply H.
  Qed.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_le mem: le bot mem.
  Proof. ii. apply Cell.bot_le. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof. econs. i. apply Cell.bot_disjoint. Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    (LocFun.add loc (Cell.mk (Cell.Raw.singleton_wf msg LT))
                (fun _ => Cell.bot)).

  Definition init: t := fun _ => Cell.init.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists ts msg,
        <<TS: Time.le (times loc) ts>> /\
        <<MSG: get loc ts mem = Some msg>>.

  Inductive closed_capability (capability:Capability.t) (mem:t): Prop :=
  | closed_capability_intro
      (UR: closed_timemap capability.(Capability.ur) mem)
      (RW: closed_timemap capability.(Capability.rw) mem)
      (SC: closed_timemap capability.(Capability.sc) mem)
  .

  Definition closed (mem:t): Prop :=
    forall loc ts msg (MSG: get loc ts mem = Some msg),
      <<WF: Capability.wf msg.(Message.released)>> /\
      <<CLOSED: closed_capability msg.(Message.released) mem>>.

  Definition closed_promises (promises:Promises.t) (mem:t): Prop :=
    forall loc ts (PROMISES: Promises.mem loc ts promises),
    exists msg, get loc ts mem = Some msg.

  Inductive add (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t): forall (mem2:t), Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from1 to1 msg1 r)
      (WF: Capability.wf msg1.(Message.released))
      (CLOSED: closed_capability msg1.(Message.released) (LocFun.add loc r mem1)):
      add mem1 loc from1 to1 msg1 (LocFun.add loc r mem1)
  .

  Inductive split (mem1:t) (loc:Loc.t) (from1 to1 to2:Time.t) (msg1:Message.t): forall (mem2:t), Prop :=
  | split_intro
      r
      (SPLIT: Cell.split (mem1 loc) from1 to1 to2 msg1 r)
      (WF: Capability.wf msg1.(Message.released))
      (CLOSED: closed_capability msg1.(Message.released) (LocFun.add loc r mem1)):
      split mem1 loc from1 to1 to2 msg1 (LocFun.add loc r mem1)
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
  .

  Definition future := rtc future_imm.
  Definition splits := rtc splits_imm.

  Lemma splits_future: splits <2= future.
  Proof.
    i. induction PR.
    - econs 1.
    - econs 2; eauto. inv H. econs 2. eauto.
  Qed.

  Inductive promise
            (promises1:Promises.t) (mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t):
    forall (promises2:Promises.t) (mem2:t), Prop :=
  | promise_add
      mem2
      (ADD: add mem1 loc from1 to1 msg1 mem2):
      promise promises1 mem1 loc from1 to1 msg1 (Promises.set loc to1 promises1) mem2
  | promise_split
      to2 mem2
      (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
      (OWN: Promises.mem loc to2 promises1):
      promise promises1 mem1 loc from1 to1 msg1 (Promises.set loc to1 promises1) mem2
  .

  Inductive fulfill
            (promises1:Promises.t) (mem1:t)
            (loc:Loc.t) (to:Time.t) (msg:Message.t):
    forall (promises2:Promises.t), Prop :=
  | fulfill_intro
      (GET: get loc to mem1 = Some msg)
      (OWN: Promises.mem loc to promises1):
      fulfill promises1 mem1 loc to msg (Promises.unset loc to promises1)
  .


  (* Lemmas on add & split *)

  Lemma add_disjoint
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv ADD. inv ADD0. destruct r. ss. subst.
    unfold get, Cell.get, Cell.Raw.get.
    destruct (DOMap.find to1 (Cell.raw (mem1 loc))) as [[]|] eqn:X; auto.
    exfalso. eapply DISJOINT; eauto.
    - apply Interval.mem_ub. auto.
    - apply Interval.mem_ub. eapply Cell.WF. eauto.
  Qed.

  Lemma add_get1
        mem1 loc from1 to1 msg1 mem2
        l t m
        (ADD: add mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem1 = Some m):
    get l t mem2 = Some m.
  Proof.
    exploit add_disjoint; eauto. i.
    unfold get, Cell.get, Cell.Raw.get in *. inv ADD. inv ADD0.
    unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite DOMap.gsspec. condtac; auto. subst.
    congruence.
  Qed.

  Lemma add_get2
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    get loc to1 mem2 = Some msg1.
  Proof.
    unfold get, Cell.get, Cell.Raw.get in *. inv ADD. inv ADD0.
    unfold LocFun.add, LocFun.find. condtac; [|congruence].
    rewrite <- H0. rewrite DOMap.gss. auto.
  Qed.

  Lemma add_get_inv
        mem1 loc from1 to1 msg1 mem2
        l t m
        (ADD: add mem1 loc from1 to1 msg1 mem2)
        (GET: get l t mem2 = Some m):
    (l = loc /\ t = to1 /\ m = msg1) \/ get l t mem1 = Some m.
  Proof.
    unfold get, Cell.get, Cell.Raw.get in *. inv ADD. inv ADD0.
    revert GET. unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite DOMap.gsspec. condtac; auto. subst.
    s. i. inv GET. auto.
  Qed.

  Lemma split_disjoint
        mem1 loc from1 to1 to2 msg1 mem2
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv SPLIT. inv SPLIT0. destruct r. ss. subst.
    unfold get, Cell.get, Cell.Raw.get.
    destruct (DOMap.find to1 (Cell.raw (mem1 loc))) as [[]|] eqn:X; auto.
    destruct (mem1 loc).(Cell.WF).
    exfalso. eapply DISJOINT; [apply GET2|apply X| | |].
    - ii. subst. eapply Time.lt_strorder. eauto.
    - econs; eauto. apply Time.le_lteq. auto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
  Qed.

  Lemma split_get1
        mem1 loc from1 to1 to2 msg1 mem2
        l t m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem1 = Some m):
    get l t mem2 = Some m.
  Proof.
    unfold get, Cell.get, Cell.Raw.get in *. inv SPLIT. inv SPLIT0.
    unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite ? DOMap.gsspec. repeat condtac; subst; ss.
    - destruct (DOMap.find to1 (Cell.raw (mem1 loc))) as [[]|] eqn:X; inv GET.
      destruct (mem1 loc).(Cell.WF).
      exfalso. eapply DISJOINT; [apply GET2|apply X| | |].
      + ii. subst. eapply Time.lt_strorder. eauto.
      + econs; eauto. apply Time.le_lteq. auto.
      + apply Interval.mem_ub. eapply VOLUME. eauto.
    - rewrite GET2 in *. inv GET. auto.
  Qed.

  Lemma split_get2
        mem1 loc from1 to1 to2 msg1 mem2
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2):
    get loc to1 mem2 = Some msg1.
  Proof.
    unfold get, Cell.get, Cell.Raw.get in *. inv SPLIT. inv SPLIT0.
    unfold LocFun.add, LocFun.find. condtac; [|congruence].
    rewrite <- H0. rewrite DOMap.gss. auto.
  Qed.

  Lemma split_get_inv
        mem1 loc from1 to1 to2 msg1 mem2
        l t m
        (SPLIT: split mem1 loc from1 to1 to2 msg1 mem2)
        (GET: get l t mem2 = Some m):
    (l = loc /\ t = to1 /\ m = msg1) \/ get l t mem1 = Some m.
  Proof.
    unfold get, Cell.get, Cell.Raw.get in *. inv SPLIT. inv SPLIT0.
    revert GET. unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite ? DOMap.gsspec. repeat condtac; subst; ss; auto.
    - i. inv GET. auto.
    - i. inv GET. rewrite GET2. auto.
  Qed.

  Lemma future_get
        loc ts msg mem1 mem2
        (LE: future mem1 mem2)
        (GET: get loc ts mem1 = Some msg):
    get loc ts mem2 = Some msg.
  Proof.
    induction LE; auto. apply IHLE. inv H.
    - eapply add_get1; eauto.
    - eapply split_get1; eauto.
  Qed.

  Lemma splits_get
        loc ts msg mem1 mem2
        (LE: splits mem1 mem2)
        (GET: get loc ts mem1 = Some msg):
    get loc ts mem2 = Some msg.
  Proof.
    induction LE; auto. apply IHLE.
    inv H. eapply split_get1; eauto.
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
    eexists _, _. splits; eauto. eapply future_get; eauto.
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

  Lemma future_closed_promises
        promises mem1 mem2
        (CLOSED: closed_promises promises mem1)
        (FUTURE: future mem1 mem2):
    closed_promises promises mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    eexists. eapply future_get; eauto.
  Qed.

  Lemma incr_closed_timemap
        loc s ts msg mem
        (CLOSED: closed_timemap s mem)
        (GET: get loc ts mem = Some msg):
    closed_timemap (TimeMap.incr loc ts s) mem.
  Proof.
    unfold TimeMap.incr, LocFun.add, LocFun.find. ii.
    destruct (Loc.eq_dec loc0 loc).
    - destruct (Time.join_cases (s loc) ts) as [X|X]; rewrite X; eauto.
      + exploit CLOSED. i. des.
        eexists _, _. splits; eauto. subst. eauto.
      + eexists _, _. splits; eauto. reflexivity. subst loc. eauto.
    - apply CLOSED.
  Qed.

  Lemma incr_ur_closed_capability
        loc ts s msg mem
        (CLOSED: closed_capability s mem)
        (GET: get loc ts mem = Some msg):
    closed_capability (Capability.incr_ur loc ts s) mem.
  Proof.
    inv CLOSED. econs; s.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
  Qed.

  Lemma incr_rw_closed_capability
        loc ts s msg mem
        (CLOSED: closed_capability s mem)
        (GET: get loc ts mem = Some msg):
    closed_capability (Capability.incr_rw loc ts s) mem.
  Proof.
    inv CLOSED. econs; s.
    - auto.
    - eapply incr_closed_timemap; eauto.
    - eapply incr_closed_timemap; eauto.
  Qed.


  (* Lemmas on promise & fulfill *)

  Lemma promise_future
        promises1 mem1 loc from to msg promises2 mem2
        (CLOSED_PROMISES1: closed_promises promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2):
    <<CLOSED_PROMISES2: closed_promises promises2 mem2>> /\
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv PROMISE.
    - splits.
      + ii. apply Promises.set_inv in PROMISES. des.
        * subst. eexists. eapply add_get2. eauto.
        * exploit CLOSED_PROMISES1; eauto. i. des.
          eexists. eapply add_get1; eauto.
      + ii. eapply add_get_inv in MSG; eauto. des.
        * subst. inv ADD. eauto.
        * exploit CLOSED1; eauto. i. des. splits; auto.
          eapply future_closed_capability; eauto.
          econs 2; eauto. econs 1. eauto.
      + econs 2; eauto. econs 1. eauto.
    - splits.
      + ii. apply Promises.set_inv in PROMISES. des.
        * subst. eexists. eapply split_get2. eauto.
        * exploit CLOSED_PROMISES1; eauto. i. des.
          eexists. eapply split_get1; eauto.
      + ii. eapply split_get_inv in MSG; eauto. des.
        * subst. inv SPLIT. eauto.
        * exploit CLOSED1; eauto. i. des. splits; auto.
          eapply future_closed_capability; eauto.
          econs 2; eauto. econs 2. eauto.
      + econs 2; eauto. econs 2. eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx
        (CLOSED_PROMISES1: closed_promises promises1 mem1)
        (WF1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2)
        (CLOSED_PROMISES: closed_promises ctx mem1)
        (DISJOINT: Promises.disjoint promises1 ctx):
    Promises.disjoint promises2 ctx.
  Proof.
    inv PROMISE.
    - econs. i. apply Promises.set_inv in LHS. des.
      + subst. exploit CLOSED_PROMISES; eauto. i. des.
        exploit add_disjoint; eauto. congruence.
      + eapply DISJOINT; eauto.
    - econs. i. apply Promises.set_inv in LHS. des.
      + subst. exploit CLOSED_PROMISES; eauto. i. des.
        exploit split_disjoint; eauto. congruence.
      + eapply DISJOINT; eauto.
  Qed.

  Lemma fulfill_future
        promises1 mem1 loc to msg promises2
        (CLOSED_PROMISES1: closed_promises promises1 mem1)
        (WF1: closed mem1)
        (FULFILL: fulfill promises1 mem1 loc to msg promises2):
    closed_promises promises2 mem1.
  Proof.
    inv FULFILL. ii. apply Promises.unset_inv in PROMISES. des.
    apply CLOSED_PROMISES1. auto.
  Qed.

  Lemma fulfill_disjoint
        promises1 mem1 loc to msg promises2 ctx
        (CLOSED_PROMISES1: closed_promises promises1 mem1)
        (WF1: closed mem1)
        (FULFILL: fulfill promises1 mem1 loc to msg promises2)
        (CLOSED_PROMISES: closed_promises ctx mem1)
        (DISJOINT: Promises.disjoint promises1 ctx):
    Promises.disjoint promises2 ctx.
  Proof.
    inv FULFILL. econs. i. apply Promises.unset_inv in LHS. des.
    eapply DISJOINT; eauto.
  Qed.

  Lemma fulfill_mon
        promises1 mem1 mem1' loc to msg promises2
        (FULFILL: fulfill promises1 mem1 loc to msg promises2)
        (FUTURE: future mem1 mem1'):
    fulfill promises1 mem1' loc to msg promises2.
  Proof.
    inv FULFILL. econs; eauto. eapply future_get; eauto.
  Qed.
End Memory.
