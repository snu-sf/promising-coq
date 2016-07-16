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

Set Implicit Arguments.


Module Message.
  Structure t := mk {
    val: Const.t;
    released: option View.t;
  }.
  Definition elt: t := mk 0 None.
End Message.

Module Cell.
  Module Raw.
    Definition t := DOMap.t (DenseOrder.t * Message.t).

    Inductive wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            (from, to) = (Time.bot, Time.bot) \/ Time.lt from to)
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

    Definition singleton (from to:Time.t) (val:Const.t) (released:option View.t): t :=
      DOMap.singleton to (from, Message.mk val released).

    Lemma singleton_wf
          from to val released
          (LT: Time.lt from to):
      wf (singleton from to val released).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Definition init: t :=
      DOMap.singleton Time.bot (Time.bot, Message.elt).

    Lemma init_wf: wf init.
    Proof.
      unfold init. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Lemma find_mem_ub
          from to msg cell
          (WF: wf cell)
          (FIND: DOMap.find to cell = Some (from, msg)):
      (from, to) = (Time.bot, Time.bot) \/
      Interval.mem (from, to) to.
    Proof.
      inv WF. exploit VOLUME; eauto. i. des; auto.
      right. econs; eauto. refl.
    Qed.

    Inductive add (cell1:t) (from to:Time.t) (val:Const.t) (released:option View.t): forall (rhs:t), Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                     (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO: Time.lt from to)
        (WF: View.opt_wf released):
        add cell1 from to val released (DOMap.add to (from, (Message.mk val released)) cell1)
    .

    Lemma add_o
          cell2 cell1 from to val released
          t
          (ADD: add cell1 from to val released cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, Message.mk val released)
      else DOMap.find t cell1.
    Proof.
      inv ADD. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma add_wf
          cell1 from to val released cell2
          (ADD: add cell1 from to val released cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (add_o to1); eauto.
        erewrite (add_o to2); eauto.
        repeat condtac; s; i.
        + inv GET1. congr.
        + inv GET1. inv ADD. hexploit DISJOINT0; eauto.
        + inv GET2. inv ADD. symmetry. hexploit DISJOINT0; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive split (cell1:t) (ts1 ts2 ts3:Time.t) (val2 val3:Const.t) (released2 released3:option View.t): forall (cell2:t), Prop :=
    | split_intro
        (GET2: DOMap.find ts3 cell1 = Some (ts1, Message.mk val3 released3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (REL_WF: View.opt_wf released2):
        split cell1 ts1 ts2 ts3 val2 val3 released2 released3
              (DOMap.add ts2 (ts1, Message.mk val2 released2)
              (DOMap.add ts3 (ts2, Message.mk val3 released3) cell1))
    .

    Lemma split_o
          cell2 cell1 ts1 ts2 ts3 val2 val3 released2 released3
          t
          (SPLIT: split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t ts2
      then Some (ts1, Message.mk val2 released2)
      else if Time.eq_dec t ts3
           then Some (ts2, Message.mk val3 released3)
           else DOMap.find t cell1.
    Proof.
      inv SPLIT. rewrite ? DOMap.gsspec.
      repeat condtac; repeat subst; try congr.
    Qed.

    Lemma split_wf
          cell2 cell1 ts1 ts2 ts3 val2 val3 released2 released3
          (SPLIT: split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite split_o; eauto. repeat condtac; auto.
        + i. inv GET. inv SPLIT. auto.
        + i. inv GET. inv SPLIT. auto.
        + i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (split_o to1); eauto.
        erewrite (split_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv GET2.
          eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET1. inv GET2.
          symmetry. eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact NEQ; eauto. i.
          eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + eapply DISJOINT; eauto.
    Qed.

    Inductive lower (cell1:t) (from to:Time.t) (val:Const.t) (released1 released2:option View.t): forall (cell2:t), Prop :=
    | update_intro
        (GET2: DOMap.find to cell1 = Some (from, Message.mk val released1))
        (TS: Time.lt from to)
        (REL_WF: View.opt_wf released2)
        (REL_LE: View.opt_le released2 released1):
        lower cell1 from to val released1 released2
              (DOMap.add to (from, Message.mk val released2) cell1)
    .

    Lemma lower_o
          cell2 cell1 from to val released1 released2
          t
          (LOWER: lower cell1 from to val released1 released2 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, Message.mk val released2)
      else DOMap.find t cell1.
    Proof.
      inv LOWER. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma lower_wf
          cell2 cell1 from to val released1 released2
          (LOWER: lower cell1 from to val released1 released2 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite lower_o; eauto. condtac; auto.
        + i. inv GET. inv LOWER. eapply VOLUME. eauto.
        + i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (lower_o to1); eauto.
        erewrite (lower_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv LOWER. eapply DISJOINT; eauto.
        + inv GET2. inv LOWER. eapply DISJOINT; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive remove (cell1:t) (from to:Time.t) (val:Const.t) (released:option View.t): forall (cell2:t), Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, Message.mk val released)):
        remove cell1 from to val released (DOMap.remove to cell1)
    .

    Lemma remove_o
          cell2 cell1 from to val released
          t
          (REMOVE: remove cell1 from to val released cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then None
      else DOMap.find t cell1.
    Proof.
      inv REMOVE. rewrite DOMap.grspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma remove_wf
          cell1 from to val released cell2
          (REMOVE: remove cell1 from to val released cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite remove_o; eauto. condtac; try congr.
        i. eapply VOLUME; eauto.
      - revert GET1 GET2.
        erewrite (remove_o to1); eauto.
        erewrite (remove_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
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

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Definition singleton
             (from to:Time.t) (val:Const.t) (released:option View.t)
             (LT: Time.lt from to): t :=
    mk (Raw.singleton_wf val released LT).

  Lemma singleton_get
        from to val released (LT:Time.lt from to)
        t:
    get t (singleton val released LT) =
    if Loc.eq_dec t to
    then Some (from, Message.mk val released)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition init: t := mk Raw.init_wf.

  Definition add (cell1:t) (from to:Time.t) (val:Const.t) (released:option View.t) (cell2:t): Prop :=
    Raw.add cell1 from to val released cell2.

  Definition split (cell1:t) (ts1 ts2 ts3:Time.t) (val2 val3:Const.t) (released2 released3:option View.t) (cell2:t): Prop :=
    Raw.split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2.

  Definition lower (cell1:t) (from to:Time.t) (val:Const.t) (released1 released2:option View.t) (cell2:t): Prop :=
    Raw.lower cell1 from to val released1 released2 cell2.

  Definition remove (cell1:t) (from to:Time.t) (val:Const.t) (released:option View.t) (cell2:t): Prop :=
    Raw.remove cell1 from to val released cell2.

  Lemma add_o
        cell2 cell1 from to val released
        t
        (ADD: add cell1 from to val released cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, Message.mk val released)
    else get t cell1.
  Proof. apply Raw.add_o. auto. Qed.

  Lemma split_o
        cell2 cell1 ts1 ts2 ts3 val2 val3 released2 released3
        t
        (SPLIT: split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2):
    get t cell2 =
    if Time.eq_dec t ts2
    then Some (ts1, Message.mk val2 released2)
    else if Time.eq_dec t ts3
         then Some (ts2, Message.mk val3 released3)
         else get t cell1.
  Proof. apply Raw.split_o. auto. Qed.

  Lemma lower_o
        cell2 cell1 from to val released1 released2
        t
        (LOWER: lower cell1 from to val released1 released2 cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, Message.mk val released2)
    else get t cell1.
  Proof. eapply Raw.lower_o. eauto. Qed.

  Lemma remove_o
        cell2 cell1 from to val released
        t
        (REMOVE: remove cell1 from to val released cell2):
    get t cell2 =
    if Time.eq_dec t to
    then None
    else get t cell1.
  Proof. eapply Raw.remove_o. eauto. Qed.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key _ cell.(raw).

  Lemma max_ts_spec
        ts from msg cell
        (GET: get ts cell = Some (from, msg)):
    <<GET: exists from val released, get (max_ts cell) cell = Some (from, Message.mk val released)>> /\
    <<MAX: Time.le ts (max_ts cell)>>.
  Proof.
    unfold get in GET.
    generalize (DOMap.max_key_spec _ cell.(Cell.raw)). i. des. splits; eauto.
    - destruct (DOMap.find
                  (DOMap.max_key (DenseOrder.t * Message.t) (Cell.raw cell))
                  (Cell.raw cell)) as [[? []]|] eqn:X.
      + esplits. eauto.
      + exfalso. eapply FIND; eauto. rewrite GET. congr.
    - apply MAX. rewrite GET. auto. congr.
  Qed.

  Lemma add_exists
        cell1 from to val released
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (WF: View.opt_wf released):
    exists cell2, add cell1 from to val released cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold add. econs; eauto.
  Grab Existential Variables.
    eapply Raw.add_wf; eauto. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to val released
        (TO: Time.lt (max_ts cell1) to)
        (WF: View.opt_wf released):
    exists cell2, add cell1 (max_ts cell1) to val released cell2.
  Proof.
    apply add_exists; auto. i.
    exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO1. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 cell1 from to val released cell2
        (LE: le promises1 cell1)
        (ADD: add cell1 from to val released cell2):
    exists promises2, add promises1 from to val released promises2.
  Proof.
    inv ADD. apply add_exists; auto. i.
    eapply DISJOINT. eauto.
  Qed.

  Lemma split_exists
        cell1 ts1 ts2 ts3 val2 val3 released2 released3
        (GET2: get ts3 cell1 = Some (ts1, Message.mk val3 released3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (REL_WF: View.opt_wf released2):
    exists cell2, split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold split. econs; eauto.
  Grab Existential Variables.
    eapply Raw.split_wf; eauto. econs; eauto.
  Qed.

  Lemma split_exists_le
        promises1 cell1 ts1 ts2 ts3 val2 val3 released2 released3 promises2
        (LE: le promises1 cell1)
        (SPLIT: split promises1 ts1 ts2 ts3 val2 val3 released2 released3 promises2):
    exists cell2, split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2.
  Proof.
    inv SPLIT. eapply split_exists; eauto.
  Qed.

  Lemma lower_exists
        cell1 from to val released1 released2
        (GET2: get to cell1 = Some (from, Message.mk val released1))
        (TS: Time.lt from to)
        (REL_WF: View.opt_wf released2)
        (REL_LE: View.opt_le released2 released1):
    exists cell2, lower cell1 from to val released1 released2 cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold lower. econs; eauto.
  Grab Existential Variables.
    eapply Raw.lower_wf; eauto. econs; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 cell1 from to val released1 released2 promises2
        (LE: le promises1 cell1)
        (LOWER: lower promises1 from to val released1 released2 promises2):
    exists cell2, lower cell1 from to val released1 released2 cell2.
  Proof.
    inv LOWER. apply lower_exists; auto.
  Qed.

  (* Lemmas on add, split, lower & remove *)

  Lemma add_get0
        cell1 from1 to1 val1 released1 cell2
        (ADD: add cell1 from1 to1 val1 released1 cell2):
    get to1 cell1 = None.
  Proof.
    inv ADD. unfold get.
    destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
    exfalso. exploit DISJOINT; eauto.
    - apply Interval.mem_ub. auto.
    - apply Interval.mem_ub.
      destruct cell1.(Cell.WF). exploit VOLUME; eauto. i. des; ss.
      inv x. inv TO.
  Qed.

  Lemma split_get0
        cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2):
    <<GET2: get ts2 cell1 = None>> /\
    <<GET3: get ts3 cell1 = Some (ts1, Message.mk val3 released3)>>.
  Proof.
    inv SPLIT. splits; auto.
    destruct (get ts2 cell1) as [[]|] eqn:X; auto.
    destruct cell1.(WF). exfalso. eapply DISJOINT.
    - apply X.
    - apply GET2.
    - ii. subst. eapply Time.lt_strorder. eauto.
    - apply Interval.mem_ub. exploit VOLUME; eauto. i. des; auto.
      inv x. inv TS12.
    - econs; ss. left. auto.
  Qed.

  Lemma lower_get0
        cell1 from to val released1 released2 cell2
        (LOWER: lower cell1 from to val released1 released2 cell2):
    get to cell1 = Some (from, Message.mk val released1).
  Proof. inv LOWER. auto. Qed.

  Lemma remove_get0
        cell1 from to val released cell2
        (REMOVE: remove cell1 from to val released cell2):
    get to cell1 = Some (from, Message.mk val released).
  Proof. inv REMOVE. auto. Qed.

  Lemma add_inhabited
        cell1 cell2 from to val released
        (ADD: add cell1 from to val released cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite add_o; eauto. condtac; auto. subst.
    inv ADD. inv TO.
  Qed.

  Lemma split_inhabited
        cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 val2 val3 released2 released3 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite split_o; eauto. repeat condtac; subst; ss.
    - inv SPLIT. inv TS12.
    - inv SPLIT. inv TS23.
  Qed.

  Lemma lower_inhabited
        cell1 from to val released1 released2 cell2
        (LOWER: lower cell1 from to val released1 released2 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite lower_o; eauto. condtac; auto.
    subst. inv LOWER. inv TS.
  Qed.

  Lemma add_max_ts
        cell1 to val released cell2
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt))
        (ADD: add cell1 (max_ts cell1) to val released cell2):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    revert GET. erewrite add_o; eauto. condtac; auto. i.
    apply TimeFacts.antisym.
    - left. eapply TimeFacts.le_lt_lt.
      + eapply max_ts_spec. eauto.
      + inv ADD. auto.
    - eapply max_ts_spec. erewrite add_o; eauto. condtac; ss. congr.
  Qed.

  Lemma remove_singleton
        from to val released (LT:Time.lt from to):
    remove (singleton val released LT) from to val released bot.
  Proof.
    assert (Raw.bot = DOMap.remove to ((singleton val released LT).(raw))).
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
        cell1 from to val released
        (GET: get to cell1 = Some (from, Message.mk val released)):
    exists cell2, remove cell1 from to val released cell2.
  Proof.
    eexists (mk _). destruct cell1. ss.
    Grab Existential Variables.
    { eapply Raw.remove_wf.
      - econs. eauto.
      - apply WF.
    }
  Qed.
End Cell.
