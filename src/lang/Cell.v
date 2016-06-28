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
    released: Capability.t;
  }.
  Definition elt: t := mk 0 Capability.bot.
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

    Definition singleton (from to:Time.t) (val:Const.t) (released:Capability.t): t :=
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
      DOMap.singleton Time.bot (Time.bot, Message.mk 0 Capability.bot).

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

    Inductive add (cell1:t) (from to:Time.t) (val:Const.t) (released:Capability.t): forall (rhs:t), Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                     (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO: Time.lt from to):
        add cell1 from to val released (DOMap.add to (from, (Message.mk val released)) cell1)
    .

    Lemma add_wf
          cell1 from to val released cell2
          (ADD: add cell1 from to val released cell2)
          (CELL1: wf cell1):
      wf cell2.
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

    Inductive update (cell1:t) (from1 from2 to:Time.t) (val:Const.t) (released1 released2:Capability.t): forall (cell2:t), Prop :=
    | update_intro
        (GET2: DOMap.find to cell1 = Some (from1, Message.mk val released1))
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REL_WF: Capability.wf released2)
        (REL_LE: Capability.le released2 released1):
        update cell1 from1 from2 to val released1 released2
               (DOMap.add to (from2, Message.mk val released2) cell1)
    .

    Lemma update_wf
          cell1 from1 from2 to val released1 released2 cell2
          (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv UPDATE. inv CELL1. econs; i.
      - rewrite ? DOMap.Facts.add_o in *.
        revert GET. condtac; i; try by inv GET; auto.
        eapply VOLUME. eauto.
      - rewrite ? DOMap.Facts.add_o in *.
        revert GET1 GET0. repeat condtac; i; repeat subst; try congr;
          (repeat match goal with
                 | [H: Some _ = Some _ |- _] => inv H
                  end);
          (try by eapply DISJOINT; eauto).
        + ii. eapply (DISJOINT to1 to2); eauto.
          eapply Interval.le_mem; try apply LHS.
          econs; ss. refl.
        + ii. eapply (DISJOINT to2 to1); eauto.
          eapply Interval.le_mem; try apply RHS.
          econs; ss. refl.
    Qed.

    Inductive remove (cell1:t) (from to:Time.t) (val:Const.t) (released:Capability.t): forall (cell2:t), Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, Message.mk val released)):
        remove cell1 from to val released (DOMap.remove to cell1)
    .

    Lemma remove_wf
          cell1 from to val released cell2
          (REMOVE: remove cell1 from to val released cell2)
          (CELL1: wf cell1):
      wf cell2.
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
      (DISJOINT0: forall from1 from2 msg1 msg2
                    (GET1: get Time.bot lhs = Some (from1, msg1))
                    (GET2: get Time.bot rhs = Some (from2, msg2)),
          False)
      (DISJOINT1: forall to1 to2 from1 from2 msg1 msg2
                    (GET1: get to1 lhs = Some (from1, msg1))
                    (GET2: get to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs.
    - i. eapply DISJOINT0; eauto.
    - i. symmetry. eapply DISJOINT1; eauto.
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
    exploit Raw.find_mem_ub; try apply lhs; eauto. i.
    exploit Raw.find_mem_ub; try apply rhs; eauto. i.
    inv DISJOINT. des; inversion x0; inversion x1; subst; try by inv FROM.
    - eapply DISJOINT0; eauto.
    - eapply DISJOINT1; eauto.
  Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint cell: disjoint bot cell.
  Proof.
    econs.
    - ii. rewrite bot_get in GET1. congr.
    - i. rewrite bot_get in GET1. congr.
  Qed.

  Definition singleton
             (from to:Time.t) (val:Const.t) (released:Capability.t)
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

  Definition add (cell1:t) (from to:Time.t) (val:Const.t) (released:Capability.t) (cell2:t): Prop :=
    Raw.add cell1 from to val released cell2.

  Definition update (cell1:t) (from1 from2 to:Time.t) (val:Const.t) (released1 released2:Capability.t) (cell2:t): Prop :=
    Raw.update cell1 from1 from2 to val released1 released2 cell2.

  Definition remove (cell1:t) (from to:Time.t) (val:Const.t) (released:Capability.t) (cell2:t): Prop :=
    Raw.remove cell1 from to val released cell2.

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
        (TO1: Time.lt from to):
    exists cell2, add cell1 from to val released cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold add. econs; eauto.
  Grab Existential Variables.
    eapply Raw.add_wf; eauto. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to val released
        (TO: Time.lt (max_ts cell1) to)
        (WF: Capability.wf released):
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

  Lemma update_exists
        cell1 from1 from2 to val released1 released2
        (GET2: get to cell1 = Some (from1, Message.mk val released1))
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REL_WF: Capability.wf released2)
        (REL_LE: Capability.le released2 released1):
    exists cell2, update cell1 from1 from2 to val released1 released2 cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold update. econs; eauto.
  Grab Existential Variables.
    eapply Raw.update_wf; eauto. econs; eauto.
  Qed.

  Lemma update_exists_le
        promises1 cell1 from1 from2 to val released1 released2 promises2
        (LE: le promises1 cell1)
        (UPDATE: update promises1 from1 from2 to val released1 released2 promises2):
    exists cell2, update cell1 from1 from2 to val released1 released2 cell2.
  Proof.
    inv UPDATE. eapply update_exists; eauto.
  Qed.

  (* Lemmas on add, update & remove *)

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

  Lemma add_get1
        cell1 from1 to1 val1 released1 cell2
        t f m
        (ADD: add cell1 from1 to1 val1 released1 cell2)
        (GET: get t cell1 = Some (f, m)):
    get t cell2 = Some (f, m).
  Proof.
    exploit add_get0; eauto. i.
    unfold get in *. inv ADD.
    rewrite DOMap.gsspec. condtac; auto. subst.
    congr.
  Qed.

  Lemma add_get2
        cell1 from1 to1 val1 released1 cell2
        (ADD: add cell1 from1 to1 val1 released1 cell2):
    get to1 cell2 = Some (from1, Message.mk val1 released1).
  Proof.
    unfold get in *. inv ADD.
    rewrite DOMap.gss. auto.
  Qed.

  Lemma add_get_inv
        cell1 from1 to1 val1 released1 cell2
        t f m
        (ADD: add cell1 from1 to1 val1 released1 cell2)
        (GET: get t cell2 = Some (f, m)):
    (t = to1 /\ f = from1 /\ m = Message.mk val1 released1) \/
    (~ t = to1 /\
     get t cell1 = Some (f, m)).
  Proof.
    unfold get in *. inv ADD.
    revert GET. rewrite <- H0. rewrite DOMap.gsspec. condtac; auto.
    i. inv GET. auto.
  Qed.

  Lemma add_inhabited
        cell1 cell2 from to val released
        (ADD: add cell1 from to val released cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    des. exploit add_get1; eauto.
  Qed.

  Lemma add_max_ts
        cell1 to val released cell2
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt))
        (ADD: add cell1 (max_ts cell1) to val released cell2):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    apply TimeFacts.antisym.
    - exploit add_get_inv; eauto. i. des.
      + subst. refl.
      + left. eapply TimeFacts.le_lt_lt.
        * eapply max_ts_spec. rewrite x1. eauto.
        * inv ADD. eauto.
    - eapply max_ts_spec. erewrite add_get2; eauto.
  Qed.

  Lemma update_get0
        cell1 from1 from2 to val released1 released2 cell2
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2):
    get to cell1 = Some (from1, Message.mk val released1).
  Proof.
    inv UPDATE. unfold get.
    destruct (DOMap.find to (raw cell1)) as [[]|] eqn:X; auto.
  Qed.

  Lemma update_get1
        cell1 from1 from2 to val released1 released2 cell2
        t f m
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
        (GET: get t cell1 = Some (f, m)):
    (f = from1 /\ t = to /\ m = Message.mk val released1 /\ get t cell2 = Some (from2, Message.mk val released2)) \/
    (~ (t = to) /\ get t cell2 = Some (f, m)).
  Proof.
    unfold get in *. destruct cell1, cell2. inv UPDATE. ss. subst.
    rewrite ? DOMap.gsspec. condtac; subst; auto.
    rewrite GET2 in GET. inv GET. auto.
  Qed.

  Lemma update_get1'
        cell1 from1 from2 to val released1 released2 cell2
        t f v r
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
        (GET: get t cell1 = Some (f, Message.mk v r)):
    exists f' r', get t cell2 = Some (f', Message.mk v r').
  Proof.
    exploit update_get1; eauto. i. des; eauto.
    inv x2. esplits; eauto.
  Qed.

  Lemma update_get2
        cell1 from1 from2 to val released1 released2 cell2
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2):
    get to cell2 = Some (from2, Message.mk val released2).
  Proof.
    unfold get in *. destruct cell1, cell2. inv UPDATE. ss. subst.
    apply DOMap.gss.
  Qed.

  Lemma update_get_inv
        cell1 from1 from2 to val released1 released2 cell2
        t f v r
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
        (GET: get t cell2 = Some (f, Message.mk v r)):
    (t = to /\ f = from2 /\ v = val /\ r = released2) \/
    (t <> to /\ get t cell1 = Some (f, Message.mk v r)).
  Proof.
    unfold get in *. destruct cell1, cell2. inv UPDATE. ss. subst.
    revert GET. rewrite ? DOMap.gsspec. condtac; subst; i; inv GET; auto.
  Qed.

  Lemma update_get_inv'
        cell1 from1 from2 to val released1 released2 cell2
        t f v r
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
        (GET: get t cell2 = Some (f, Message.mk v r)):
    exists f' r', get t cell1 = Some (f', Message.mk v r').
  Proof.
    exploit update_get_inv; eauto. i. des; eauto.
    subst. esplits. eapply update_get0. eauto.
  Qed.

  Lemma update_inhabited
        cell1 from1 from2 to val released1 released2 cell2
        (UPDATE: update cell1 from1 from2 to val released1 released2 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    des. exploit update_get1; eauto. i. des; auto.
    subst. inv UPDATE. inv FROM2.
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
