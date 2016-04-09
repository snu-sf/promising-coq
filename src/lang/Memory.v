Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.

Set Implicit Arguments.


Module Times.
  Definition t := LocFun.t Time.t.
  Definition init: t := LocFun.init Time.elt.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (LocFun.find loc lhs) (LocFun.find loc rhs).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. reflexivity. Qed.
  Next Obligation. ii. etransitivity; eauto. Qed.

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Times.

Module Snapshot.
  Structure t := mk {
    reads: Times.t;
    writes: Times.t;
  }.

  Definition init: t := mk Times.init Times.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (READS: Times.le lhs.(reads) rhs.(reads))
      (WRITES: Times.le lhs.(writes) rhs.(writes))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etransitivity; eauto.
  Qed.

  Inductive readable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | readable_intro
      (* (CoRR: Time.le (Times.get loc history.(Snapshot.reads)) ts) *)
      (CoWR: Time.le (Times.get loc history.(Snapshot.writes)) ts)
  .

  Inductive writable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | writable_intro
      (CoRW: Time.lt (Times.get loc history.(Snapshot.reads)) ts)
      (CoWW: Time.lt (Times.get loc history.(Snapshot.writes)) ts)
  .
End Snapshot.

Module Message.
  Structure t := mk {
    val: Const.t;
    released: Snapshot.t;
  }.
  Definition elt: t := mk 0 Snapshot.init.
End Message.

Module Cell.
  Structure t := mk {
    messages: Time.t -> (option (Time.t * Message.t));

    VOLUME:
      forall to from msg
        (MESSAGE: messages to = Some (from, msg)),
        Time.lt from to;
    DISJOINT:
      forall to1 to2 from1 from2 msg1 msg2
        (TO: to1 <> to2)
        (MESSAGE1: messages to1 = Some (from1, msg1))
        (MESSAGE2: messages to2 = Some (from2, msg2)),
        Interval.disjoint (from1, to1) (from2, to2);
    DOMAIN:
      exists tos,
      forall to from msg (MSG: messages to = Some (from, msg)),
        List.In to tos;
  }.

  Definition get (to:Time.t) (cell:t): option Message.t :=
    option_map snd (cell.(messages) to).

  Lemma extensionality lhs rhs
        (MESSAGES: forall x, lhs.(messages) x = rhs.(messages) x):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    cut (messages0 = messages1).
    { i. subst. f_equal; apply proof_irrelevance. }
    extensionality to. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg (MSG: lhs.(messages) to = Some (from, msg)),
      rhs.(messages) to = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. apply H0. apply H. auto. Qed.

  Inductive own (cell:t) (ts:Time.t): Prop :=
  | own_intro
      to from msg
      (MESSAGE: cell.(messages) to = Some (from, msg))
      (INTERVAL: Interval.mem (from, to) ts)
  .

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall ts (LHS: own lhs ts) (RHS: own rhs ts), False)
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. eapply DISJOINT0; eauto.
  Qed.

  Lemma disjoint_messages
        to lhs rhs lx rx
        (DISJ: disjoint lhs rhs)
        (LHS: lhs.(messages) to = Some lx)
        (RHS: rhs.(messages) to = Some rx):
    False.
  Proof.
    destruct lx, rx.
    eapply DISJ; econs; eauto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
    - apply Interval.mem_ub. eapply VOLUME. eauto.
  Qed.

  Program Definition init: t :=
    mk
      (TimeFun.add Time.elt (Some (Time.decr Time.elt, Message.mk 0 Snapshot.init)) (TimeFun.init None))
      _ _ _.
  Next Obligation.
    unfold TimeFun.add in *.
    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end;
      inv MESSAGE.
    apply Time.decr_spec.
  Qed.
  Next Obligation.
    unfold TimeFun.add in *.
    repeat match goal with
           | [H: context[if ?c then _ else _] |- _] => destruct c
           end;
      subst; inv MESSAGE1; inv MESSAGE2.
    congruence.
  Qed.
  Next Obligation.
    exists [Time.elt]. i.
    unfold TimeFun.add in *.
    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end;
      subst; inv MSG.
    econs. auto.
  Qed.

  Inductive declare (from to:Time.t) (msg:Message.t) (cell1 cell2:t): Prop :=
  | declare_add
      (MESSAGES1: cell1.(messages) to = None)
      (MESSAGES2: cell2.(messages) = TimeFun.add to (Some (from, msg)) cell1.(messages))
  | declare_split
      msg' middle
      (MESSAGES1: cell1.(messages) to = Some (from, msg'))
      (MESSAGES2: cell2.(messages) =
                  TimeFun.add middle (Some (from, msg))
                              (TimeFun.add to (Some (middle, msg)) cell1.(messages)))
  .

  Inductive future (lhs rhs:t): Prop :=
  | future_intro
      (MESSAGES:
         forall to from_lhs msg
           (LHS: lhs.(messages) to = Some (from_lhs, msg)),
         exists from_rhs,
           rhs.(messages) to = Some (from_rhs, msg))
      (OWNERSHIP: own lhs <1= own rhs)
  .

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation.
    ii. econs; i; eauto.
  Qed.
  Next Obligation.
    ii. inv H; inv H0. econs; i.
    - exploit MESSAGES; eauto. i. des.
      eapply MESSAGES0; eauto.
    - exploit OWNERSHIP; eauto.
  Qed.

  Lemma declare_future
        from to msg cell1 cell2
        (DECLARE: declare from to msg cell1 cell2):
    future cell1 cell2.
  Proof.
  Admitted.

  Program Definition remove (to:Time.t) (cell:t): t :=
    mk (TimeFun.add to None cell.(messages)) _ _ _.
  Next Obligation.
    unfold TimeFun.add in *.    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end; inv MESSAGE.
    eapply VOLUME; eauto.
  Qed.
  Next Obligation.
    unfold TimeFun.add in *.    repeat match goal with
           | [H: context[if ?c then _ else _] |- _] => destruct c
           end;
      inv MESSAGE1; inv MESSAGE2.
    eapply DISJOINT; eauto.
  Qed.
  Next Obligation.
    generalize (DOMAIN cell). i. des.
    exists tos. i.
    unfold TimeFun.add in *.    match goal with
    | [H: context[if ?c then _ else _] |- _] => destruct c
    end; inv MSG.
    eapply H; eauto.
  Qed.
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (to:Time.t) (mem:t): option Message.t :=
    Cell.get to (mem loc).

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (LE: forall loc, Cell.le (lhs loc) (rhs loc))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. econs. intro loc. reflexivity. Qed.
  Next Obligation. econs. inv H. inv H0. intro loc. etransitivity; eauto. Qed.

  Definition own (mem:t) (loc:Loc.t) (to:Time.t): Prop :=
    Cell.own (mem loc) to.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc, Cell.disjoint (lhs loc) (rhs loc))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. symmetry. apply DISJOINT.
  Qed.

  Definition init: t := LocFun.init Cell.init.

  Inductive declare (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem1:t): forall (mem2:t), Prop :=
  | declare_intro
      cell2
      (ALLOC: Cell.declare from to msg (mem1 loc) cell2):
      declare loc from to msg mem1 (LocFun.add loc cell2 mem1)
  .

  Inductive future (lhs rhs:t): Prop :=
  | future_intro
      (FUTURE: forall loc, Cell.future (lhs loc) (rhs loc))
  .

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation. econs. intros loc. reflexivity. Qed.
  Next Obligation. econs. inv H. inv H0. intros loc. etransitivity; eauto. Qed.

  Lemma declare_future
        loc from to msg mem1 mem2
        (DECLARE: declare loc from to msg mem1 mem2):
    future mem1 mem2.
  Proof.
    econs. intro loc'.
    inv DECLARE. unfold LocFun.add.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c
    end.
    - subst. eapply Cell.declare_future; eauto.
    - reflexivity.
  Qed.

  Definition remove (loc:Loc.t) (to:Time.t) (mem:t): t :=
    LocFun.add loc (Cell.remove to (mem loc)) mem.
End Memory.
