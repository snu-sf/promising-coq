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

  Definition eq := @eq t.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (lhs loc) (rhs loc).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. refl. Qed.
  Next Obligation. ii. etrans; eauto. Qed.

  Definition bot: t := fun _ => Time.bot.

  Lemma bot_spec (tm:t): le bot tm.
  Proof. ii. apply Time.bot_spec. Qed.

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

  Definition singleton loc ts :=
    LocFun.add loc ts (LocFun.init Time.bot).

  Lemma singleton_spec loc ts c
        (LOC: Time.le ts (c loc)):
    le (singleton loc ts) c.
  Proof.
    ii. unfold singleton, LocFun.add, LocFun.find.
    condtac; subst; ss. apply Time.bot_spec.
  Qed.

  Lemma singleton_inv loc ts c
        (LE: le (singleton loc ts) c):
    Time.le ts (c loc).
  Proof.
    generalize (LE loc). unfold singleton, LocFun.add, LocFun.find.
    condtac; [|congr]. auto.
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

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality loc. apply TimeFacts.antisym; auto.
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

  Lemma ext l r
        (UR: l.(ur) = r.(ur))
        (RW: l.(rw) = r.(rw))
        (SC: l.(sc) = r.(sc)):
    l = r.
  Proof.
    destruct l, r. f_equal; auto.
  Qed.

  Definition bot: t := mk TimeMap.bot TimeMap.bot TimeMap.bot.

  Lemma bot_wf: wf bot.
  Proof. econs; refl. Qed.

  Lemma bot_spec (c:t): le bot c.
  Proof. econs; apply TimeMap.bot_spec. Qed.

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

  Definition bot_unless (cond:bool) (c:t): t :=
    if cond then c else bot.

  Lemma bot_unless_wf
        cond c
        (WF: wf c):
    wf (bot_unless cond c).
  Proof.
    destruct cond; ss. apply bot_wf.
  Qed.

  Definition singleton_ur loc ts :=
    mk (TimeMap.singleton loc ts)
       (TimeMap.singleton loc ts)
       (TimeMap.singleton loc ts).

  Lemma singleton_ur_wf
        loc ts:
    wf (singleton_ur loc ts).
  Proof.
    econs; ss; refl.
  Qed.

  Lemma singleton_ur_spec loc ts c
        (WF: wf c)
        (TS: Time.le ts (c.(ur) loc)):
    le (singleton_ur loc ts) c.
  Proof.
    econs; s;
      try apply TimeMap.bot_spec;
      try apply TimeMap.singleton_spec; auto.
    - etrans; eauto. apply WF.
    - etrans; eauto. etrans; apply WF.
  Qed.

  Lemma singleton_ur_inv loc ts c
        (LE: le (singleton_ur loc ts) c):
    Time.le ts (c.(ur) loc).
  Proof.
    apply TimeMap.singleton_inv. apply LE.
  Qed.

  Definition singleton_rw loc ts :=
    mk TimeMap.bot
       (TimeMap.singleton loc ts)
       (TimeMap.singleton loc ts).

  Lemma singleton_rw_wf
        loc ts:
    wf (singleton_rw loc ts).
  Proof.
    econs; ss; try refl. apply TimeMap.bot_spec.
  Qed.

  Lemma singleton_rw_spec loc ts c
        (WF: wf c)
        (TS: Time.le ts (c.(rw) loc)):
    le (singleton_rw loc ts) c.
  Proof.
    econs; s;
      try apply TimeMap.bot_spec;
      try apply TimeMap.singleton_spec; auto.
    etrans; eauto. apply WF.
  Qed.

  Lemma singleton_rw_inv loc ts c
        (LE: le (singleton_rw loc ts) c):
    Time.le ts (c.(rw) loc).
  Proof.
    apply TimeMap.singleton_inv. apply LE.
  Qed.

  Definition singleton_sc loc ts :=
    mk TimeMap.bot
       TimeMap.bot
       (TimeMap.singleton loc ts).

  Lemma singleton_sc_wf
        loc ts:
    wf (singleton_sc loc ts).
  Proof.
    econs; ss; try refl. apply TimeMap.bot_spec.
  Qed.

  Lemma singleton_sc_spec loc ts c
        (WF: wf c)
        (TS: Time.le ts (c.(sc) loc)):
    le (singleton_sc loc ts) c.
  Proof.
    econs; s;
      try apply TimeMap.bot_spec;
      try apply TimeMap.singleton_spec; auto.
  Qed.

  Lemma singleton_sc_inv loc ts c
        (LE: le (singleton_sc loc ts) c):
    Time.le ts (c.(sc) loc).
  Proof.
    apply TimeMap.singleton_inv. apply LE.
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

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    destruct l, r. inv LR. inv RL. ss. f_equal.
    - apply TimeMap.antisym; auto.
    - apply TimeMap.antisym; auto.
    - apply TimeMap.antisym; auto.
  Qed.

  Lemma timemap_le_le tm1 tm2
        (LE: TimeMap.le tm1 tm2):
    le (mk tm1 tm1 tm1) (mk tm2 tm2 tm2).
  Proof. econs; eauto. Qed.
End Capability.
