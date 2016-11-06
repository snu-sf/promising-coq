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


Definition loc_ts_eq_dec (lhs rhs:Loc.t * Time.t):
  {lhs.(fst) = rhs.(fst) /\ lhs.(snd) = rhs.(snd)} +
  {lhs.(fst) <> rhs.(fst) \/ lhs.(snd) <> rhs.(snd)}.
Proof.
  destruct lhs, rhs.
  destruct (Loc.eq_dec t t1), (Time.eq_dec t0 t2); subst; auto.
Defined.
Global Opaque loc_ts_eq_dec.

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

  Definition add (l:Loc.t) (ts:Time.t) (tm:t): t :=
    fun l' =>
      if Loc.eq_dec l' l
      then ts
      else get l' tm.

  Definition add_spec l' l ts tm:
    get l' (add l ts tm) =
    if Loc.eq_dec l' l
    then ts
    else get l' tm.
  Proof. auto. Qed.

  Lemma add_spec_eq l ts tm:
    get l (add l ts tm) = ts.
  Proof.
    rewrite add_spec.
    destruct (Loc.eq_dec l l); auto.
    congruence.
  Qed.

  Lemma add_spec_neq l' l ts tm (NEQ: l' <> l):
    get l' (add l ts tm) = get l' tm.
  Proof.
    rewrite add_spec.
    destruct (Loc.eq_dec l' l); auto.
    congruence.
  Qed.

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

Module View <: JoinableType.
  Structure t_ := mk {
    pln: TimeMap.t;
    rlx: TimeMap.t;
  }.
  Definition t := t_.

  Inductive wf (view:t): Prop :=
  | wf_intro
      (PLN_RLX: TimeMap.le view.(pln) view.(rlx))
  .

  Inductive opt_wf: forall (view:option View.t), Prop :=
  | opt_wf_some
      view
      (WF: wf view):
      opt_wf (Some view)
  | opt_wf_none:
      opt_wf None
  .

  Definition eq := @eq t.

  Inductive le_ (lhs rhs:t): Prop :=
  | le_intro
      (PLN: TimeMap.le lhs.(pln) rhs.(pln))
      (RLX: TimeMap.le lhs.(rlx) rhs.(rlx))
  .
  Definition le := le_.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Inductive opt_le: forall (lhs rhs:option t), Prop :=
  | opt_le_none
      rhs:
      opt_le None rhs
  | opt_le_some
      lhs rhs
      (LE: le lhs rhs):
      opt_le (Some lhs) (Some rhs)
  .

  Global Program Instance opt_le_PreOrder: PreOrder opt_le.
  Next Obligation.
    ii. destruct x; econs. refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; econs. etrans; eauto.
  Qed.

  Lemma ext l r
        (PLN: l.(pln) = r.(pln))
        (RLX: l.(rlx) = r.(rlx))
    : l = r.
  Proof.
    destruct l, r. f_equal; auto.
  Qed.

  Definition bot: t := mk TimeMap.bot TimeMap.bot.

  Lemma bot_wf: wf bot.
  Proof. econs; refl. Qed.

  Lemma bot_spec (c:t): le bot c.
  Proof. econs; apply TimeMap.bot_spec. Qed.

  Definition join (lhs rhs:t): t :=
    mk (TimeMap.join lhs.(pln) rhs.(pln))
       (TimeMap.join lhs.(rlx) rhs.(rlx)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. unfold join. f_equal; apply TimeMap.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    unfold join. ss. f_equal.
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
       (TimeMap.singleton loc ts).

  Lemma singleton_ur_wf
        loc ts:
    wf (singleton_ur loc ts).
  Proof.
    econs; ss; refl.
  Qed.

  Lemma singleton_ur_spec loc ts c
        (WF: wf c)
        (TS: Time.le ts (c.(pln) loc)):
    le (singleton_ur loc ts) c.
  Proof.
    econs; s;
      try apply TimeMap.bot_spec;
      try apply TimeMap.singleton_spec; auto.
    - etrans; eauto. apply WF.
  Qed.

  Lemma singleton_ur_inv loc ts c
        (LE: le (singleton_ur loc ts) c):
    Time.le ts (c.(pln) loc).
  Proof.
    apply TimeMap.singleton_inv. apply LE.
  Qed.

  Definition singleton_rw loc ts :=
    mk TimeMap.bot
       (TimeMap.singleton loc ts).

  Lemma singleton_rw_wf
        loc ts:
    wf (singleton_rw loc ts).
  Proof.
    econs; ss; try refl. apply TimeMap.bot_spec.
  Qed.

  Lemma singleton_rw_spec loc ts c
        (WF: wf c)
        (TS: Time.le ts (c.(rlx) loc)):
    le (singleton_rw loc ts) c.
  Proof.
    econs; s;
      try apply TimeMap.bot_spec;
      try apply TimeMap.singleton_spec; auto.
  Qed.

  Lemma singleton_rw_inv loc ts c
        (LE: le (singleton_rw loc ts) c):
    Time.le ts (c.(rlx) loc).
  Proof.
    apply TimeMap.singleton_inv. apply LE.
  Qed.

  Definition singleton_ur_if (cond:bool) loc ts :=
    (if cond then singleton_ur else singleton_rw) loc ts.

  Lemma singleton_ur_if_wf
        cond loc ts:
    wf (singleton_ur_if cond loc ts).
  Proof.
    destruct cond; ss.
    - apply singleton_ur_wf.
    - apply singleton_rw_wf.
  Qed.

  Lemma singleton_ur_if_spec (cond:bool) loc ts c
        (WF: wf c)
        (TS: Time.le ts ((if cond then c.(pln) else c.(rlx)) loc)):
    le (singleton_ur_if cond loc ts) c.
  Proof.
    destruct cond; ss.
    - apply singleton_ur_spec; ss.
    - apply singleton_rw_spec; ss.
  Qed.

  Lemma singleton_ur_if_inv cond loc ts c
        (LE: le (singleton_ur_if cond loc ts) c):
    Time.le ts ((if cond then c.(pln) else c.(rlx)) loc).
  Proof.
    destruct cond; ss.
    - apply singleton_ur_inv. ss.
    - apply singleton_rw_inv. ss.
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
  Qed.

  Lemma opt_antisym l r
        (LR: opt_le l r)
        (RL: opt_le r l):
    l = r.
  Proof.
    inv LR; inv RL; ss. f_equal.
    apply antisym; ss.
  Qed.

  Lemma timemap_le_le tm1 tm2
        (LE: TimeMap.le tm1 tm2):
    le (mk tm1 tm1) (mk tm2 tm2).
  Proof. econs; eauto. Qed.

  Definition unwrap (view:option t): t :=
    match view with
    | Some view => view
    | None => bot
    end.

  Lemma unwrap_opt_wf
        view
        (WF: opt_wf view):
    wf view.(unwrap).
  Proof.
    inv WF; ss. apply bot_wf.
  Qed.

  Lemma unwrap_opt_le
        view1 view2
        (WF: opt_le view1 view2):
    le view1.(unwrap) view2.(unwrap).
  Proof.
    inv WF; ss. apply bot_spec.
  Qed.

  Lemma opt_None_spec rhs:
    opt_le None rhs.
  Proof. econs. Qed.

  Lemma join_bot_l rhs:
    join bot rhs = rhs.
  Proof.
    apply antisym.
    - apply join_spec.
      + apply bot_spec.
      + refl.
    - apply join_r.
  Qed.
End View.
