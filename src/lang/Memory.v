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
      (ADD: Cell.add (mem1 loc) from to val released r)
      (WF: Capability.wf released):
      add mem1 loc from to val released (LocFun.add loc r mem1)
  .

  Inductive update (mem1:t) (loc:Loc.t) (from1 from2 to:Time.t) (val:Const.t) (released1 released2:Capability.t): forall (mem2:t), Prop :=
  | update_intro
      r
      (UPDATE: Cell.update (mem1 loc) from1 from2 to val released1 released2 r):
      update mem1 loc from1 from2 to val released1 released2 (LocFun.add loc r mem1)
  .

  Inductive remove (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (val1:Const.t) (released1:Capability.t): forall (mem2:t), Prop :=
  | remove_intro
      r
      (REMOVE: Cell.remove (mem1 loc) from1 to1 val1 released1 r):
      remove mem1 loc from1 to1 val1 released1 (LocFun.add loc r mem1)
  .

  Inductive future_imm (mem1 mem2:t): Prop :=
  | future_imm_add
      loc from1 to1 val1 released1
      (ADD: add mem1 loc from1 to1 val1 released1 mem2)
  | future_imm_update
      loc from1 from2 to val released1 released2
      (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
  .

  Definition future := rtc future_imm.

  Inductive promise_kind :=
  | promise_kind_add
  | promise_kind_update (from1:Time.t) (released1:Capability.t)
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
      from1 released1
      (PROMISES: update promises1 loc from1 from to val released1 released promises2)
      (MEM: update mem1 loc from1 from to val released1 released mem2)
      (TS: Time.le (Capability.rw released loc) to):
      promise promises1 mem1 loc from to val released promises2 mem2 (promise_kind_update from1 released1)
  .

  Inductive write
            (promises1 mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (val1:Const.t) (released1:Capability.t)
            (promises3 mem2:t) (kind:promise_kind): Prop :=
  | write_intro
      promises2
      (PROMISE: Memory.promise promises1 mem1 loc from1 to1 val1 released1 promises2 mem2 kind)
      (REMOVE: Memory.remove promises2 loc from1 to1 val1 released1 promises3)
  .


  (* Lemmas on add, split & remove *)

  Lemma add_get0
        mem1 loc from1 to1 val1 released1 mem2
        (ADD: add mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem1 = None.
  Proof.
    inv ADD. exploit Cell.add_get0; eauto.
  Qed.

  Lemma add_get1
        mem1 loc from1 to1 val1 released1 mem2
        l t f m
        (ADD: add mem1 loc from1 to1 val1 released1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    get l t mem2 = Some (f, m).
  Proof.
    inv ADD. unfold get, LocFun.add, LocFun.find. condtac; auto. subst.
    exploit Cell.add_get1; eauto.
  Qed.

  Lemma add_get2
        mem1 loc from1 to1 val1 released1 mem2
        (ADD: add mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem2 = Some (from1, Message.mk val1 released1).
  Proof.
    inv ADD. unfold get, LocFun.add, LocFun.find. condtac; [|congr].
    exploit Cell.add_get2; eauto.
  Qed.

  Lemma add_get_inv
        mem1 loc from1 to1 val1 released1 mem2
        l t f m
        (ADD: add mem1 loc from1 to1 val1 released1 mem2)
        (GET: get l t mem2 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = Message.mk val1 released1) \/
    (~ (l = loc /\ t = to1) /\
     get l t mem1 = Some (f, m)).
  Proof.
    inv ADD. revert GET. unfold get, LocFun.add, LocFun.find. condtac; i.
    - subst. exploit Cell.add_get_inv; eauto. i. des.
      + subst. left. auto.
      + right. splits; auto. contradict x0. des. auto.
    - right. splits; auto. clear COND. contradict n. des. auto.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc from to val released
        (ADD: add mem1 loc from to val released mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    inv ADD. ii. specialize (INHABITED loc0).
    unfold get, LocFun.add, LocFun.find. condtac; auto. subst.
    eapply Cell.add_inhabited; eauto.
  Qed.

  Lemma update_get0
        mem1 loc from1 from2 to val released1 released2 mem2
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2):
    get loc to mem1 = Some (from1, Message.mk val released1).
  Proof.
    inv UPDATE. exploit Cell.update_get0; eauto.
  Qed.

  Lemma update_get1
        mem1 loc from1 from2 to val released1 released2 mem2
        l t f m
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
        (GET: get l t mem1 = Some (f, m)):
    (l = loc /\ f = from1 /\ t = to /\ m = Message.mk val released1 /\ get l t mem2 = Some (from2, Message.mk val released2)) \/
    (~ (l = loc /\ t = to) /\ get l t mem2 = Some (f, m)).
  Proof.
    unfold get in *. inv UPDATE.
    unfold LocFun.add, LocFun.find. condtac; cycle 1.
    { right. splits; ss. ii. des. auto. }
    subst. exploit Cell.update_get1; eauto. i. des.
    - left. auto.
    - right. splits; auto. contradict x0. des. auto.
  Qed.

  Lemma update_get1'
        mem1 loc from1 from2 to val released1 released2 mem2
        l t f v r
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
        (GET: get l t mem1 = Some (f, Message.mk v r)):
    exists f' r', get l t mem2 = Some (f', Message.mk v r').
  Proof.
    exploit update_get1; eauto. i. des; eauto.
    inv x3. esplits; eauto.
  Qed.

  Lemma update_get2
        mem1 loc from1 from2 to val released1 released2 mem2
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2):
    get loc to mem2 = Some (from2, Message.mk val released2).
  Proof.
    unfold get in *. inv UPDATE.
    unfold LocFun.add, LocFun.find. condtac; [|congr].
    exploit Cell.update_get2; eauto.
  Qed.

  Lemma update_get_inv
        mem1 loc from1 from2 to val released1 released2 mem2
        l t f v r
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
        (GET: get l t mem2 = Some (f, Message.mk v r)):
    (l = loc /\ t = to /\ f = from2 /\ v = val /\ r = released2) \/
    (~ (l = loc /\ t = to) /\ get l t mem1 = Some (f, Message.mk v r)).
  Proof.
    unfold get in *. inv UPDATE. revert GET.
    unfold LocFun.add, LocFun.find. condtac; cycle 1.
    { right. splits; auto. ii. des. auto. }
    subst. i. exploit Cell.update_get_inv; eauto. i. des.
    - subst. left. auto.
    - right. splits; auto. ii. des. auto.
  Qed.

  Lemma update_get_inv'
        mem1 loc from1 from2 to val released1 released2 mem2
        l t f v r
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
        (GET: get l t mem2 = Some (f, Message.mk v r)):
    exists f' r', get l t mem1 = Some (f', Message.mk v r').
  Proof.
    exploit update_get_inv; eauto. i. des; eauto.
    subst. esplits. eapply update_get0. eauto.
  Qed.

  Lemma update_inhabited
        mem1 mem2 loc from1 from2 to val released1 released2
        (UPDATE: update mem1 loc from1 from2 to val released1 released2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    inv UPDATE. ii. specialize (INHABITED loc0).
    unfold get, LocFun.add, LocFun.find. condtac; auto. subst.
    eapply Cell.update_inhabited; eauto.
  Qed.

  Lemma remove_get0
        mem1 loc from1 to1 val1 released1 mem2
        (REMOVE: remove mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem1 = Some (from1, Message.mk val1 released1).
  Proof.
    inv REMOVE. inv REMOVE0. destruct r. ss.
  Qed.

  Lemma remove_get1
        mem1 loc from1 to1 val1 released1 mem2
        l t f m
        (REMOVE: remove mem1 loc from1 to1 val1 released1 mem2)
        (GET: get l t mem1 = Some (f, m)):
    (l = loc /\ t = to1 /\ f = from1 /\ m = Message.mk val1 released1) \/ get l t mem2 = Some (f, m).
  Proof.
    exploit remove_get0; eauto. i.
    unfold get, Cell.get in *. inv REMOVE. inv REMOVE0.
    unfold LocFun.add, LocFun.find. condtac; auto. subst.
    rewrite <- H0. rewrite DOMap.grspec. condtac; auto. subst.
    rewrite x0 in GET. inv GET. left. auto.
  Qed.

  Lemma remove_get2
        mem1 loc from1 to1 val1 released1 mem2
        (REMOVE: remove mem1 loc from1 to1 val1 released1 mem2):
    get loc to1 mem2 = None.
  Proof.
    unfold get, Cell.get in *. inv REMOVE. inv REMOVE0.
    unfold LocFun.add, LocFun.find. condtac; [|congr].
    rewrite <- H0. rewrite DOMap.grs. auto.
  Qed.

  Lemma remove_get_inv
        mem1 loc from1 to1 val1 released1 mem2
        l t f m
        (REMOVE: remove mem1 loc from1 to1 val1 released1 mem2)
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
    - exploit add_get1; eauto.
    - exploit update_get1; eauto. i. des.
      + inv x3. exploit IHLE; eauto. i. des.
        inv UPDATE. inv UPDATE0.
        esplits; eauto.
        * etrans; eauto. 
        * etrans; eauto.
      + eapply IHLE; eauto.
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
    exploit future_get; eauto. i. des. eauto.
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
    - exploit add_get1; eauto. i. esplits; eauto. refl.
    - exploit update_get1; eauto. i. des.
      + inv x3. esplits; eauto. inv PROMISES. inv UPDATE. auto.
      + esplits; eauto. refl.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    get loc to promises2 = Some (from, Message.mk val released).
  Proof.
    inv PROMISE.
    - eapply add_get2; eauto.
    - eapply update_get2; eauto.
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
    - exploit add_get1; try apply GET; eauto. i. esplits; eauto. refl.
    - exploit update_get1; try apply GET; eauto. i. des.
      + inv x3. esplits; eauto. inv PROMISES. inv UPDATE. auto.
      + esplits; eauto. refl.
  Qed.

  Lemma promise_promises_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        l t f v r
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (GET: get l t promises2 = Some (f, Message.mk v r)):
    (l = loc /\ t = to /\ f = from /\ v = val /\ r = released) \/
    (~ (l = loc /\ t = to) /\ exists f' r', get l t promises1 = Some (f', Message.mk v r')).
  Proof.
    inv PROMISE.
    - exploit add_get_inv; try apply PROMISES; eauto. i. des.
      + inv x3. left. splits; auto.
      + right. splits; auto. eexists. eauto.
    - exploit update_get_inv; try apply PROMISES; eauto. i. des.
      + subst. left. splits; auto.
      + subst. right. splits; auto. esplits; eauto.
  Qed.

  Lemma promise_future0
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (INHABITED1: inhabited mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<INHABITED2: inhabited mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv PROMISE.
    - splits; eauto.
      + ii. eapply add_get_inv in LHS; eauto. des.
        * subst. eapply add_get2. eauto.
        * eapply add_get1; eauto.
      + eapply add_inhabited; eauto.
      + econs 2; eauto. econs 1; eauto.
    - splits; eauto.
      + ii. destruct msg.
        eapply update_get_inv in LHS; eauto. des.
        * subst. eapply update_get2. eauto.
        * subst. exploit update_get1; try apply MEM; try apply LE_PROMISES1; eauto. i. des; auto.
          contradict x0. auto.
      + eapply update_inhabited; eauto.
      + econs 2; eauto. econs 2; eauto.
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
    inv PROMISE.
    - econs; eauto.
      ii. eapply add_get_inv in MSG; eauto. des.
      + inv MSG2. inv MEM. eauto.
      + inv CLOSED1. exploit CLOSED; eauto. i. des. splits; auto.
        eapply future_closed_capability; eauto.
    - econs; eauto.
      ii. eapply update_get_inv in MSG; eauto. des.
      + subst. splits; auto. inv PROMISES. inv UPDATE. auto.
      + inv CLOSED1. exploit CLOSED; eauto. i. des. splits; auto.
        eapply future_closed_capability; eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to val released promises2 mem2 ctx kind
        (LE_PROMISES1: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to val released promises2 mem2 kind)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: Memory.disjoint promises1 ctx):
    <<DISJOINT: Memory.disjoint promises2 ctx>> /\
    <<LE_PROMISES: le ctx mem2>>.
  Proof.
    exploit promise_future0; try apply PROMISE; try apply CLOSED1; eauto. i. des.
    inv PROMISE.
    - splits.
      + econs. i. econs.
        { i. eapply add_get_inv in GET1; eauto. des.
          - subst. inv MEM. inv ADD. inv TO.
          - inv DISJOINT. destruct (DISJOINT0 loc0). eapply DISJOINT1; eauto.
        }
        i. eapply add_get_inv in GET1; eauto. des.
        * subst. exploit LE_PROMISES; eauto. i.
          exploit add_get1; eauto. i.
          exploit add_get2; eauto. i.
          eapply Cell.WF; eauto.
          ii. subst. exploit add_get0; eauto. congr.
        * eapply DISJOINT; eauto.
      + ii. eapply add_get1; eauto.
    - splits.
      + econs. i. econs.
        { i. destruct msg1. eapply update_get_inv in GET1; eauto. des.
          - inv MEM. inv UPDATE. inv FROM2.
          - inv DISJOINT. destruct (DISJOINT0 loc0). eapply DISJOINT1; eauto.
        }
        i. destruct msg1. eapply update_get_inv in GET1; eauto. des.
        * subst. inv PROMISES. inv UPDATE.
          eapply Interval.le_disjoint.
          { eapply DISJOINT; eauto. }
          { econs; s; try refl. apply Time.le_lteq. auto. }
        * eapply DISJOINT; eauto.
      + ii. exploit update_get1; eauto. i. des; auto. subst.
        inv PROMISES. inv UPDATE.
        exfalso. eapply Cell.disjoint_get; [apply DISJOINT| |]; eauto.
  Qed.

  Lemma remove_future
        promises1 mem1 loc from to val released promises2
        (LE_PROMISES1: le promises1 mem1)
        (REMOVE: remove promises1 loc from to val released promises2):
    <<LE_PROMISES2: le promises2 mem1>>.
  Proof.
    ii. eapply remove_get_inv in LHS; eauto. des. auto.
  Qed.

  Lemma remove_disjoint
        promises1 mem1 loc from to val released promises2 ctx
        (LE_PROMISES1: le promises1 mem1)
        (REMOVE: remove promises1 loc from to val released promises2)
        (LE_PROMISES: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>>.
  Proof.
    econs. i. econs.
    - i. eapply remove_get_inv in GET1; eauto. des.
      inv DISJOINT. destruct (DISJOINT0 loc0). eapply DISJOINT1; eauto.
    - i. eapply remove_get_inv in GET1; eauto. des.
      eapply DISJOINT; eauto.
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
    <<INHABITED2: inhabited mem2>> /\
    <<FUTURE: future mem1 mem2>>.
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
        (DISJOINT: Memory.disjoint promises1 ctx):
    <<DISJOINT: Memory.disjoint promises2 ctx>> /\
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
    apply Memory.max_timemap_spec; try apply CLOSED2.
    ii. exploit Memory.max_timemap_closed; try apply CLOSED1; eauto. i. des.
    exploit Memory.future_get; eauto. i. des.
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
        mem1 mem2 loc to val released
        (ADD: add mem1 loc (max_ts loc mem1) to val released mem2)
        (INHABITED: inhabited mem1):
    max_timemap mem2 = TimeMap.join (max_timemap mem1) (TimeMap.singleton loc to).
  Proof.
    hexploit add_inhabited; eauto. i. des.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_timemap_closed; eauto. instantiate (1 := l). i. des.
      exploit add_get_inv; eauto. i. des.
      + subst. etrans; [|apply TimeMap.join_r].
        apply TimeMap.singleton_inv. refl.
      + etrans; [|apply TimeMap.join_l].
        eapply max_ts_spec; eauto.
    - apply TimeMap.join_spec.
      + apply max_timemap_spec; auto.
        eapply future_closed_timemap.
        * apply max_timemap_closed. auto.
        * econs 2; [|econs 1]. econs 1. eauto.
      + exploit add_get2; eauto. i.
        apply TimeMap.singleton_spec. eapply max_ts_spec. eauto.
  Qed.

  Lemma add_max_capability
        mem1 mem2 loc to val released
        (ADD: add mem1 loc (max_ts loc mem1) to val released mem2)
        (INHABITED: inhabited mem1):
    max_capability mem2 = Capability.join (max_capability mem1) (Capability.singleton_ur loc to).
  Proof.
    apply Capability.ext; s.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
    - eapply add_max_timemap; eauto.
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

  Lemma update_exists
        mem1 loc from1 from2 to val released1 released2
        (GET2: get loc to mem1 = Some (from1, Message.mk val released1))
        (TO1: Time.le from1 from2)
        (TO2: Time.lt from2 to)
        (REL_WF: Capability.wf released2)
        (REL_LE: Capability.le released2 released1):
    exists mem2, update mem1 loc from1 from2 to val released1 released2 mem2.
  Proof.
    exploit Cell.update_exists; eauto. i. des.
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

  Lemma update_exists_le
        promises1 mem1 loc from1 from2 to val released1 released2 promises2
        (LE: le promises1 mem1)
        (UPDATE: update promises1 loc from1 from2 to val released1 released2 promises2):
    exists mem2, update mem1 loc from1 from2 to val released1 released2 mem2.
  Proof.
    inv UPDATE.
    exploit Cell.update_exists_le; eauto.
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

  Lemma update_exists_same
        mem1 loc from to val released
        (REL_WF: Capability.wf released)
        (GET: get loc to mem1 = Some (from, Message.mk val released))
        (LT: Time.lt from to):
    update mem1 loc from from to val released released mem1.
  Proof.
    exploit update_exists; eauto; try refl. i. des.
    cut (mem2 = mem1).
    { i. subst. auto. }
    apply ext. i.
    destruct (get loc0 ts mem2) as [[? []]|] eqn:X.
    { exploit update_get_inv; eauto. i. des; subst; auto. }
    destruct (get loc0 ts mem1) as [[? []]|] eqn:Y.
    { exploit update_get1; eauto. i. des; congr. }
    auto.
  Qed.

  Lemma promise_exists_same
        promises1 mem1 loc from to val released
        (REL_WF: Capability.wf released)
        (LE: le promises1 mem1)
        (MEM: closed mem1)
        (GET: get loc to promises1 = Some (from, Message.mk val released))
        (LT: Time.lt from to):
    promise promises1 mem1 loc from to val released promises1 mem1 (promise_kind_update from released).
  Proof.
    exploit update_exists_same; eauto. i.
    exploit update_exists_same; try apply LE; eauto. i.
    econs; eauto.
    eapply MEM. eauto.
  Qed.
End Memory.
