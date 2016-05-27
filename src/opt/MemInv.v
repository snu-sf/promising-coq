Require Import RelationClasses.
Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import DenseOrder.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (SPLITS: Memory.splits mem_tgt mem_src)
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation. ii. econs. refl. Qed.
Next Obligation. ii. inv H. inv H0. econs. etrans; eauto. Qed.

Lemma sim_memory_get
      mem_src mem_tgt
      loc from to msg
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.get loc to mem_tgt = Some (from, msg)):
  exists from', Memory.get loc to mem_src = Some (from', msg).
Proof.
  eapply Memory.splits_get; eauto. apply SIM.
Qed.

Module MemInv.
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
      congr.
  Qed.

  Lemma set_eq loc ts promises:
    mem loc ts (set loc ts promises) = true.
  Proof.
    rewrite set_o.
    destruct (Loc.eq_dec loc loc); [|congr].
    destruct (Time.eq_dec ts ts); [|congr].
    auto.
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
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts2); [|congr].
      apply Bool.andb_false_iff. auto.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. destruct (Time.eq_dec ts2 ts1); ss; [congr|].
      apply Bool.andb_true_r.
  Qed.

  Lemma unset_eq loc ts promises:
    mem loc ts (unset loc ts promises) = false.
  Proof.
    rewrite unset_o.
    destruct (Loc.eq_dec loc loc); [|congr].
    destruct (Time.eq_dec ts ts); [|congr].
    auto.
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

  Lemma unset_set loc to inv
        (MEM: mem loc to inv = false):
    unset loc to (set loc to inv) = inv.
  Proof.
    apply ext. i.
    rewrite unset_o, set_o.
    destruct (Loc.eq_dec loc0 loc), (Time.eq_dec ts to); ss; splits; auto.
    subst. auto.
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

  Inductive sem (inv:t) (promises_src promises_tgt:Memory.t): Prop :=
  | sem_intro
      (LE: Memory.le promises_tgt promises_src)
      (GET: forall loc ts (MEM: mem loc ts inv),
          Memory.get loc ts promises_src <> None /\ Memory.get loc ts promises_tgt = None)
      (MEM: forall loc ts
              (SRC: Memory.get loc ts promises_src <> None)
              (TGT: Memory.get loc ts promises_tgt = None),
          mem loc ts inv)
  .

  Lemma promise
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        (PROMISES_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE_SRC1: Memory.le promises1_src mem1_src)
        (LE_TGT1: Memory.le promises1_tgt mem1_tgt)
        (CLOSED_SRC1: Memory.closed mem1_src)
        (CLOSED_TGT1: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISES_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<LE_SRC1: Memory.le promises2_src mem2_src>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
  Admitted.

  Lemma fulfill_tgt
        inv
        promises1_src
        promises1_tgt promises2_tgt
        loc from to msg
        (FULFILL_TGT: Memory.fulfill promises1_tgt loc from to msg promises2_tgt)
        (INV: sem inv promises1_src promises1_tgt):
    sem (set loc to inv) promises1_src promises2_tgt.
  Proof.
  Admitted.

  Lemma fulfill_src
        inv
        promises1_src
        promises1_tgt
        loc from to msg
        (TGT: Memory.get loc to promises1_tgt = None)
        (INV1: sem inv promises1_src promises1_tgt):
    exists promises2_src,
      <<FULFILL_SRC: Memory.fulfill promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem (unset loc to inv) promises2_src promises1_tgt>>.
  Proof.
  Admitted.

  Lemma fulfill
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (FULFILL_TGT: Memory.fulfill promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE_SRC1: Memory.le promises1_src mem1_src)
        (LE_TGT1: Memory.le promises1_tgt mem1_tgt)
        (CLOSED_SRC1: Memory.closed mem1_src)
        (CLOSED_TGT1: Memory.closed mem1_tgt):
    exists promises2_src,
      <<FULFILL_SRC: Memory.fulfill promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem inv promises2_src promises2_tgt>>.
  Proof.
    exploit fulfill_tgt; eauto. i.
    exploit fulfill_src; eauto.
    { inv x0. eapply GET; eauto. apply set_eq. }
    i. des.
    eexists. splits; eauto.
    rewrite unset_set in INV2; auto.
    admit.
  Admitted.

  Lemma future
        inv
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (INV1: sem inv promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE_SRC1: Memory.le promises_src mem1_src)
        (LE_TGT1: Memory.le promises_tgt mem1_tgt)
        (LE_SRC2: Memory.le promises_src mem2_src):
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_src>> /\
      <<WF2_PROMISES_TGT: Memory.le promises_tgt mem2_src>>.
  Proof.
    splits.
    - etrans; eauto. apply Memory.splits_future. apply SIM1.
    - etrans; [apply INV1|]. eauto.
  Qed.

  Lemma sem_bot promises:
    sem bot promises promises.
  Proof.
    econs.
    - refl.
    - i. rewrite bot_spec in MEM. done.
    - congr.
  Qed.

  Lemma sem_bot_inv
        promises
        (SEM: sem bot promises Memory.bot):
    promises = Memory.bot.
  Proof.
    extensionality loc. apply Cell.ext. s.
    apply DOMap.eq_leibniz. ii.
    unfold Cell.Raw.bot. rewrite DOMap.gempty.
    destruct (DOMap.find y (Cell.raw (promises loc))) eqn:X; auto.
    inv SEM.  exploit MEM.
    - unfold Memory.get, Cell.get. rewrite X. congr.
    - apply Memory.bot_get.
    - i. rewrite bot_spec in x. congr.
  Qed.
End MemInv.
