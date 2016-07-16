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
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Module SimPromises.
  Definition t := Loc.t -> DOSet.t.

  Definition mem loc ts (promises:t) := DOSet.mem ts (promises loc).

  Lemma ext lhs rhs
        (EXT: forall loc ts, mem loc ts lhs = mem loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. unfold LocFun.find. i.
    apply DOSet.eq_leibniz. ii.
    specialize (EXT i a). unfold mem in *. econs; i.
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
    apply LocFun.ext. unfold LocFun.find, join. i.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply LocFun.ext. unfold LocFun.find, join. i.
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
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then true
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, set, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq. auto.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
  Qed.

  Lemma set_eq loc ts promises:
    mem loc ts (set loc ts promises) = true.
  Proof.
    rewrite set_o. condtac; ss. des; congr.
  Qed.

  Lemma set_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (set loc2 ts2 promises)):
    (loc1 = loc2 /\ ts1 = ts2) \/ mem loc1 ts1 promises.
  Proof.
    revert MEM. rewrite set_o. repeat condtac; ss; auto.
  Qed.

  Definition unset (loc:Loc.t) (ts:Time.t) (promises:t) :=
    LocFun.add loc (DOSet.remove ts (promises loc)) promises.

  Lemma unset_o loc1 ts1 loc2 ts2 promises:
    mem loc1 ts1 (unset loc2 ts2 promises) =
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then false
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, unset, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq.
      apply Bool.andb_false_iff. auto.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
      apply Bool.andb_true_r.
  Qed.

  Lemma unset_eq loc ts promises:
    mem loc ts (unset loc ts promises) = false.
  Proof.
    rewrite unset_o. condtac; ss. des; congr.
  Qed.

  Lemma unset_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (unset loc2 ts2 promises)):
    ~ (loc1 = loc2 /\ ts1 = ts2) /\ mem loc1 ts1 promises.
  Proof.
    revert MEM. rewrite unset_o. condtac; ss. i.
    splits; auto. ii. des; auto.
  Qed.

  Lemma unset_set loc to inv
        (MEM: mem loc to inv = false):
    unset loc to (set loc to inv) = inv.
  Proof.
    apply ext. i.
    rewrite unset_o, set_o.  condtac; ss. des. subst. auto.
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
      (SOUND: forall l t (INV: mem l t inv),
          Memory.get l t promises_tgt = None /\
          exists f v r, Memory.get l t promises_src = Some (f, Message.mk v r))
      (COMPLETE: forall l t f v r
                   (SRC: Memory.get l t promises_src = Some (f, Message.mk v r))
                   (TGT: Memory.get l t promises_tgt = None),
          mem l t inv)
  .

  Lemma promise
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to val released promises2_tgt mem2_tgt kind)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released promises2_src mem2_src kind>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - exploit (@Memory.add_exists mem1_src loc from to val released);
        try by inv MEM; inv ADD.
      { eapply covered_disjoint.
        - apply SIM1.
        - inv MEM. inv ADD. auto.
      }
      i. des.
      exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_add; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + econs; eauto.
      + econs.
        * ii. erewrite Memory.add_o; eauto.
          erewrite (@Memory.add_o promises2_tgt) in LHS; try exact PROMISES. revert LHS.
          condtac; ss. apply INV1.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2); eauto.
          condtac; ss. des. subst.
          erewrite Memory.add_get0 in x3; eauto. congr.
        * i. revert SRC TGT.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2_tgt); eauto.
          condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.split_get0; try exact PROMISES; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 val val3 released);
        try by inv PROMISES; inv SPLIT.
      { apply INV1. eauto. }
      i. des.
      exploit Memory.split_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_split; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + econs; eauto.
      + econs.
        * ii. revert LHS.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); try exact x0.
          repeat condtac; ss. apply INV1.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); eauto.
          exploit Memory.split_get0; try exact x0; eauto. i. des.
          repeat condtac; ss.
          { des. subst. congr. }
          { guardH o. des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.lower_get0; try exact PROMISES; eauto. i.
      exploit (@Memory.lower_exists promises1_src loc from to val released0 released);
        try by inv MEM; inv LOWER.
      { apply INV1. eauto. }
      i. des.
      exploit Memory.lower_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_lower; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + econs; eauto.
      + econs.
        * ii. revert LHS.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); try exact x1.
          condtac; ss. apply INV1.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
          exploit Memory.lower_get0; try exact x1; eauto. i. des.
          condtac; ss.
          { des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
  Qed.

  Lemma remove_tgt
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to val released promises2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
      <<INV2: sem (set loc to inv) promises1_src promises2_tgt>> /\
      <<INV2': mem loc to inv = false>>.
  Proof.
    hexploit Memory.remove_future; eauto. i. des.
    exploit Memory.remove_get0; [eauto|]. i.
    inv INV1. exploit LE; eauto. i.
    esplits.
    - econs.
      + ii. revert LHS.
        erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      + i. erewrite Memory.remove_o; eauto.
        revert INV. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        * des. subst. esplits; eauto.
        * exploit SOUND; eauto.
      + i. revert TGT.
        erewrite Memory.remove_o; eauto. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        eapply COMPLETE; eauto.
    - destruct (mem loc to inv) eqn:X; auto.
      exploit SOUND; [eauto|]. i. des. congr.
  Qed.

  Lemma remove_src
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt
        (INV1: sem inv promises1_src promises1_tgt)
        (INV1': mem loc to inv)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (GET: Memory.get loc to promises1_src = Some (from, Message.mk val released))
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to val released promises2_src>> /\
      <<INV2: sem (unset loc to inv) promises2_src promises1_tgt>>.
  Proof.
    inv INV1.
    exploit Memory.remove_exists; eauto. i. des.
    esplits; eauto.
    econs.
    - ii. revert LHS.
      erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
      des. subst. exploit SOUND; eauto. i. des. congr.
    - i. rewrite unset_o in INV. revert INV. condtac; ss.
      guardH o.
      i. exploit SOUND; eauto. i. des. splits; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. unguardH o. des; congr.
    - i. revert SRC.
      erewrite Memory.remove_o; eauto. rewrite unset_o.
      unfold Time.t, DOSet.elt. condtac; ss; i.
      eapply COMPLETE; eauto.
  Qed.

  Lemma remove
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (REL_WF: View.opt_wf released)
        (TIME: Time.lt from to)
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to val released promises2_tgt)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to val released promises2_src>> /\
      <<INV2: sem inv promises2_src promises2_tgt>>.
  Proof.
    hexploit Memory.remove_future; try apply REMOVE_TGT; eauto. i. des.
    exploit remove_tgt; eauto. i. des.
    exploit Memory.remove_get0; eauto. i.
    inv INV1. exploit LE; eauto. i.
    exploit remove_src; try apply set_eq; eauto. i. des.
    esplits; eauto.
    rewrite unset_set in INV0; auto.
  Qed.

  Lemma future_imm
        inv
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future_imm mem1_src mem2_src)
        (INV1: sem inv promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv FUTURE_SRC.
    - exploit (@Memory.add_exists mem1_tgt loc from to val (Some (Memory.max_released mem1_tgt loc to))).
      { eapply covered_disjoint; try apply SIM1; eauto. inv ADD. inv ADD0. auto. }
      { inv ADD. inv ADD0. auto. }
      { econs. eapply Memory.max_released_wf; eauto. }
      i. des.
      exploit sim_memory_add; try exact SIM1; eauto.
      { erewrite Memory.max_released_spec; try exact ADD; eauto.
        econs. apply sim_memory_max_released; auto.
      }
      i.
      exploit Memory.max_released_closed; eauto. i. des.
      esplits.
      + econs 2; eauto. econs 1; eauto. econs. eauto.
      + ii. erewrite Memory.add_o; eauto. condtac; ss; eauto.
        des. subst. exploit LE1_TGT; eauto. erewrite Memory.add_get0; eauto. congr.
      + auto.
    - esplits; eauto.
      + refl.
      + etrans; eauto. eapply split_sim_memory. eauto.
    - esplits; eauto.
      + refl.
      + etrans; eauto. eapply lower_sim_memory. eauto.
  Qed.

  Lemma future
        inv
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (INV1: sem inv promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    revert INV1 SIM1 LE1_SRC LE1_TGT LE2_SRC CLOSED1_SRC CLOSED1_TGT.
    revert inv promises_src promises_tgt mem1_tgt.
    induction FUTURE_SRC; i.
    { esplits; eauto. refl. }
    assert (LE_SRC: Memory.le promises_src y).
    { ii. exploit LE1_SRC; eauto. i. destruct msg.
      exploit Memory.future_get; try exact x0; eauto.
      { econs 2; [|refl]. eauto. }
      i. des.
      exploit Memory.future_get; try exact GET; eauto. i. des.
      erewrite LE2_SRC in GET0; eauto. inv GET0.
      rewrite GET. f_equal. f_equal.
      - apply TimeFacts.antisym; eauto.
      - f_equal. apply View.opt_antisym; eauto.
    }
    exploit future_imm; eauto. i. des.
    exploit IHFUTURE_SRC; eauto.
    { eapply Memory.future_closed; try exact CLOSED1_SRC; eauto. econs 2; eauto. }
    { eapply Memory.future_closed; try exact CLOSED1_TGT; eauto. }
    i. des.
    esplits.
    - etrans; eauto.
    - auto.
    - auto.
  Qed.

  Lemma sem_bot promises:
    sem bot promises promises.
  Proof.
    econs.
    - refl.
    - i. inv INV.
    - i. congr.
  Qed.

  Lemma sem_bot_inv
        promises_src promises_tgt
        (SEM: sem bot promises_src promises_tgt):
    promises_src = promises_tgt.
  Proof.
    apply Memory.ext. i.
    destruct (Memory.get loc ts promises_tgt) as [[? []]|] eqn:X.
    - inv SEM. exploit LE; eauto.
    - destruct (Memory.get loc ts promises_src) as [[? []]|] eqn:Y; auto.
      inv SEM. exploit COMPLETE; eauto. i. inv x.
  Qed.
End SimPromises.
