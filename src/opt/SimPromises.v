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
Require Import Commit.
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
    - exploit (@Memory.add_exists mem1_src loc from to val released).
      { admit. (* m1 sim m2 means m1 and m2 takes the same intervals *) }
      { inv MEM. inv ADD. auto. }
      { inv MEM. inv ADD. auto. }
      i. des.
      exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_add; try apply SIM1; eauto. i.
      esplits; eauto.
      + econs; eauto.
      + econs.
        * ii. eapply Memory.add_get_inv in LHS; eauto. i. des.
          { subst. eapply Memory.add_get2. eauto. }
          { apply INV1 in LHS0. eapply Memory.add_get1; eauto. }
        * inv INV1. i. exploit SOUND; eauto. i. des. splits.
          { destruct (Memory.get l t0 promises2_tgt) as [[]|] eqn:X; auto.
            exploit Memory.add_get_inv; try exact X; eauto. i. des; [|congr].
            subst. exploit Memory.add_get0; try exact x1; eauto. i. congr.
          }
          { exploit Memory.add_get1; eauto. }
        * inv INV1. i. exploit Memory.add_get_inv; try exact SRC; eauto. i. des.
          { inv x6. exploit Memory.add_get2; try exact PROMISES; eauto. i. congr. }
          { eapply COMPLETE; eauto.
            destruct (Memory.get l t0 promises1_tgt) as [[? []]|] eqn:X; auto.
            exploit Memory.add_get1; try exact X; eauto. i. congr.
          }
    - exploit Memory.update_get0; try apply PROMISES; eauto. i. des.
      exploit (@Memory.update_exists promises1_src loc from1 from to val released1 released).
      { apply INV1. eauto. }
      { inv PROMISES. inv UPDATE. auto. }
      { inv PROMISES. inv UPDATE. auto. }
      { inv PROMISES. inv UPDATE. auto. }
      { inv PROMISES. inv UPDATE. auto. }
      i. des.
      exploit Memory.update_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_update; try apply SIM1; eauto. i.
      esplits; eauto.
      + econs; eauto.
      + econs.
        * ii. destruct msg.
          eapply Memory.update_get_inv in LHS; eauto. i. des.
          { subst. eapply Memory.update_get2. eauto. }
          { inv INV1. exploit LE; eauto. i.
            exploit Memory.update_get1; try exact x1; eauto. i. des; auto.
            inv x7. contradict LHS. auto.
          }
        * inv INV1. i. exploit SOUND; eauto. i. des. splits.
          { destruct (Memory.get l t0 promises2_tgt) as [[? []]|] eqn:X; auto.
            exploit Memory.update_get_inv; try exact X; eauto. i. des; [|congr].
            subst. exploit Memory.update_get0; try exact PROMISES; eauto. i. congr.
          }
          { exploit Memory.update_get1; try exact x4; eauto. i. des; eauto. }
        * inv INV1. i. exploit Memory.update_get_inv; try exact SRC; eauto. i. des.
          { subst. exploit Memory.update_get2; try exact PROMISES; eauto. i. congr. }
          { eapply COMPLETE; eauto.
            destruct (Memory.get l t0 promises1_tgt) as [[? []]|] eqn:X; auto.
            exploit Memory.update_get1; try exact X; eauto. i. des; congr.
          }
  Admitted.

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
      + ii. exploit Memory.remove_get_inv; eauto. i. des.
        apply LE. auto.
      + i. erewrite MemoryFacts.remove_o; eauto.
        revert INV. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        * des. subst. esplits; eauto.
        * exploit SOUND; eauto.
      + i. revert TGT.
        erewrite MemoryFacts.remove_o; eauto. rewrite set_o.
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
    - ii. exploit LE; eauto. i.
      exploit Memory.remove_get1; eauto. i. des; auto.
      subst. exploit SOUND; eauto. i. des. congr.
    - i. rewrite unset_o in INV. revert INV. condtac; ss.
      guardH o.
      i. exploit SOUND; eauto. i. des. splits; eauto.
      exploit Memory.remove_get1; eauto. i. des; eauto.
      inv x5. unguardH o. des; congr.
    - i. exploit Memory.remove_get_inv; eauto. i. des.
      rewrite unset_o. condtac; ss.
      eapply COMPLETE; eauto.
  Qed.

  Lemma remove
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (REL_WF: Capability.wf released)
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

  Lemma write_promise
        inv
        loc from to val released
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (WRITE_TGT: Memory.write promises1_tgt mem1_tgt loc from to val released promises2_tgt mem2_tgt kind)
        (REL: Capability.wf released)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SEC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released promises2_src mem2_src kind>> /\
      <<INV2: sem (set loc to inv) promises2_src promises2_tgt>> /\
      <<INV2': mem loc to inv = false>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv WRITE_TGT.
    exploit Memory.promise_future0; try apply PROMISE; eauto; try committac. i. des.
    exploit promise; eauto. i. des.
    exploit Memory.promise_future0; try apply PROMISE_SRC; eauto; try committac. i. des.
    exploit remove_tgt; eauto; try refl. i. des.
    esplits; eauto.
  Qed.

  Lemma write
        inv
        loc from to val released_src released_tgt
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (REL_LE: Capability.le released_src released_tgt)
        (REL_WF_SRC: Capability.wf released_src)
        (REL_WF_TGT: Capability.wf released_tgt)
        (WRITE_TGT: Memory.write promises1_tgt mem1_tgt loc from to val released_tgt promises2_tgt mem2_tgt kind)
        (INV1: sem inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SEC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<WRITE_SRC: Memory.write promises1_src mem1_src loc from to val released_src promises2_src mem2_src kind>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv WRITE_TGT.
    exploit Memory.promise_future0; try apply PROMISE; eauto; try committac. i. des.
    exploit promise; eauto. i. des.
    exploit Memory.promise_future0; try apply PROMISE_SRC; eauto; try committac. i. des.
    exploit remove; eauto; try eapply MemoryFacts.promise_time_lt; eauto. i. des.
    exploit MemorySplit.remove_promise_remove; try exact REMOVE_SRC; eauto; try refl.
    { by inv PROMISE. }
    { eapply MemoryFacts.promise_time_lt. eauto. }
    i. des.
    esplits.
    - econs; eauto.
      eapply MemoryMerge.promise_promise_promise; eauto.
    - auto.
    - etrans; eauto. eapply sim_memory_promise_lower. eauto.
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
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<CLOSED2_TGT: Memory.closed mem2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    revert INV1 SIM1 LE1_SRC LE1_TGT LE2_SRC CLOSED1_TGT.
    revert inv promises_src promises_tgt mem1_tgt.
    induction FUTURE_SRC; i.
    { esplits; eauto. refl. }
    inv H.
    - admit.
    - admit.
  Admitted.

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
