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

Lemma memory_sim_add
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to val released
      (SIM: Memory.sim mem1_tgt mem1_src)
      (SRC: Memory.add mem1_src loc from to val released mem2_src)
      (TGT: Memory.add mem1_tgt loc from to val released mem2_tgt):
  Memory.sim mem2_tgt mem2_src.
Proof.
Admitted.

Lemma memory_sim_split
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to1 to2 val released
      (SIM: Memory.sim mem1_tgt mem1_src)
      (SRC: Memory.split mem1_src loc from to1 to2 val released mem2_src)
      (TGT: Memory.split mem1_tgt loc from to1 to2 val released mem2_tgt):
  Memory.sim mem2_tgt mem2_src.
Proof.
Admitted.

Lemma memory_sim_closed_timemap
      mem_src mem_tgt
      tm
      (SIM: Memory.sim mem_tgt mem_src)
      (TGT: Memory.closed_timemap tm mem_tgt):
  Memory.closed_timemap tm mem_src.
Proof.
  ii. exploit TGT; eauto. i. des.
  exploit Memory.sim_get; eauto. i. des. eauto.
Qed.

Lemma memory_sim_closed_capability
      mem_src mem_tgt
      capability
      (SIM: Memory.sim mem_tgt mem_src)
      (TGT: Memory.closed_capability capability mem_tgt):
  Memory.closed_capability capability mem_src.
Proof.
  econs.
  - eapply memory_sim_closed_timemap; eauto. apply TGT.
  - eapply memory_sim_closed_timemap; eauto. apply TGT.
  - eapply memory_sim_closed_timemap; eauto. apply TGT.
Qed.

Module MemInv.
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
    if Loc.eq_dec loc1 loc2
    then if Time.eq_dec ts1 ts2
         then true
         else mem loc1 ts1 promises
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, set, LocFun.add, LocFun.find.
    repeat condtac; subst; ss.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq. auto.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
  Qed.

  Lemma set_eq loc ts promises:
    mem loc ts (set loc ts promises) = true.
  Proof.
    rewrite set_o, Loc.eq_dec_eq, Time.eq_dec_eq. auto.
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
    if Loc.eq_dec loc1 loc2
    then if Time.eq_dec ts1 ts2
         then false
         else mem loc1 ts1 promises
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, unset, LocFun.add, LocFun.find. repeat condtac; subst; ss.
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
    rewrite unset_o. rewrite Loc.eq_dec_eq, Time.eq_dec_eq. auto.
  Qed.

  Lemma unset_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (unset loc2 ts2 promises)):
    ~ (loc1 = loc2 /\ ts1 = ts2) /\ mem loc1 ts1 promises.
  Proof.
    revert MEM. rewrite unset_o. repeat condtac; ss; splits; auto.
    - ii. des. subst. congr.
    - ii. des. subst. congr.
  Qed.

  Lemma unset_set loc to inv
        (MEM: mem loc to inv = false):
    unset loc to (set loc to inv) = inv.
  Proof.
    apply ext. i.
    rewrite unset_o, set_o. repeat condtac; ss. subst. auto.
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
      (JOIN: forall loc ts, Memory.mem loc ts promises_src = orb (mem loc ts inv) (Memory.mem loc ts promises_tgt))
      (DISJOINT: forall loc ts (INV:mem loc ts inv) (TGT:Memory.mem loc ts promises_tgt), False)
  .

  Lemma promise
        inv
        loc from to val released_src released_tgt
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (REL: Capability.le released_src released_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to val released_tgt promises2_tgt mem2_tgt kind)
        (INV1: sem inv promises1_src promises1_tgt)
        (LE1: Memory.le promises1_tgt promises1_src)
        (SIM1: Memory.sim mem1_tgt mem1_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SEC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released_src promises2_src mem2_src kind>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<LE2: forall l t f m
               (LT: (l, t) <> (loc, to))
               (MSG: Memory.get l t promises2_tgt = Some (f, m)),
          Memory.get l t promises2_src = Some (f, m)>> /\
      <<SIM2: Memory.sim mem2_tgt mem2_src>>.
  Proof.
    inv PROMISE_TGT.
    - admit.
    - admit.
    - admit.
  Admitted.

    (* - exploit Memory.add_exists; eauto. i. des. *)
    (*   exploit memory_sim_add; try apply INV1; eauto. i. *)
    (*   exploit Memory.promise_add_exists; try apply LE1_SRC; eauto. *)
    (*   { eapply memory_sim_closed_capability; eauto. } *)
    (*   i. des. *)
    (*   exploit Memory.promise_future; try apply x2; eauto. i. des. *)
    (*   esplits; eauto. *)
    (*   inv x2. inv INV1. ss. econs. *)
    (*   + ii. exploit Memory.add_get_inv; try apply PROMISES; eauto. i. des. *)
    (*     * subst. eapply Memory.add_get2; eauto. *)
    (*     * exploit LE; eauto. i. *)
    (*       eapply Memory.add_get1; eauto. *)
    (*   + i. exploit GET; eauto. i. des. splits. *)
    (*     * destruct (Memory.get loc0 ts promises1_src) as [[]|] eqn:X; [|congr]. *)
    (*       erewrite Memory.add_get1; eauto. *)
    (*     * destruct (Memory.get loc0 ts promises2_tgt) as [[]|] eqn:X; [|done]. *)
    (*       exploit Memory.add_get_inv; try apply X; eauto. i. des; [|congr]. *)
    (*       subst. exploit Memory.add_disjoint; try apply PROMISES0; eauto. congr. *)
    (*   + i. *)
    (*     destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X; [|congr]. *)
    (*     exploit Memory.add_get_inv; try apply X; eauto. i. des. *)
    (*     * subst. exploit Memory.add_get2; try apply PROMISES; eauto. congr. *)
    (*     * apply MEM1; [congr|]. *)
    (*       destruct (Memory.get loc0 ts promises1_tgt) as [[]|] eqn:Y; [|done]. *)
    (*       exploit Memory.add_get1; try apply Y; eauto. congr. *)
    (* - exploit Memory.split_exists; eauto. i. des. *)
    (*   exploit Memory.split_exists_le; try apply LE1_SRC; eauto. i. des. *)
    (*   exploit memory_sim_split; try apply INV1; eauto. i. *)
    (*   exploit memory_sim_closed_capability; eauto. i. *)
    (*   exploit Memory.promise_split; [apply x0|apply x1| | |]; eauto. i. *)
    (*   exploit Memory.promise_future; try apply x4; eauto. i. des. *)
    (*   esplits; eauto. *)
    (*   inv INV1. ss. econs. *)
    (*   + ii. exploit Memory.split_get_inv; try apply PROMISES; eauto. i. des. *)
    (*     * subst. eapply Memory.split_get2; eauto. *)
    (*     * subst. exploit Memory.split_get1; try apply x0; eauto. i. des; [done|]. *)
    (*       contradict x5. auto. *)
    (*     * exploit LE; eauto. i. *)
    (*       exploit Memory.split_get1; try apply x0; eauto. i. des; [|done]. *)
    (*       contradict x6. auto. *)
    (*   + i. exploit GET; eauto. i. des. splits. *)
    (*     * destruct (Memory.get loc0 ts promises1_src) as [[]|] eqn:X; [|congr]. *)
    (*       exploit Memory.split_get1; try apply x0; eauto. i. des; congr. *)
    (*     * destruct (Memory.get loc0 ts promises2_tgt) as [[]|] eqn:X; [|done]. *)
    (*       exploit Memory.split_get_inv; try apply X; eauto. i. des; subst; [|congr|congr]. *)
    (*       exploit Memory.split_disjoint; try apply x0; eauto. congr. *)
    (*   + i. *)
    (*     destruct (Memory.get loc0 ts mem2) as [[]|] eqn:X; [|congr]. *)
    (*     exploit Memory.split_get_inv; try apply X; eauto. i. des. *)
    (*     * subst. exploit Memory.split_get2; try apply PROMISES; eauto. congr. *)
    (*     * subst. exploit Memory.split_get0; try apply PROMISES; eauto. i. des. *)
    (*       exploit Memory.split_get1; try apply PROMISES; eauto. i. des; congr. *)
    (*     * apply MEM0; [congr|]. *)
    (*       destruct (Memory.get loc0 ts promises1_tgt) as [[]|] eqn:Y; [|done]. *)
    (*       exploit Memory.split_get1; try apply Y; eauto. i. des; congr. *)

  Lemma write_promise
        inv
        loc from to val released_src released_tgt
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (REL: Capability.le released_src released_tgt)
        (WRITE_TGT: Memory.write promises1_tgt mem1_tgt loc from to val released_tgt promises2_tgt mem2_tgt kind)
        (INV1: sem inv promises1_src promises1_tgt)
        (LE1: Memory.le promises1_tgt promises1_src)
        (SIM1: Memory.sim mem1_tgt mem1_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SEC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released_src promises2_src mem2_src kind>> /\
      <<INV2: sem (set loc to inv) promises2_src promises2_tgt>> /\
      <<LE2: Memory.le promises2_tgt promises2_src>> /\
      <<SIM2: Memory.sim mem2_tgt mem2_src>>.
  Proof.
    inv WRITE_TGT. exploit promise; eauto. i. des.
    esplits; eauto.
    - admit.
    - ii. apply LE2; eauto.
      + ii. inv H. exploit Memory.remove_get2; eauto. i. congr.
      + eapply Memory.remove_get_inv; eauto.
  Admitted.

  Lemma write
        inv
        loc from to val released_src released_tgt
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (REL: Capability.le released_src released_tgt)
        (WRITE_TGT: Memory.write promises1_tgt mem1_tgt loc from to val released_tgt promises2_tgt mem2_tgt kind)
        (INV1: sem inv promises1_src promises1_tgt)
        (LE1: Memory.le promises1_tgt promises1_src)
        (SIM1: Memory.sim mem1_tgt mem1_src)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SEC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists promises2_src mem2_src,
      <<WRITE_SRC: Memory.write promises1_src mem1_src loc from to val released_src promises2_src mem2_src kind>> /\
      <<INV2: sem inv promises2_src promises2_tgt>> /\
      <<LE2: Memory.le promises2_tgt promises2_src>> /\
      <<SIM2: Memory.sim mem2_tgt mem2_src>>.
  Proof.
    exploit write_promise; eauto. i. des.
    exploit Memory.promise_get2; eauto. i.
    exploit Memory.remove_exists; eauto. i. des.
    esplits.
    - econs; eauto.
    - inv INV2. econs.
      + i. erewrite Memory.remove_mem; [|eauto].
        rewrite JOIN. rewrite set_o.
        repeat condtac; subst; s; try by apply Bool.andb_true_r.
        admit.
      + i. eapply DISJOINT; eauto.
        rewrite set_o. repeat condtac; auto.
    - ii. exploit LE2; eauto. i.
      exploit Memory.remove_get1; eauto. i. des; auto.
      subst. inv INV2. exfalso. eapply DISJOINT.
      + apply set_eq.
      + unfold Memory.mem. rewrite LHS. auto.
    - auto.
  Admitted.

  Lemma future
        inv
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (INV1: sem inv promises_src promises_tgt)
        (LE1: Memory.le promises_tgt promises_src)
        (SIM1: Memory.sim mem1_tgt mem1_src)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src):
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_src>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_src>>.
  Proof.
    splits.
    - etrans; eauto. apply Memory.sim_future. apply SIM1.
    - etrans; try apply LE1; eauto.
  Qed.

  Lemma sem_bot promises:
    sem bot promises promises.
  Proof.
    econs.
    - refl.
    - i. inv INV.
  Qed.

  Lemma sem_bot_inv
        promises_src promises_tgt
        (SEM: sem bot promises_src promises_tgt)
        (LE: Memory.le promises_tgt promises_src):
    promises_src = promises_tgt.
  Proof.
    apply Memory.ext. i.
    destruct (Memory.get loc ts promises_tgt) as [[]|] eqn:X.
    - exploit LE; eauto.
    - destruct (Memory.get loc ts promises_src) as [[]|] eqn:Y; auto.
      inv SEM. exploit JOIN; eauto. unfold Memory.mem.
      rewrite X, Y. ss.
  Qed.
End MemInv.
