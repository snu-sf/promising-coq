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

Set Implicit Arguments.


Inductive covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
    (MSG: forall loc from_tgt to val released_tgt
            (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.mk val released_tgt)),
        exists from_src released_src,
          <<GET: Memory.get loc to mem_src = Some (from_src, Message.mk val released_src)>> /\
          <<RELEASED: View.opt_le released_src released_tgt>>)
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation.
  econs; try refl. i. esplits; eauto. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto. i.
  exploit MSG0; eauto. i. des.
  exploit MSG; eauto. i. des.
  esplits; eauto. etrans; eauto.
Qed.


Lemma sim_memory_get
      loc from_tgt to val released_tgt mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.mk val released_tgt)):
  exists from_src released_src,
    <<GET: Memory.get loc to mem_src = Some (from_src, Message.mk val released_src)>> /\
    <<RELEASED: View.opt_le released_src released_tgt>>.
Proof.
  eapply SIM. eauto.
Qed.

Lemma sim_memory_max_timemap
      mem_src mem_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt):
  TimeMap.le (Memory.max_timemap mem_src) (Memory.max_timemap mem_tgt).
Proof.
  apply Memory.max_timemap_spec'; try by apply CLOSED_TGT; auto. i.
  destruct (Time.le_lt_dec (Memory.max_timemap mem_src loc) Time.bot).
  { esplits; eauto. apply CLOSED_TGT. }
  exploit Memory.max_timemap_closed; try apply CLOSED_SRC; eauto.
  instantiate (1 := loc). i. des.
  inv SIM. destruct (COVER loc (Memory.max_timemap mem_src loc)) as [C1 C2].
  exploit C1; eauto.
  { econs; eauto. apply Interval.mem_ub.
    destruct (mem_src loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
    inv x. rewrite H1 in *. inv l.
  }
  i. inv x. inv ITV. destruct msg. ss.
  esplits; eauto.
Qed.

Lemma sim_memory_max_view
      mem_src mem_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt):
  View.le (Memory.max_view mem_src) (Memory.max_view mem_tgt).
Proof.
  econs; apply sim_memory_max_timemap; auto.
Qed.

Lemma sim_memory_max_released
      mem_src mem_tgt loc ts
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt):
  View.le (Memory.max_released mem_src loc ts) (Memory.max_released mem_tgt loc ts).
Proof.
  unfold Memory.max_released. econs; s.
  - ii. unfold TimeMap.add. condtac; [refl|].
    unfold TimeMap.get. aggrtac.
    etrans; [|apply Time.join_l]. eapply sim_memory_max_timemap; eauto.
  - ii. unfold TimeMap.add. condtac; [refl|].
    unfold TimeMap.get. aggrtac.
    etrans; [|apply Time.join_l]. eapply sim_memory_max_timemap; eauto.
  - unfold TimeMap.get. aggrtac.
    etrans; [|apply TimeMap.join_l]. eapply sim_memory_max_timemap; eauto.
Qed.

Lemma covered_disjoint
      mem1 mem2 loc from to
      (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2)
      (DISJOINT: forall to2 from2 msg2
                   (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)):
  forall to2 from2 msg2
    (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
    Interval.disjoint (from, to) (from2, to2).
Proof.
  ii. exploit COVER; eauto.
  { econs; eauto. }
  i. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma get_disjoint_covered_disjoint
      mem loc from to:
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)) ->
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts).
Proof.
  ii. inv H0. eapply H; eauto.
Qed.

Lemma covered_disjoint_get_disjoint
      mem loc from to:
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts) ->
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)).
Proof.
  ii. eapply H; eauto. econs; eauto.
Qed.

Lemma add_covered
      mem2 mem1 loc from to val released
      l t
      (ADD: Memory.add mem1 loc from to val released mem2):
  covered l t mem2 <->
  covered l t mem1 \/ (l = loc /\ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. erewrite Memory.add_get0 in GET; eauto. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma split_covered
      mem2 mem1 loc ts1 ts2 ts3 val2 val3 released2 released3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - exploit Memory.split_get0; eauto. i. des.
    inv H. revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [refl|].
      inv SPLIT. inv SPLIT0. left. auto.
    + guardH o. des. subst. i. inv GET. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [|refl].
      inv SPLIT. inv SPLIT0. left. auto.
    + i. econs; eauto.
  - exploit Memory.split_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss.
    + des. subst. rewrite GET3 in GET. inv GET.
      destruct (Time.le_lt_dec t ts2).
      * econs.
        { instantiate (2 := from). instantiate (2 := ts2).
          erewrite Memory.split_o; eauto. condtac; ss.
          des; congr.
        }
        { inv ITV. econs; ss. }
      * econs.
        { instantiate (2 := ts2). instantiate (2 := ts3).
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          - des. subst. inv SPLIT. inv SPLIT0.
            exfalso. eapply Time.lt_strorder. eauto.
          - guardH o. des; congr.
        }
        { inv ITV. econs; ss. }
    + econs; eauto. erewrite Memory.split_o; eauto.
      repeat condtac; ss; eauto.
      * guardH o. des. subst. congr.
      * guardH o. guardH o0. des. subst.
        unguardH o. des; congr.
Qed.

Lemma lower_covered
      mem2 mem1 loc from to val released1 released2
      l t
      (LOWER: Memory.lower mem1 loc from to val released1 released2 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. econs; eauto.
      eapply Memory.lower_get0; eauto.
    + i. econs; eauto.
  - exploit Memory.lower_get0; eauto. i.
    inv H.
    destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss.
    + des. subst. econs; eauto.
      erewrite Memory.lower_o; eauto. condtac.
      * rewrite GET in x0. inv x0. eauto.
      * ss. des; congr.
    + econs; eauto.
      erewrite Memory.lower_o; eauto. rewrite GET. condtac; ss.
      des; congr.
Qed.

Lemma sim_memory_add
      mem1_src mem1_tgt released_src
      mem2_src mem2_tgt released_tgt
      loc from to val
      (REL_LE: View.opt_le released_src released_tgt)
      (SRC: Memory.add mem1_src loc from to val released_src mem2_src)
      (TGT: Memory.add mem1_tgt loc from to val released_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs.
  - i. rewrite add_covered; [|eauto]. rewrite (@add_covered mem2_tgt); [|eauto].
    econs; i; des; (try by right).
    + left. eapply COVER. eauto.
    + left. eapply COVER. eauto.
  - i. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
    + erewrite (@Memory.add_o mem2_src); eauto. condtac; ss. eauto.
Qed.

Lemma sim_memory_split
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc ts1 ts2 ts3 val2 val3 released2_src released3_src released2_tgt released3_tgt
      (REL_LE: View.opt_le released2_src released2_tgt)
      (SRC: Memory.split mem1_src loc ts1 ts2 ts3 val2 val3 released2_src released3_src mem2_src)
      (TGT: Memory.split mem1_tgt loc ts1 ts2 ts3 val2 val3 released2_tgt released3_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs.
  - i. rewrite split_covered; [|eauto]. rewrite (@split_covered mem2_tgt); [|eauto].
    apply COVER.
  - i. revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.split_o; eauto. condtac; ss.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss.
      i. inv GET. guardH o. guardH o0. des. subst.
      exploit Memory.split_get0; try exact SRC; eauto. i. des.
      exploit Memory.split_get0; try exact TGT; eauto. i. des.
      exploit MSG; eauto. i. des. rewrite GET3 in GET. inv GET.
      esplits; eauto.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss. eauto.
Qed.

Lemma sim_memory_lower
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to val released1_src released1_tgt released2_src released2_tgt
      (REL_LE: View.opt_le released2_src released2_tgt)
      (SRC: Memory.lower mem1_src loc from to val released1_src released2_src mem2_src)
      (TGT: Memory.lower mem1_tgt loc from to val released1_tgt released2_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs.
  - i. rewrite lower_covered; [|eauto]. rewrite (@lower_covered mem2_tgt); [|eauto].
    apply COVER.
  - i. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.lower_o; eauto. condtac; ss.
    + erewrite (@Memory.lower_o mem2_src); eauto. condtac; ss. eauto.
Qed.

Lemma sim_memory_promise
      loc from to val kind
      promises1_src mem1_src released_src promises2_src mem2_src
      promises1_tgt mem1_tgt released_tgt promises2_tgt mem2_tgt
      (REL_LE: View.opt_le released_src released_tgt)
      (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to val released_src promises2_src mem2_src kind)
      (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to val released_tgt promises2_tgt mem2_tgt kind)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv PROMISE_SRC; inv PROMISE_TGT.
  - eapply sim_memory_add; eauto.
  - eapply sim_memory_split; eauto.
  - eapply sim_memory_lower; eauto.
Qed.

Lemma sim_memory_closed_timemap
      mem_src mem_tgt
      tm
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_timemap tm mem_tgt):
  Memory.closed_timemap tm mem_src.
Proof.
  ii. exploit TGT; eauto. i. des.
  exploit sim_memory_get; eauto. i. des. eauto.
Qed.

Lemma sim_memory_closed_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_view view mem_tgt):
  Memory.closed_view view mem_src.
Proof.
  econs.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
Qed.

Lemma sim_memory_closed_opt_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_opt_view view mem_tgt):
  Memory.closed_opt_view view mem_src.
Proof.
  inv TGT; econs. eapply sim_memory_closed_view; eauto.
Qed.

Lemma lower_sim_memory
      mem1 loc from to val released1 released2 mem2
      (LOWER: Memory.lower mem1 loc from to val released1 released2 mem2):
  sim_memory mem2 mem1.
Proof.
  econs.
  - i. eapply lower_covered. eauto.
  - i. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst.
      erewrite Memory.lower_get0 in GET; eauto. inv GET.
      esplits; eauto. inv LOWER. inv LOWER0. auto.
    + esplits; eauto. refl.
Qed.

Lemma promise_lower_sim_memory
      promises1 mem1 loc from to val released1 released2 promises2 mem2
      (PROMISE: Memory.promise promises1 mem1 loc from to val released2 promises2 mem2 (Memory.op_kind_lower released1)):
  sim_memory mem2 mem1.
Proof.
  inv PROMISE. eapply lower_sim_memory. eauto.
Qed.

Lemma split_sim_memory
      mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1
      (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1):
  sim_memory mem1 mem0.
Proof.
  econs.
  - i. eapply split_covered. eauto.
  - i. exploit Memory.split_get0; eauto. i. des.
    erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. congr.
    + guardH o. des. subst. rewrite GET3 in GET. inv GET.
      esplits; eauto. refl.
    + esplits; eauto. refl.
Qed.
