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
Require Import Memory.
Require Import MemoryFacts.

Set Implicit Arguments.


Module MemorySplit.
  Lemma remove_update_remove
        mem0 loc from1 from2 to val released1 released2 mem2
        (REL_LE: Capability.le released2 released1)
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REMOVE: Memory.remove mem0 loc from1 to val released1 mem2):
    exists mem1',
      <<UPDATE: Memory.update mem0 loc from1 from2 to val released1 released2 mem1'>> /\
      <<REMOVE: Memory.remove mem1' loc from2 to val released2 mem2>>.
  Proof.
    exploit Memory.remove_get0; eauto. i.
    inv REMOVE. inv REMOVE0.
    erewrite <- LocFun.add_add_eq.
    destruct r. ss. subst.
    esplits.
    - econs. instantiate (1 := Cell.mk _). econs; eauto.
    - econs; eauto. unfold LocFun.add. condtac; [|congr].
      unfold Cell.remove. s.
      replace (DOMap.remove to (Cell.raw (mem0 loc))) with
      (DOMap.remove to
                    (DOMap.add to
                               (from2,
                                {|
                                  Message.val := val;
                                  Message.released := released2 |})
                               (Cell.raw (mem0 loc)))).
      + econs. rewrite DOMap.gss. auto.
      + apply DOMap.eq_leibniz. ii.
        rewrite ? DOMap.grspec, DOMap.gsspec. condtac; auto.
        Grab Existential Variables.
        { eapply Cell.Raw.update_wf; eauto.
          - econs; eauto.
          - apply mem0.
        }
  Qed.

  Lemma remove_promise_remove
        promises0 mem0 loc from1 from2 to val released1 released2 promises2
        (PROMISES: Memory.le promises0 mem0)
        (REL_LE: Capability.le released2 released1)
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (REL_TO: Time.le (Capability.rw released1 loc) to)
        (FROM1: Time.le from1 from2)
        (FROM2: Time.lt from2 to)
        (REMOVE: Memory.remove promises0 loc from1 to val released1 promises2):
    exists promises1' mem1',
      <<PROMISE: Memory.promise promises0 mem0 loc from2 to val released2 promises1' mem1' (Memory.promise_kind_update from1 released1)>> /\
      <<REMOVE: Memory.remove promises1' loc from2 to val released2 promises2>>.
  Proof.
    exploit remove_update_remove; eauto. i. des.
    exploit Memory.update_exists_le; eauto. i. des.
    esplits; eauto.
    - econs; eauto. etrans; eauto. apply REL_LE.
  Qed.

  Lemma commute_remove_update_add_remove_remove
        mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 released3' mem1 mem2 mem4
        (REMOVE1: Memory.remove mem0 loc ts1 ts3 val3 released3 mem4)
        (UPDATE1: Memory.update mem0 loc ts1 ts2 ts3 val3 released3 released3' mem1)
        (ADD2: Memory.add mem1 loc ts1 ts2 val2 released2 mem2):
    exists mem3',
      <<REMOVE3: Memory.remove mem2 loc ts1 ts2 val2 released2 mem3'>> /\
      <<REMOVE4: Memory.remove mem3' loc ts2 ts3 val3 released3' mem4>>.
  Proof.
    exploit Memory.add_get2; eauto. i.
    exploit Memory.remove_exists; eauto. i. des.
    exploit Memory.update_get2; eauto. i.
    exploit Memory.add_get1; eauto. i.
    exploit Memory.remove_get1; eauto. i. des.
    { inv x7. inv ADD2. inv ADD. exfalso. eapply Time.lt_strorder. eauto. }
    i. des.
    exploit Memory.remove_exists; eauto. i. des.
    esplits; eauto.
    cut (mem5 = mem4); [by i; subst|].
    apply Memory.ext. i.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.remove_o; eauto.
    erewrite MemoryFacts.add_o; eauto.
    erewrite MemoryFacts.update_o; eauto.
    erewrite (@MemoryFacts.remove_o mem4); eauto.
    repeat (condtac; ss). des; try congr. subst.
    exploit Memory.update_get0; try eexact UPDATE1; eauto. i.
    destruct (Memory.get loc ts2 mem0) as [[]|] eqn:X; auto.
    destruct (mem0 loc).(Cell.WF).
    exfalso. eapply DISJOINT; try exact o; eauto.
    - apply Interval.mem_ub.
      exploit VOLUME; eauto. i. des; auto.
      inv x. inv ADD2. inv ADD. inv TO.
    - inv UPDATE1. inv UPDATE. inv ADD2. inv ADD.
      econs; eauto. left. auto.
  Qed.

  Lemma update_add_exists
        mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 released3'
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (GET: Memory.get loc ts3 mem0 = Some (ts1, Message.mk val3 released3))
        (WF2: Capability.wf released2)
        (WF3: Capability.wf released3')
        (LE3: Capability.le released3' released3):
    exists mem1' mem2',
      <<STEP1: Memory.update mem0 loc ts1 ts2 ts3 val3 released3 released3' mem1'>> /\
      <<STEP2: Memory.add mem1' loc ts1 ts2 val2 released2 mem2'>>.
  Proof.
    exploit Memory.update_exists; eauto.
    { left. auto. }
    i. des.
    exploit (Memory.add_exists mem2 loc); try exact TS12; try exact WF2; eauto.
    { i. destruct msg2.
      exploit Memory.update_get_inv; eauto. i. des.
      - subst. ii. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      - assert (to2 <> ts3).
        { contradict x1. auto. }
        destruct (mem0 loc).(Cell.WF).
        ii. eapply DISJOINT; try exact H; eauto.
        eapply Interval.le_mem; try exact LHS; eauto. econs; s.
        + refl.
        + left. auto.
    }
    i. des.
    esplits; eauto.
  Qed.

  Lemma remove_promise_promise_remove_remove
        loc ts1 ts2 ts3 val2 released2 val3 released3 released3'
        promises0 mem0
        promises4
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (WF2: Capability.wf released2)
        (WF3: Capability.wf released3')
        (LE3: Capability.le released3' released3)
        (TS2: Time.le (Capability.rw released2 loc) ts2)
        (TS3: Time.le (Capability.rw released3' loc) ts3)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc ts1 ts3 val3 released3 promises4):
    exists promises1 promises2 promises3 mem1 mem2,
      <<STEP1: Memory.promise promises0 mem0 loc ts2 ts3 val3 released3' promises1 mem1 (Memory.promise_kind_update ts1 released3)>> /\
      <<STEP2: Memory.promise promises1 mem1 loc ts1 ts2 val2 released2 promises2 mem2 Memory.promise_kind_add>> /\
      <<STEP3: Memory.remove promises2 loc ts1 ts2 val2 released2 promises3>> /\
      <<STEP4: Memory.remove promises3 loc ts2 ts3 val3 released3' promises4>>.
  Proof.
    exploit Memory.remove_get0; eauto. i.
    exploit update_add_exists; try exact TS12; try exact LE3; try exact x0; try exact WF2; eauto. i. des.
    exploit LE; eauto. i.
    exploit update_add_exists; try exact TS12; try exact LE3; try exact x; try exact WF2; eauto. i. des.
    exploit commute_remove_update_add_remove_remove; try exact REMOVE; eauto. i. des.
    esplits; eauto.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma promise_remove_promise_remove_promise_remove
        loc ts1 ts2 ts3 val2 val1 released1 released2
        promises0 mem0
        mem4 promises4
        promises5
        (LE: Memory.le promises0 mem0)
        (PROMISE: Memory.promise promises0 mem0 loc ts1 ts3 val2 released2 promises4 mem4 Memory.promise_kind_add)
        (REMOVE: Memory.remove promises4 loc ts1 ts3 val2 released2 promises5):
    exists promises1 promises2 promises3 mem1 mem3,
      <<STEP1: Memory.promise promises0 mem0 loc ts1 ts2 val1 released1 promises1 mem1 Memory.promise_kind_add>> /\
      <<STEP2: Memory.remove promises1 loc ts1 ts2 val1 released1 promises2>> /\
      <<STEP3: Memory.promise promises2 mem1 loc ts2 ts3 val2 released2 promises3 mem3 Memory.promise_kind_add>> /\
      <<STEP4: Memory.remove promises3 loc ts2 ts3 val2 released2 promises4>>.
  Proof.
  Admitted.
End MemorySplit.
