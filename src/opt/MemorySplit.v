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
  Lemma remove_lower_remove
        mem0 loc from to val released1 released2 mem2
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (TS: Time.lt from to)
        (REMOVE: Memory.remove mem0 loc from to val released1 mem2):
    exists mem1',
      <<LOWER: Memory.lower mem0 loc from to val released1 released2 mem1'>> /\
      <<REMOVE: Memory.remove mem1' loc from to val released2 mem2>>.
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
                               (from,
                                {|
                                  Message.val := val;
                                  Message.released := released2 |})
                               (Cell.raw (mem0 loc)))).
      + econs. rewrite DOMap.gss. auto.
      + apply DOMap.eq_leibniz. ii.
        rewrite ? DOMap.grspec, DOMap.gsspec. condtac; auto.
        Grab Existential Variables.
        { eapply Cell.Raw.lower_wf; eauto.
          - econs; eauto.
          - apply mem0.
        }
  Qed.

  Lemma remove_promise_remove
        promises0 mem0 loc from to val released1 released2 promises2
        (PROMISES: Memory.le promises0 mem0)
        (REL_LE: Capability.le released2 released1)
        (REL_WF1: Capability.wf released1)
        (REL_WF2: Capability.wf released2)
        (REL_TO: Time.le (Capability.rw released1 loc) to)
        (TS: Time.lt from to)
        (REMOVE: Memory.remove promises0 loc from to val released1 promises2):
    exists promises1' mem1',
      <<PROMISE: Memory.promise promises0 mem0 loc from to val released2 promises1' mem1' (Memory.promise_kind_lower released1)>> /\
      <<REMOVE: Memory.remove promises1' loc from to val released2 promises2>>.
  Proof.
    exploit remove_lower_remove; try exact REMOVE; eauto. i. des.
    exploit Memory.lower_exists_le; eauto. i. des.
    esplits; eauto.
    - econs; eauto. etrans; eauto. apply REL_LE.
  Qed.

  Lemma commute_remove_split_remove_remove
        mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1 mem3
        (REMOVE1: Memory.remove mem0 loc ts1 ts3 val3 released3 mem3)
        (SPLIT1: Memory.split mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1):
    exists mem2',
      <<REMOVE3: Memory.remove mem1 loc ts1 ts2 val2 released2 mem2'>> /\
      <<REMOVE4: Memory.remove mem2' loc ts2 ts3 val3 released3 mem3>>.
  Proof.
    exploit (@Memory.remove_exists mem1 loc ts1 ts2 val2 released2); eauto.
    { erewrite Memory.split_o; eauto. repeat condtac; ss.
      - guardH o. des. subst. inv SPLIT1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      - guardH o0. des; congr.
    }
    i. des.
    exploit (@Memory.remove_exists mem2 loc ts2 ts3 val3 released3); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      - des. subst. inv SPLIT1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss.
        clear -o1. des; congr.
    }
    i. des. esplits; eauto.
    cut (mem4 = mem3); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite Memory.split_o; eauto. erewrite (@Memory.remove_o mem3); eauto.
    repeat (condtac; ss). guardH o. des. subst.
    exploit Memory.split_get0; eauto. i. des. auto.
  Qed.

  Lemma remove_promise_promise_remove_remove
        loc ts1 ts2 ts3 val2 released2 val3 released3
        promises0 mem0
        promises3
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (WF2: Capability.wf released2)
        (TS2: Time.le (Capability.rw released2 loc) ts2)
        (LE: Memory.le promises0 mem0)
        (REMOVE: Memory.remove promises0 loc ts1 ts3 val3 released3 promises3):
    exists promises1 promises2 mem1,
      <<STEP1: Memory.promise promises0 mem0 loc ts1 ts2 val2 released2 promises1 mem1 (Memory.promise_kind_split ts3 val3 released3)>> /\
      <<STEP2: Memory.remove promises1 loc ts1 ts2 val2 released2 promises2>> /\
      <<STEP3: Memory.remove promises2 loc ts2 ts3 val3 released3 promises3>>.
  Proof.
    exploit Memory.remove_get0; eauto. i.
    exploit Memory.split_exists; eauto. i. des.
    exploit LE; eauto. i.
    exploit Memory.split_exists; eauto. i. des.
    exploit commute_remove_split_remove_remove; try exact REMOVE; eauto. i. des.
    esplits; eauto. econs; eauto.
  Qed.

  Lemma commute_add_split_add_add
        mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1 mem2
        (ADD1: Memory.add mem0 loc ts1 ts3 val3 released3 mem1)
        (SPLIT2: Memory.split mem1 loc ts1 ts2 ts3 val2 val3 released2 released3 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc ts1 ts2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc ts2 ts3 val3 released3 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc ts1 ts2 val2 released2); eauto.
    { i. inv ADD1. inv ADD. hexploit DISJOINT; eauto. i.
      eapply Interval.le_disjoint; eauto. econs; [refl|].
      inv SPLIT2. inv SPLIT. left. auto.
    }
    { inv SPLIT2. inv SPLIT. auto. }
    { inv SPLIT2. inv SPLIT. auto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc ts2 ts3 val3 released3); eauto.
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        symmetry. apply Interval.disjoint_imm.
      - i. inv ADD1. inv ADD. hexploit DISJOINT; eauto. i.
        eapply Interval.le_disjoint; eauto. econs; [|refl].
        inv SPLIT2. inv SPLIT. left. auto.
    }
    { inv SPLIT2. inv SPLIT. auto. }
    { inv ADD1. inv ADD. auto. }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    inv SPLIT2. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma commute_promise_add_promise_split_promise_add_promise_add
        promises0 mem0 loc ts1 ts2 ts3 val2 val3 released2 released3
        promises1 mem1
        promises2 mem2
        (ADD1: Memory.promise promises0 mem0 loc ts1 ts3 val3 released3 promises1 mem1 Memory.promise_kind_add)
        (SPLIT2: Memory.promise promises1 mem1 loc ts1 ts2 val2 released2 promises2 mem2 (Memory.promise_kind_split ts3 val3 released3)):
    exists promises1' mem1',
      <<ADD1: Memory.promise promises0 mem0 loc ts1 ts2 val2 released2 promises1' mem1' Memory.promise_kind_add>> /\
      <<ADD2: Memory.promise promises1' mem1' loc ts2 ts3 val3 released3 promises2 mem2 Memory.promise_kind_add>>.
  Proof.
    inv ADD1. inv SPLIT2.
    exploit commute_add_split_add_add; try exact PROMISES; eauto. i. des.
    exploit commute_add_split_add_add; try exact MEM; eauto. i. des.
    esplits.
    - econs; eauto.
    - econs; eauto.
  Qed.
End MemorySplit.
