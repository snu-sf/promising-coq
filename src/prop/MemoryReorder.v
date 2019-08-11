Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.

Require Import SimMemory.
Require Import MemorySplit.

Set Implicit Arguments.


Module MemoryReorder.
  Lemma add_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2).
    { i. inv ADD2. inv ADD. eapply DISJOINT.
      etrans; [eapply Memory.add_o; eauto|]. condtac; ss; eauto.
      des. subst. erewrite Memory.add_get0 in GET2; eauto. congr.
    }
    { inv ADD2. inv ADD. auto. }
    { inv ADD2. inv ADD. eauto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1).
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        exploit Memory.add_get0; try exact ADD2; eauto.
        inv ADD2. inv ADD. symmetry. eapply DISJOINT.
        etrans; [eapply Memory.add_o; eauto|]. condtac; ss. des; congr.
      - guardH o. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto; cycle 1.
    { ii. inv H.
      exploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.add_o; eauto. condtac; ss. des; congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact ADD2; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
  Qed.

  Lemma add_split
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem2):
    (loc1 = loc2 /\ from1 = ts21 /\ to1 = ts23 /\ val1 = val23 /\ released1 = released23 /\
     exists mem1',
       <<ADD1: Memory.add mem0 loc2 ts21 ts22 val22 released22 mem1'>> /\
       <<ADD2: Memory.add mem1' loc2 ts22 ts23 val23 released23 mem2>>) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, ts23)>> /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem1'>> /\
       <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    revert GET3. erewrite Memory.add_o; eauto. condtac; ss.
    { des. i. inv GET3. left. splits; eauto.
      eapply MemorySplit.commute_add_split_add_add; eauto.
    }
    guardH o. i. right. splits.
    { ii. inv H. unguardH o. des; congr. }
    exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23); eauto;
      try by inv SPLIT2; inv SPLIT; eauto.
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1);
      try by inv ADD1; inv ADD; eauto.
    { i. revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
      - des. subst. i. inv GET0.
        inv ADD1. inv ADD. hexploit DISJOINT; eauto. i. symmetry in H.
        symmetry. eapply Interval.le_disjoint; eauto. econs; [refl|].
        inv SPLIT2. inv SPLIT. left. auto.
      - guardH o0. i. des. inv GET0.
        inv ADD1. inv ADD. hexploit DISJOINT; eauto. i. symmetry in H.
        symmetry. eapply Interval.le_disjoint; eauto. econs; [|refl].
        inv SPLIT2. inv SPLIT. left. auto.
      - guardH o0. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    i. des.
    esplits; eauto.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.split_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst.
      revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
    - guardH o0. des. repeat subst. unguardH o. des; congr.
  Qed.

  Lemma add_lower
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2 released2'
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2 released2' mem2):
    (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ val1 = val2 /\ released1 = released2 /\
     Memory.add mem0 loc1 from1 to1 val1 released2' mem2) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, to2)>> /\
     exists mem1',
       <<LOWER1: Memory.lower mem0 loc2 from2 to2 val2 released2 released2' mem1'>> /\
       <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
    - des. subst. i. inv x0. left. splits; eauto.
      inv ADD1. inv ADD. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.add in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
    - guardH o. i. right. splits.
      { ii. inv H. unguardH o. des; congr. }
      exploit (@Memory.lower_exists mem0 loc2 from2 to2); eauto.
      { inv LOWER2. inv LOWER. auto. }
      { inv LOWER2. inv LOWER. eauto. }
      { inv LOWER2. inv LOWER. auto. }
      i. des.
      exploit (@Memory.add_exists mem3 loc1 from1 to1).
      { i. revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
        - des. subst. i. inv GET2.
          inv ADD1. inv ADD. eapply DISJOINT.
          eapply Memory.lower_get0. eauto.
        - guardH o0. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
      }
      { inv ADD1. inv ADD. auto. }
      { inv ADD1. inv ADD. eauto. }
      i. des.
      esplits; eauto.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.add_o; eauto. erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
      repeat (condtac; ss). des. repeat subst.
      unguardH o. des; congr.
  Qed.

  Lemma add_remove
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (ADD1: Memory.add mem0 loc1 from1 to1 val1 released1 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 val1 released1 mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
      { des. subst. congr. }
      eauto.
    }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1);
      try by inv ADD1; inv ADD; eauto.
    { i. revert GET2. erewrite Memory.remove_o; eauto. condtac; ss.
      inv ADD1. inv ADD. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst. congr.
  Qed.

  Lemma split_add
        mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 loc2 from2 to2 val2 released2
        mem2
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2):
    <<LOCTS1: (loc1, ts12) <> (loc2, to2)>> /\
    <<LOCTS2: (loc1, ts13) <> (loc2, to2)>> /\
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem2>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2);
      try by inv ADD2; inv ADD; eauto.
    { apply covered_disjoint_get_disjoint. i. rewrite <- split_covered in H; eauto.
      eapply get_disjoint_covered_disjoint; eauto. inv ADD2. inv ADD. auto.
    }
    i. des.
    exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.add_o; eauto. condtac; ss.
      { des. subst.
        hexploit Memory.add_get0; try exact ADD2; eauto.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
      }
      eapply Memory.split_get0. eauto.
    }
    i. des.
    splits.
    { ii. inv H.
      hexploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
      guardH o0. des; congr.
    }
    { ii. inv H.
      hexploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
      guardH o. des; congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst.
      hexploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
    - guardH o. des. repeat subst.
      hexploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
  Qed.

  Lemma split_split
        mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23
        mem2
        (LOCTS1: (loc1, ts13) <> (loc2, ts23))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem2):
    (loc1 = loc2 /\ ts21 = ts11 /\ ts23 = ts12 /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts13 val22 val13 released22 released13 mem1'>> /\
       <<SPLIT2: Memory.split mem1' loc1 ts22 ts12 ts13 val12 val13 released12 released13 mem2>>) \/
    ((loc2, ts21, ts23) <> (loc1, ts11, ts12) /\
     exists mem1',
       <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem1'>> /\
       <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem2>>).
  Proof.
    exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
    revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    - i. des. inv GET3. left. splits; auto.
      exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
      exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
      revert GET4. erewrite Memory.split_o; eauto. condtac; ss.
      exploit (@Memory.split_exists mem0 loc1 ts21 ts22 ts13);
        try by inv SPLIT2; inv SPLIT; eauto.
      { etrans.
        - inv SPLIT2. inv SPLIT. eauto.
        - inv SPLIT1. inv SPLIT. eauto.
      }
      i. des.
      exploit (@Memory.split_exists mem3 loc1 ts22 ts12 ts13);
        (try by inv SPLIT1; inv SPLIT; eauto);
        (try by inv SPLIT2; inv SPLIT; eauto).
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. inv x0. inv SPLIT.
          exfalso. eapply Time.lt_strorder. eauto.
        - guardH o. des; congr.
      }
      i. des.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst. inv x1. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      + guardH o. des. repeat subst. inv x0. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
    - guardH o. i. des. inv GET3. congr.
    - guardH o. guardH o0. i. right.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23);
        try by inv SPLIT2; inv SPLIT; eauto. i. des.
      exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
        try by inv SPLIT1; inv SPLIT; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. hexploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
          revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
        - guardH o1. des. subst. unguardH o0. des; congr.
        - eapply Memory.split_get0. eauto.
      }
      i. des. splits.
      { ii. inv H. unguardH o. des; congr. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
      + guardH o1. des. repeat subst. unguardH o. des; congr.
      + guardH o1. des. repeat subst.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
      + guardH o1. guardH o2. des. repeat subst. unguardH o0. des; congr.
  Qed.

  Lemma split_lower_diff
        mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 loc2 from2 to2 val2 released2 released2'
        mem2
        (LOCTS1: (loc1, ts13) <> (loc2, to2))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2 released2' mem2):
    (loc1 = loc2 /\ ts11 = from2 /\ ts12 = to2 /\ val12 = val2 /\ released12 = released2 /\
     Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released2' released13 mem2) \/
    ((loc1, ts12) <> (loc2, to2) /\
     exists mem1',
        <<LOWER1: Memory.lower mem0 loc2 from2 to2 val2 released2 released2' mem1'>> /\
        <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto. erewrite Memory.split_o; eauto. repeat condtac; ss.
    - des. subst. i. inv x0. left. splits; auto.
      inv SPLIT1. inv SPLIT. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.split in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
    - guardH o. des. subst. congr.
    - guardH o. guardH o0. i. right.
      exploit (@Memory.lower_exists mem0 loc2 from2 to2);
        try by inv LOWER2; inv LOWER; eauto. i. des.
      exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
        try by inv SPLIT1; inv SPLIT; eauto.
      { erewrite Memory.lower_o; eauto. condtac; ss.
        { des. subst. congr. }
        eapply Memory.split_get0. eauto.
      }
      i. des.
      splits.
      { ii. inv H. exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
        revert GET2. erewrite Memory.lower_get0; eauto. congr.
      }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.split_o; eauto. erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst. congr.
      + guardH o1. des. repeat subst. congr.
  Qed.

  Lemma split_lower_same
        loc
        mem0 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 from2 val2 released2 released2'
        mem2
        (SPLIT1: Memory.split mem0 loc ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (LOWER2: Memory.lower mem1 loc from2 ts13 val2 released2 released2' mem2):
    from2 = ts12 /\ released13 = released2 /\
    exists mem1',
      <<LOWER1: Memory.lower mem0 loc ts11 ts13 val2 released2 released2' mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc ts11 ts12 ts13 val12 val13 released12 released2' mem2>>.
  Proof.
    exploit Memory.lower_get0; eauto. erewrite Memory.split_o; eauto. repeat condtac; ss; cycle 2.
    { clear -o0. des; congr. }
    { des. subst. inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto. }
    clear o a COND COND0. i. inv x0. splits; ss.
    exploit Memory.split_get0; eauto. i. des.
    exploit (@Memory.lower_exists mem0 loc ts11 ts13);
      try by inv LOWER2; inv LOWER; eauto.
    { inv SPLIT1. inv SPLIT. etrans; eauto. }
    i. des.
    exploit (@Memory.split_exists mem3 loc ts11 from2 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.lower_o; eauto. condtac; ss. des; congr. }
    i. des.
    cut (mem4 = mem2); [by i; subst; esplits; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    des. repeat subst. congr.
  Qed.

  Lemma split_lower
        mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 loc2 from2 to2 val2 released2 released2'
        mem2
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2 released2' mem2):
    (loc1 = loc2 /\ ts11 = from2 /\ ts12 = to2 /\ val12 = val2 /\ released12 = released2 /\
     Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released2' released13 mem2) \/
    ((loc1, ts12) <> (loc2, to2) /\
     exists from2' released13' mem1',
        <<LOWER1: Memory.lower mem0 loc2 from2' to2 val2 released2 released2' mem1'>> /\
        <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 val12 val13 released12 released13' mem2>>).
  Proof.
    destruct (classic ((loc1, ts13) = (loc2, to2))).
    { inv H. exploit split_lower_same; eauto. i. des. subst.
      right. esplits; eauto. ii. inv H.
      inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
    }
    { exploit split_lower_diff; eauto. i. des.
      - left. ss.
      - right. splits; ss. esplits; eauto.
    }
  Qed.

  Lemma split_remove
        mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13
        mem1 loc2 from2 to2 val2 released2
        mem2
        (LOCTS1: (loc1, ts12) <> (loc2, to2))
        (LOCTS2: (loc1, ts13) <> (loc2, to2))
        (SPLIT1: Memory.split mem0 loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<SPLIT2: Memory.split mem1' loc1 ts11 ts12 ts13 val12 val13 released12 released13 mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss.
      { des. subst. congr. }
      { guardH o. des. subst. congr. }
      eauto.
    }
    i. des.
    exploit (@Memory.split_exists mem3 loc1 ts11 ts12 ts13);
      try by inv SPLIT1; inv SPLIT; eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      { des. subst. congr. }
      eapply Memory.split_get0. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.split_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.split_o mem1); eauto.
    repeat (condtac; ss).
    - des. repeat subst. congr.
    - guardH o. des. repeat subst. congr.
  Qed.

  Lemma lower_add
        mem0 loc1 from1 to1 val1 released1 released1'
        mem1 loc2 from2 to2 val2 released2
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 val1 released1 released1' mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1 to1 val1 released1 released1' mem2>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2);
      try by inv ADD2; inv ADD; eauto.
    { apply covered_disjoint_get_disjoint. i. rewrite <- lower_covered in H; eauto.
      eapply get_disjoint_covered_disjoint; eauto. inv ADD2. inv ADD. auto.
    }
    i. des.
    exploit (@Memory.lower_exists mem3 loc1 from1 to1);
      try by inv LOWER1; inv LOWER; eauto.
    { erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. hexploit Memory.lower_get0; eauto.
        erewrite Memory.add_get0; eauto. congr.
      - eapply Memory.lower_get0. eauto.
    }
    i. des.
    esplits; eauto; cycle 1.
    { ii. inv H.
      exploit Memory.lower_get0; try exact LOWER1; eauto.
      erewrite Memory.add_get0; eauto. congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.lower_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.add_get0; try exact ADD2; eauto.
    erewrite Memory.lower_o; eauto. condtac; ss.
  Qed.

  Lemma lower_split
        mem0 loc1 from1 to1 val1 released1 released1'
        mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 val1 released1 released1' mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem2):
    exists from1' released23' mem1',
      <<SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 val22 val23 released22 released23' mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1' to1 val1 released1 released1' mem2>> /\
      <<FROM1: __guard__ ((loc1, to1, from1', released1', released23') = (loc2, ts23, ts22, released23, released1) \/
                          ((loc1, to1) <> (loc2, ts23) /\ (from1', released23') = (from1, released23)))>>.
  Proof.
    destruct (loc_ts_eq_dec (loc1, to1) (loc2, ts23)); ss.
    - des. subst.
      exploit Memory.split_get0; eauto. i. des.
      revert GET3. erewrite Memory.lower_o; eauto. condtac; ss; cycle 1.
      { des; congr. }
      i. inv GET3.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23); eauto;
        try by inv SPLIT2; inv SPLIT; eauto.
      { eapply Memory.lower_get0. eauto. }
      i. des.
      exploit (@Memory.lower_exists mem3 loc2 ts22 ts23); eauto;
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        ss. des. subst. inv SPLIT2. inv SPLIT.
        exfalso. eapply Time.lt_strorder. eauto.
      }
      { inv SPLIT2. inv SPLIT. auto. }
      i. des.
      esplits; eauto; cycle 1.
      { left. eauto. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss).
      des. repeat subst.
      revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
    - guardH o.
      exploit Memory.split_get0; eauto. i. des.
      exploit (@Memory.split_exists mem0 loc2 ts21 ts22 ts23); eauto;
        try by inv SPLIT2; inv SPLIT; eauto.
      { revert GET3. erewrite Memory.lower_o; eauto. condtac; eauto.
        ss. i. des. inv GET3. unguardH o. des; congr.
      }
      i. des.
      exploit (@Memory.lower_exists mem3 loc1 from1 to1); eauto;
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.split_o; eauto. repeat condtac; ss.
        - des. subst. hexploit Memory.split_get0; eauto.
          erewrite Memory.lower_get0; eauto. i. des. congr.
        - guardH o0. des. subst.
          unguardH o. des; congr.
        - eapply Memory.lower_get0. eauto.
      }
      i. des.
      esplits; eauto; cycle 1.
      { right. splits; eauto. ii. inv H. unguardH o. des; congr. }
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss).
      + des. repeat subst.
        revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
      + guardH o0. des. repeat subst. unguardH o. des; congr.
  Qed.

  Lemma lower_lower
        mem0 loc1 from1 to1 val1 released1 released1'
        mem1 loc2 from2 to2 val2 released2 released2'
        mem2
        (LOWER1: Memory.lower mem0 loc1 from1 to1 val1 released1 released1' mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2 released2' mem2):
    (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ val1 = val2 /\ released1' = released2 /\
     Memory.lower mem0 loc1 from1 to1 val1 released1 released2' mem2) \/
    (<<LOCTS1: (loc1, to1) <> (loc2, to2)>> /\
     exists mem1',
       <<LOWER1: Memory.lower mem0 loc2 from2 to2 val2 released2 released2' mem1'>> /\
       <<LOWER2: Memory.lower mem1' loc1 from1 to1 val1 released1 released1' mem2>>).
  Proof.
    exploit Memory.lower_get0; eauto.
    erewrite Memory.lower_o; eauto. condtac; ss.
    - des. subst. i. inv x0. left. splits; eauto.
      inv LOWER1. inv LOWER. inv LOWER2. inv LOWER.
      rewrite LocFun.add_add_eq. econs; auto.
      unfold Cell.lower in *.
      destruct r, r0. ss. subst.
      unfold LocFun.add. condtac; [|congr]. s.
      rewrite DOMap.add_add_eq. econs; auto.
      etrans; eauto.
    - guardH o. i. right. splits.
      { ii. inv H. unguardH o. des; congr. }
      exploit (@Memory.lower_exists mem0 loc2 from2 to2); eauto.
      { inv LOWER2. inv LOWER. auto. }
      { inv LOWER2. inv LOWER. eauto. }
      { inv LOWER2. inv LOWER. auto. }
      i. des.
      exploit (@Memory.lower_exists mem3 loc1 from1 to1);
        try by inv LOWER1; inv LOWER; eauto.
      { erewrite Memory.lower_o; eauto. condtac; ss.
        - des. subst. unguardH o. des; congr.
        - eapply Memory.lower_get0. eauto.
      }
      i. des.
      esplits; eauto.
      cut (mem4 = mem2); [by i; subst; eauto|].
      apply Memory.ext. i.
      erewrite Memory.lower_o; eauto. erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
      repeat (condtac; ss). des. repeat subst.
      unguardH o. des; congr.
  Qed.

  Lemma lower_remove
        mem0 loc1 from1 to1 val1 released1 released1'
        mem1 loc2 from2 to2 val2 released2
        mem2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (LOWER1: Memory.lower mem0 loc1 from1 to1 val1 released1 released1' mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 val2 released2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 val2 released2 mem1'>> /\
      <<LOWER2: Memory.lower mem1' loc1 from1 to1 val1 released1 released1' mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.lower_o; eauto. condtac; ss.
      { des. subst. congr. }
      eauto.
    }
    i. des.
    exploit (@Memory.lower_exists mem3 loc1 from1 to1);
      try by inv LOWER1; inv LOWER; eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss.
      { des. subst. congr. }
      inv LOWER1. inv LOWER. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.lower_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.lower_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst. congr.
  Qed.

  Lemma remove_add
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 val2 released2 mem2)
        (ADD1: Memory.add mem0 loc2 from2 to2 val2 released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. erewrite Memory.add_get0 in x0; eauto. congr.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. congr.
  Qed.

  Lemma remove_split
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (SPLIT2: Memory.split mem1 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem2)
        (SPLIT1: Memory.split mem0 loc2 ts21 ts22 ts23 val22 val23 released22 released23 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit Memory.split_get0; try exact SPLIT1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.split_o; eauto. repeat condtac; ss.
      - des. subst. congr.
      - guardH o. des. subst. rewrite GET3 in x0. inv x0.
        exploit Memory.split_get0; try exact SPLIT2; eauto. i. des.
        revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.split_o; eauto.
    erewrite (@Memory.split_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss).
    - des; congr.
    - guardH o. des. repeat subst. rewrite GET3 in x0. inv x0.
      exploit Memory.remove_get0; try exact x1; eauto.
      erewrite Memory.split_o; eauto. repeat condtac; ss. i. inv x0.
      inv SPLIT1. inv SPLIT. exfalso. eapply Time.lt_strorder. eauto.
  Qed.

  Lemma remove_lower
        mem0 loc1 from1 to1 val1 released1
        mem1 loc2 from2 to2 val2 released2' released2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 val1 released1 mem1)
        (LOWER2: Memory.lower mem1 loc2 from2 to2 val2 released2' released2 mem2)
        (LOWER1: Memory.lower mem0 loc2 from2 to2 val2 released2' released2 mem1'):
    Memory.remove mem1' loc1 from1 to1 val1 released1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.lower_o; eauto. condtac; ss.
      des. subst.
      exploit Memory.lower_get0; try exact LOWER2; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst.
    exploit Memory.lower_get0; try exact LOWER2; eauto.
    erewrite Memory.remove_o; eauto. condtac; ss.
  Qed.

  Lemma remove_remove
        promises0 loc1 from1 to1 val1 released1
        promises1 loc2 from2 to2 val2 released2
        promises2
        (REMOVE1: Memory.remove promises0 loc1 from1 to1 val1 released1 promises1)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<REMOVE2: Memory.remove promises1' loc1 from1 to1 val1 released1 promises2>>.
  Proof.
    exploit Memory.remove_get0; try apply REMOVE2; eauto.
    erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
    exploit Memory.remove_exists; eauto. i. des.
    exploit Memory.remove_get0; try apply REMOVE1; eauto. i.
    exploit (@Memory.remove_exists mem2 loc1 from1 to1 val1 released1); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss. des. subst. congr. }
    i. des.
    esplits; eauto.
    cut (mem0 = promises2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o promises2); eauto. erewrite (@Memory.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.

  Lemma promise_add_promise_add
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2 mem2
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.op_kind_add)
        (PROMISE2: Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2 mem2 Memory.op_kind_add):
    exists promises1' mem1',
      <<PROMISE1: Memory.promise promises0 mem0 loc2 from2 to2 val2 released2 promises1' mem1' Memory.op_kind_add>> /\
      <<PROMISE2: Memory.promise promises1' mem1' loc1 from1 to1 val1 released1 promises2 mem2 Memory.op_kind_add>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    inv PROMISE1. inv PROMISE2.
    exploit add_add; try exact PROMISES; eauto. i. des.
    exploit add_add; try exact MEM; eauto. i. des.
    esplits; eauto.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma promise_add_remove
        loc1 from1 to1 val1 released1
        loc2 from2 to2 val2 released2
        promises0 mem0
        promises1 mem1
        promises2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (PROMISE1: Memory.promise promises0 mem0 loc1 from1 to1 val1 released1 promises1 mem1 Memory.op_kind_add)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 val2 released2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 val2 released2 promises1'>> /\
      <<PROMISE2: Memory.promise promises1' mem0 loc1 from1 to1 val1 released1 promises2 mem1 Memory.op_kind_add>>.
  Proof.
    inv PROMISE1.
    exploit add_remove; try exact PROMISES; eauto. i. des.
    esplits; eauto. econs; eauto.
  Qed.

  Lemma remove_promise
        promises1 loc1 from1 to1 val1 released1
        promises2 loc2 from2 to2 val2 released2
        promises3
        mem1 mem3
        kind
        (LE: Memory.le promises1 mem1)
        (REMOVE: Memory.remove promises1 loc1 from1 to1 val1 released1 promises2)
        (PROMISE: Memory.promise promises2 mem1 loc2 from2 to2 val2 released2 promises3 mem3 kind):
    exists promises2',
      Memory.promise promises1 mem1 loc2 from2 to2 val2 released2 promises2' mem3 kind /\
      Memory.remove promises2' loc1 from1 to1 val1 released1 promises3.
  Proof.
    inv PROMISE.
    - exploit Memory.add_exists_le; eauto. i. des.
      exploit remove_add; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.split_get0; try eexact PROMISES; eauto. i. des.
      revert GET3. erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.split_exists; eauto; try by inv PROMISES; inv SPLIT; eauto. i. des.
      exploit remove_split; eauto. i.
      esplits; eauto. econs; eauto.
    - exploit Memory.lower_get0; try eexact PROMISES; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
      exploit Memory.lower_exists; eauto; try by inv PROMISES; inv LOWER; eauto. i. des.
      exploit remove_lower; eauto. i.
      esplits; eauto. econs; eauto.
  Qed.
End MemoryReorder.
