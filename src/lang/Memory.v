Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.

Set Implicit Arguments.


Module Times.
  Definition t := LocFun.t Time.t.
  Definition init: t := LocFun.init Time.elt.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (LocFun.find loc lhs) (LocFun.find loc rhs).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. reflexivity. Qed.
  Next Obligation. ii. etransitivity; eauto. Qed.

  Definition get (loc:Loc.t) (c:t) :=
    LocFun.find loc c.
End Times.

Module Snapshot.
  Structure t := mk {
    reads: Times.t;
    writes: Times.t;
  }.

  Definition init: t := mk Times.init Times.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (READS: Times.le lhs.(reads) rhs.(reads))
      (WRITES: Times.le lhs.(writes) rhs.(writes))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etransitivity; eauto.
  Qed.

  Inductive readable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | readable_intro
      (* (CoRR: Time.le (Times.get loc history.(Snapshot.reads)) ts) *)
      (CoWR: Time.le (Times.get loc history.(Snapshot.writes)) ts)
  .

  Inductive writable (history:t) (loc:Loc.t) (ts:Time.t): Prop :=
  | writable_intro
      (CoRW: Time.lt (Times.get loc history.(Snapshot.reads)) ts)
      (CoWW: Time.lt (Times.get loc history.(Snapshot.writes)) ts)
  .
End Snapshot.

Module Message.
  Structure t := mk {
    val: Const.t;
    released: Snapshot.t;
  }.
  Definition elt: t := mk 0 Snapshot.init.
End Message.

Module Cell.
  Module Raw.
    Structure t := mk {
      messages: Time.t -> option Message.t;
      ownership: Time.t -> bool;
    }.

    Definition get (ts:Time.t) (cell:t): option Message.t := cell.(messages) ts.

    Inductive belongs_to (cell:t) (ts to:Time.t): Prop :=
    | belongs_to_instro
        from msg
        (TS: Interval.mem (from, to) ts)
        (OWN: Interval.mem (from, to) <1= cell.(ownership))
        (MSG: cell.(messages) to = Some msg)
    .

    Inductive wf (cell:t): Prop :=
    | wf_intro
        (MSG: forall ts msg, cell.(messages) ts = Some msg -> cell.(ownership) ts)
        (OWN: forall ts, cell.(ownership) ts -> exists to, belongs_to cell ts to)
        (FINITE: exists tos, forall ts msg, cell.(messages) ts = Some msg -> List.In ts tos)
    .

    Lemma extensionality
          (cell1 cell2:t)
          (EQ: forall to, cell1.(messages) to = cell2.(messages) to /\ cell1.(ownership) to = cell2.(ownership) to):
      cell1 = cell2.
    Proof.
      destruct cell1, cell2.
      assert (messages0 = messages1); subst.
      { apply TimeFun.extensionality. apply EQ. }
      assert (ownership0 = ownership1); subst.
      { apply TimeFun.extensionality. i. apply EQ. }
      auto.
    Qed.

    Lemma extensionality_inv lhs rhs (EQ: lhs = rhs):
      <<MSG: forall to, lhs.(messages) to = rhs.(messages) to>> /\
      <<OWN: forall to, lhs.(ownership) to = rhs.(ownership) to>>.
    Proof. subst. auto. Qed.

    Inductive disjoint (lhs rhs:t): Prop :=
    | disjoint_intro
        (DISJOINT: forall ts, lhs.(ownership) ts -> rhs.(ownership) ts -> False)
    .

    Global Program Instance disjoint_Symmetric: Symmetric disjoint.
    Next Obligation.
      inv H. econs. i. eapply DISJOINT; eauto.
    Qed.

    Lemma disjoint_messages
          lhs rhs
          ts lmsg rmsg
          (LWF: wf lhs)
          (RWF: wf rhs)
          (DISJOINT: disjoint lhs rhs)
          (LMSG: lhs.(messages) ts = Some lmsg)
          (RMSG: rhs.(messages) ts = Some rmsg):
      False.
    Proof.
      eapply DISJOINT.
      - inv LWF. eapply MSG. eauto.
      - inv RWF. eapply MSG. eauto.
    Qed.

    Definition join (lhs rhs:t): t :=
      mk (fun t =>
            match lhs.(messages) t, rhs.(messages) t with
            | Some _, Some _ => Some Message.elt
            | Some _, None => lhs.(messages) t
            | None, _ => rhs.(messages) t
            end)
         (fun t => orb (lhs.(ownership) t) (rhs.(ownership) t)).

    Lemma join_comm lhs rhs:
      join lhs rhs = join rhs lhs.
    Proof.
      unfold join. apply extensionality. s. i. splits.
      - destruct (messages lhs to), (messages rhs to); auto.
      - apply Bool.orb_comm.
    Qed.

    Lemma join_assoc a b c:
      join a (join b c) = join (join a b) c.
    Proof.
      unfold join. apply extensionality. s. i. splits.
      - destruct (messages a to), (messages b to), (messages c to); auto.
      - apply Bool.orb_assoc.
    Qed.

    Lemma join_disjoint a b c:
      disjoint a (join b c) <-> disjoint a b /\ disjoint a c.
    Proof.
      unfold join. econs; intro X; inv X; ss.
      - splits; econs; i.
        + eapply DISJOINT; eauto. rewrite H0. auto.
        + eapply DISJOINT; eauto. rewrite H0. rewrite Bool.orb_comm. auto.
      - econs; s; i; des.
        apply Bool.orb_true_iff in H2. des.
        + eapply H; eauto.
        + eapply H0; eauto.
    Qed.

    Lemma join_wf a b
          (WFA: wf a)
          (WFB: wf b):
      wf (join a b).
    Proof.
      econs; s; i.
      - destruct (messages a ts) eqn:A.
        { inv WFA. rewrite MSG; eauto. }
        destruct (messages b ts) eqn:B.
        { inv WFB. rewrite MSG; eauto. apply Bool.orb_comm. }
        inv H.
      - apply Bool.orb_true_iff in H. des.
        + inversion WFA. exploit OWN; eauto. i. des.
          exists to. inv x. econs; s; eauto.
          * i. apply Bool.orb_true_iff. left. eapply OWN0; eauto.
          * rewrite MSG0.
            instantiate (1 := match messages b to with
                              | Some _ => Message.elt
                              | None => msg
                              end).
            destruct (messages b to); auto.
        + inversion WFB. exploit OWN; eauto. i. des.
          exists to. inv x. econs; s; eauto.
          * i. apply Bool.orb_true_iff. right. eapply OWN0; eauto.
          * rewrite MSG0.
            instantiate (1 := match messages a to with
                              | Some _ => Message.elt
                              | None => msg
                              end).
            destruct (messages a to); auto.
      - inv WFA. inv WFB. des.
        exists (tos0 ++ tos). i. apply List.in_app_iff.
        destruct (messages a ts) eqn:A.
        { left. eapply FINITE. eauto. }
        destruct (messages b ts) eqn:B.
        { right. eapply FINITE0. eauto. }
        inv H.
    Qed.

    Definition bot: t :=
      mk (fun _ => None) (fun _ => false).

    Lemma bot_wf: wf bot.
    Proof.
      unfold bot. econs; s; i.
      - inv H.
      - inv H.
      - exists []. ii. inv H.
    Qed.

    Lemma bot_disjoint cell: disjoint cell bot.
    Proof. econs. i. inv H0. Qed.

    Lemma bot_join cell: join cell bot = cell.
    Proof.
      unfold join. apply extensionality. s. i. splits.
      - destruct (messages cell to); auto.
      - apply Bool.orb_false_r.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      mk (fun ts => if Time.eq_dec ts to then Some msg else None)
         (fun ts => if Interval.mem_dec (from, to) ts then true else false).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i; timetac.
      - exists to. econs; s; i; timetac.
        + econs; eauto.
        + inv PR. timetac.
        + inv PR. timetac.
      - exists [to]. i. timetac.
    Qed.

    Inductive splits (lhs rhs:t): Prop :=
    | splits_intro
        (MSG:
           forall to msg
             (LHS: lhs.(messages) to = Some msg),
             rhs.(messages) to = Some msg)
        (OWN: lhs.(ownership) = rhs.(ownership))
    .

    Global Program Instance splits_PreOrder: PreOrder splits.
    Next Obligation.
      ii. econs; i; eauto.
    Qed.
    Next Obligation.
      ii. inv H. inv H0. econs; auto.
      i. rewrite OWN. auto.
    Qed.

    Lemma splits_disjoint a b a'
          (DISJOINT: disjoint a b)
          (SPLITS: splits a a'):
      disjoint a' b.
    Proof.
      inv SPLITS. econs. i.
      inv DISJOINT. eapply DISJOINT0; eauto.
      congruence.
    Qed.

    Lemma splits_join a b a' b'
          (WFA: wf a)
          (WFB: wf b)
          (WFA': wf a')
          (WFB': wf b')
          (DISJOINT: disjoint a b)
          (SPLITSA: splits a a')
          (SPLITSB: splits b b'):
      splits (join a b) (join a' b').
    Proof.
      inv SPLITSA. inv SPLITSB. econs; s; i.
      - destruct (messages a to) eqn:A, (messages b to) eqn:B,
                 (messages a' to) eqn:A', (messages b' to) eqn:B';
          inv LHS;
          try (erewrite MSG in *; [|by eauto]);
          try (erewrite MSG0 in *; [|by eauto]);
          try inv A'; try inv B'; eauto.
        + exfalso. eapply DISJOINT.
          * inv WFA. eauto.
          * inv WFB'. rewrite OWN0 in *. eauto.
        + exfalso. eapply DISJOINT.
          * inv WFA'. rewrite OWN in *. eauto.
          * inv WFB. eauto.
      - rewrite OWN, OWN0. auto.
    Unshelve.
    { apply Message.elt. }
    { apply Message.elt. }
    Qed.

    Lemma splits_join_inv a b c
          (WFA: wf a)
          (WFB: wf b)
          (WFC: wf c)
          (DISJOINT: disjoint a b)
          (SPLITS: splits (join a b) c):
      exists a' b',
        <<WFA': wf a'>> /\
        <<WFB': wf b'>> /\
        <<SPLITSA: splits a a'>> /\
        <<SPLITSB: splits b b'>> /\
        <<JOINC: c = join a' b'>>.
    Proof.
      exists (mk (fun t => if a.(ownership) t then c.(messages) t else None)
            (a.(ownership))).
      exists (mk (fun t => if b.(ownership) t then c.(messages) t else None)
            (b.(ownership))).
      inv SPLITS. splits.
      - econs; s; i.
        + destruct (ownership a ts); inv H. auto.
        + inv WFA. exploit OWN0; eauto. i. des.
          exists to. inv x. econs; eauto. s. rewrite OWN1.
          * apply MSG. s. rewrite MSG1.
            instantiate (1 := match messages b to with
                              | Some _ => Message.elt
                              | None => msg
                              end).
            destruct (messages b to); auto.
          * apply Interval.mem_ub. inv TS. ss. timetac.
        + inv WFC. des. exists tos. i.
          destruct (ownership a ts) eqn:O; inv H.
          eapply FINITE. eauto.
      - econs; s; i.
        + destruct (ownership b ts); inv H. auto.
        + inv WFB. exploit OWN0; eauto. i. des.
          exists to. inv x. econs; eauto. s. rewrite OWN1.
          * apply MSG. s. rewrite MSG1.
            instantiate (1 := match messages a to with
                              | Some _ => Message.elt
                              | None => msg
                              end).
            destruct (messages a to); auto.
          * apply Interval.mem_ub. inv TS. ss. timetac.
        + inv WFC. des. exists tos. i.
          destruct (ownership b ts) eqn:O; inv H.
          eapply FINITE. eauto.
      - econs; auto. s. i.
        destruct (ownership a to) eqn:O.
        + apply MSG. s. rewrite LHS. destruct (messages b to) eqn:B; auto.
          exfalso. eapply (@disjoint_messages a b); eauto.
        + destruct WFA. exploit MSG0; eauto. i. congruence.
      - econs; auto. s. i.
        destruct (ownership b to) eqn:O.
        + apply MSG. s. rewrite LHS. destruct (messages a to) eqn:A; auto.
          exfalso. eapply (@disjoint_messages a b); eauto.
        + destruct WFB. exploit MSG0; eauto. i. congruence.
      - apply extensionality. s. i. splits.
        + destruct (ownership a to) eqn:A, (ownership b to) eqn:B, (messages c to) eqn:C; auto.
          * exfalso. inv DISJOINT. eapply DISJOINT0; eauto.
          * destruct WFC. exploit MSG0; eauto.
            rewrite <- OWN. s. rewrite A, B. intuition.
        + rewrite <- OWN. auto.
    Qed.

    Lemma join2_prop
          a b c d
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (D: wf d)
          (AB: disjoint a b)
          (CD: disjoint c d)
          (AC: disjoint a c)
          (EQ: join a b = join c d):
      <<OAD: a.(ownership) <1= d.(ownership)>> /\
      <<MAD: forall ts, a.(ownership) ts -> d.(messages) ts = a.(messages) ts>> /\
      <<OWN: forall ts, a.(ownership) ts = andb (d.(ownership) ts) (negb (b.(ownership) ts))>>.
    Proof.
      apply extensionality_inv in EQ. des. splits; ss; i.
      - specialize (OWN x0). des. rewrite PR in *. ss.
        destruct (ownership c x0) eqn:CO; ss.
        exfalso. inv AC. eapply DISJOINT; eauto.
      - specialize (MSG ts).
        destruct (messages b ts) eqn:MB.
        { exfalso. inv AB. eapply DISJOINT; eauto.
          inv B. eapply MSG0; eauto.
        }
        destruct (messages c ts) eqn:MC.
        { exfalso. inv AC. eapply DISJOINT; eauto.
          inv C. eapply MSG0; eauto.
        }
        rewrite <- MSG.
        destruct (messages a ts); auto.
      - specialize (OWN ts).
        destruct (ownership a ts) eqn:OA,
                 (ownership b ts) eqn:OB,
                 (ownership c ts) eqn:OC,
                 (ownership d ts) eqn:OD; ss.
        + exfalso. inv AB. eapply DISJOINT; eauto.
        + exfalso. inv AB. eapply DISJOINT; eauto.
        + exfalso. inv AB. eapply DISJOINT; eauto.
        + exfalso. inv AC. eapply DISJOINT; eauto.
    Qed.

    Lemma join2_sub
          a b c d
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (D: wf d)
          (AB: disjoint a b)
          (CD: disjoint c d)
          (AC: disjoint a c)
          (EQ: join a b = join c d):
      exists e, <<WF: wf e>> /\
           <<DISJOINT: disjoint a e>> /\
           <<D: d = join a e>>.
    Proof.
      Ltac tac :=
        repeat
          (try match goal with
               | [H: andb _ _ = true |- _] =>
                 apply Bool.andb_true_iff in H; des
               | [H: is_true (andb _ _) |- _] =>
                 apply Bool.andb_true_iff in H; des
               | [H: andb _ _ = false |- _] =>
                 apply Bool.andb_false_iff in H; des
               | [H: (negb _) = true |- _] =>
                 apply Bool.negb_true_iff in H
               | [H: (negb _) = false |- _] =>
                 apply Bool.negb_false_iff in H

               | [H: context[if ?c then _ else _] |- _] =>
                 let X := fresh "X" in
                 destruct c eqn:X
               | [H: context[match (?c):option _ with | Some _ => _ | None => _ end] |- _] =>
                 let X := fresh "X" in
                 destruct c eqn:X
               | [|- context[if ?c then _ else _]] =>
                 let X := fresh "X" in
                 destruct c eqn:X
               | [|- context[match (?c):option _ with | Some _ => _ | None => _ end]] =>
                 let X := fresh "X" in
                 destruct c eqn:X
               end;
           ss; subst).

      exploit (@join2_prop a b c d); eauto; i; des.
      exploit (@join2_prop c d a b); eauto; i; des.
      { symmetry. auto. }
      exists (mk (fun ts => if andb (d.(ownership) ts) (negb (a.(ownership) ts))
                    then d.(messages) ts
                    else None)
            (fun ts => andb (d.(ownership) ts) (negb (a.(ownership) ts)))).
      splits.
      - econs; i; tac.
        + generalize OWN. i. specialize (OWN1 ts). rewrite H, H0 in OWN1. ss.
          symmetry in OWN1. apply Bool.negb_false_iff in OWN1.
          inv B. exploit OWN2; eauto. i. des.
          inv D. exploit OWN3; eauto. i. des.
          inv x. inv x0.
          destruct (Time.le_lt_dec to to0).
          * exists to. econs.
            { instantiate (1 := Time.max from from0).
              inv TS. inv TS0. econs; s; eauto.
              apply Time.max_spec'; auto.
            }
            { i. inv PR. ss. apply Bool.andb_true_iff.
              rewrite OWN.
              admit.
            }
            { admit. }
          * admit.
        + inv D. des. exists tos. i. tac. eapply FINITE. eauto.
      - econs; i; tac. congruence.
      - apply extensionality. i. tac.
        + inv A. exploit MSG; eauto. congruence.
        + inv A. exploit MSG; eauto. congruence.
        + inv A. exploit MSG; eauto. i. apply OAD in x. congruence.
        + rewrite OAD, MAD, X, X1; auto.
        + rewrite X0, X1. auto.
        + rewrite X0.
          destruct (messages d to) eqn:Y.
          { inv D. exploit MSG; eauto. congruence. }
          destruct (ownership a to) eqn:Z; auto.
          apply OAD in Z. congruence.
        + rewrite OAD, MAD, X, X0; auto.
    Admitted.

    Lemma join2_cancel
          a b c
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (AB: disjoint a b)
          (AC: disjoint a c)
          (EQ: join a b = join a c):
      b = c.
    Proof.
      apply extensionality. i.
      apply extensionality_inv in EQ. des.
      specialize (MSG to). specialize (OWN to). ss. splits.
      - destruct (messages a to) eqn:MA,
                 (messages b to) eqn:MB; auto.
        { exfalso. inv AB. eapply DISJOINT; eauto.
          - inv A. eauto.
          - inv B. eauto.
        }
        destruct (messages c to) eqn:MC; auto. inv MSG.
        exfalso. inv AC. eapply DISJOINT; eauto.
        + inv A. eauto.
        + inv C. eauto.
      - destruct (ownership a to) eqn:OA; ss.
        destruct (ownership b to) eqn:OB,
                 (ownership c to) eqn:OC; auto.
        + exfalso. inv AB. eapply DISJOINT; eauto.
        + exfalso. inv AC. eapply DISJOINT; eauto.
    Qed.

    Lemma join2_splits_prop
          a b c d
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (D: wf d)
          (AB: disjoint a b)
          (CD: disjoint c d)
          (AC: splits a c)
          (EQ: join a b = join c d):
      a = c.
    Proof.
      apply extensionality. i.
      apply extensionality_inv in EQ. des.
      specialize (MSG to). specialize (OWN to). ss. splits.
      - destruct (messages a to) eqn:MA.
        { inv AC. exploit MSG0; eauto. }
        destruct (messages c to) eqn:MC; auto.
        destruct (messages b to) eqn:MB.
        { exfalso. inv AB. eapply DISJOINT.
          - inv AC. rewrite OWN0. inv C. eauto.
          - inv B. eauto.
        }
        destruct (messages d to) eqn:MD; inv MSG.
      - inv AC. rewrite OWN0. auto.
    Qed.

    Lemma join2_splits
          a b c d
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (D: wf d)
          (AB: disjoint a b)
          (CD: disjoint c d)
          (AC: splits a c)
          (EQ: join a b = join c d):
      a = c /\ b = d.
    Proof.
      exploit (@join2_splits_prop a b c d); eauto. i. subst.
      splits; auto. eapply join2_cancel; eauto.
    Qed.

    Lemma join2_inv
          a b c d
          (A: wf a)
          (B: wf b)
          (C: wf c)
          (D: wf d)
          (AB: disjoint a b)
          (CD: disjoint c d)
          (AC: disjoint a c)
          (EQ: join a b = join c d):
      exists e, <<WF: wf e>> /\
           <<AE: disjoint a e>> /\
           <<CE: disjoint c e>> /\
           <<B: b = join c e>> /\
           <<D: d = join a e>>.
    Proof.
      exploit (@join2_sub a b c d); eauto. i. des. subst.
      apply join_disjoint in CD. des.
      exists e. splits; eauto.
      rewrite join_assoc, (join_comm _ a), <- join_assoc in EQ.
      apply join2_cancel in EQ; auto.
      - apply join_wf; auto.
      - apply join_disjoint. splits; auto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option Message.t := cell.(Raw.messages) ts.

  Lemma extensionality
        (cell1 cell2:t)
        (RAW: cell1.(raw) = cell2.(raw)):
    cell1 = cell2.
  Proof.
    destruct cell1, cell2. ss. subst.
    assert (WF0 = WF1) by apply proof_irrelevance; subst.
    auto.
  Qed.

  Lemma extensionality'
        (cell1 cell2:t)
        (MSG: forall to, cell1.(Raw.messages) to = cell2.(Raw.messages) to)
        (OWN: forall to, cell1.(Raw.ownership) to = cell2.(Raw.ownership) to):
    cell1 = cell2.
  Proof.
    apply extensionality. destruct cell1, cell2. ss.
    apply Raw.extensionality; auto.
  Qed.

  Lemma extensionality_inv lhs rhs (EQ: lhs = rhs):
    raw lhs = raw rhs.
  Proof.
    destruct lhs, rhs. inv EQ. auto.
  Qed.

  Definition disjoint (lhs rhs:t): Prop := Raw.disjoint lhs rhs.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    unfold disjoint in *. symmetry. auto.
  Qed.

  Definition join (lhs rhs:t): t := @mk (Raw.join lhs rhs) (Raw.join_wf lhs.(WF) rhs.(WF)).

  Lemma join_comm lhs rhs:
    join lhs rhs = join rhs lhs.
  Proof.
    apply extensionality. apply Raw.join_comm.
  Qed.

  Lemma join_assoc a b c:
    join a (join b c) = join (join a b) c.
  Proof.
    apply extensionality. apply Raw.join_assoc.
  Qed.

  Lemma join_disjoint a b c:
    disjoint a (join b c) <-> disjoint a b /\ disjoint a c.
  Proof.
    apply Raw.join_disjoint.
  Qed.

  Definition bot: t := @mk Raw.bot Raw.bot_wf.

  Lemma bot_disjoint cell: disjoint cell bot.
  Proof. apply Raw.bot_disjoint. Qed.

  Lemma bot_join cell: join cell bot = cell.
  Proof.
    apply extensionality. apply Raw.bot_join.
  Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    @mk (Raw.singleton from to msg) (Raw.singleton_wf msg LT).

  Definition init: t :=
    @singleton (Time.decr Time.elt)
               Time.elt
               (Message.mk 0 Snapshot.init)
               (Time.decr_spec Time.elt).

  Definition splits (lhs rhs:t): Prop := Raw.splits lhs rhs.

  Global Program Instance splits_PreOrder: PreOrder splits.
  Next Obligation.
    ii. unfold splits in *. reflexivity.
  Qed.
  Next Obligation.
    ii. unfold splits in *. etransitivity; eauto.
  Qed.

  Lemma splits_disjoint a b a'
        (DISJOINT: disjoint a b)
        (SPLITS: splits a a'):
    disjoint a' b.
  Proof.
    eapply Raw.splits_disjoint; eauto.
  Qed.

  Lemma splits_join a b a' b'
        (DISJOINT: disjoint a b)
        (SPLITSA: splits a a')
        (SPLITSB: splits b b'):
    splits (join a b) (join a' b').
  Proof.
    exploit (@Raw.splits_join a b a' b'); eauto; apply WF.
  Qed.

  Lemma splits_join_inv a b c
        (DISJOINT: disjoint a b)
        (SPLITS: splits (join a b) c):
    exists a' b',
      <<SPLITSA: splits a a'>> /\
      <<SPLITSB: splits b b'>> /\
      <<JOINC: c = join a' b'>>.
  Proof.
    destruct a as [a WFA], b as [b WFB], c as [c WFC].
    unfold disjoint, splits in *. ss.
    exploit (@Raw.splits_join_inv a b c); eauto. i. des. subst.
    exists (@mk a' WFA'), (@mk b' WFB'). splits; eauto.
    apply extensionality. auto.
  Qed.

  Lemma join2_splits
        a b c d
        (AB: disjoint a b)
        (CD: disjoint c d)
        (AC: splits a c)
        (EQ: join a b = join c d):
    a = c /\ b = d.
  Proof.
    exploit (@Raw.join2_splits a b c d);
      try apply WF;
      try apply AB;
      try apply CD;
      try apply AC.
    - apply extensionality_inv in EQ. auto.
    - i. des. splits; apply extensionality; auto.
  Qed.

  Lemma join2_inv
        a b c d
        (AB: disjoint a b)
        (CD: disjoint c d)
        (AC: disjoint a c)
        (EQ: join a b = join c d):
    exists e, <<B: b = join c e>> /\
         <<D: d = join a e>>.
  Proof.
    exploit (@Raw.join2_inv a b c d);
      try apply WF;
      try apply AB;
      try apply CD;
      try apply AC.
    - apply extensionality_inv in EQ. auto.
    - i. des.
      exists (@mk e WF0). splits; auto.
      + apply extensionality. auto.
      + apply extensionality. auto.
  Qed.
End Cell.

Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option Message.t :=
    Cell.get ts (mem loc).

  Definition disjoint (lhs rhs:t): Prop := forall loc, Cell.disjoint (lhs loc) (rhs loc).

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation. ii. symmetry. apply H. Qed.

  Definition join (lhs rhs:t): t := fun loc => Cell.join (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs:
    join lhs rhs = join rhs lhs.
  Proof. extensionality i. apply Cell.join_comm. Qed.

  Lemma join_assoc a b c:
    join a (join b c) = join (join a b) c.
  Proof. extensionality i. apply Cell.join_assoc. Qed.

  Lemma join_disjoint a b c:
    disjoint a (join b c) <-> disjoint a b /\ disjoint a c.
  Proof.
    unfold disjoint. econs; i; des; splits; i.
    - specialize (H loc). apply Cell.join_disjoint in H. des. auto.
    - specialize (H loc). apply Cell.join_disjoint in H. des. auto.
    - apply Cell.join_disjoint. splits; auto.
  Qed.

  Definition bot: t := LocFun.init Cell.bot.

  Lemma bot_disjoint mem: disjoint mem bot.
  Proof. ii. apply Cell.bot_disjoint. Qed.

  Lemma bot_join mem: join mem bot = mem.
  Proof.
    extensionality loc. apply Cell.bot_join.
  Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to): t :=
    (LocFun.add loc (@Cell.mk (Cell.Raw.singleton from to msg) (Cell.Raw.singleton_wf msg LT))
                (LocFun.init Cell.bot)).

  Definition init: t := LocFun.init Cell.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      ohs
      (JOIN: join lhs ohs = rhs)
      (DISJOINT: disjoint lhs ohs)
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs.
    - apply bot_join.
    - apply bot_disjoint.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - apply join_assoc.
    - symmetry in DISJOINT0. apply join_disjoint in DISJOINT0. des.
      apply join_disjoint. splits; [eauto|].
      symmetry. eauto.
  Qed.

  Lemma le_join_l lhs rhs
        (DISJOINT: disjoint lhs rhs):
    le lhs (join lhs rhs).
  Proof. econs; eauto. Qed.

  Lemma le_join_r lhs rhs
        (DISJOINT: disjoint lhs rhs):
    le rhs (join lhs rhs).
  Proof. symmetry in DISJOINT. rewrite join_comm. econs; eauto. Qed.

  Definition splits (lhs rhs:t): Prop := forall loc, Cell.splits (lhs loc) (rhs loc).

  Global Program Instance splits_PreOrder: PreOrder splits.
  Next Obligation. ii. reflexivity. Qed.
  Next Obligation. ii. etransitivity; eauto. Qed.

  Lemma splits_disjoint a b a'
        (DISJOINT: disjoint a b)
        (SPLITS: splits a a'):
    disjoint a' b.
  Proof.
    ii. eapply Cell.splits_disjoint; eauto.
  Qed.

  Lemma splits_join a b a' b'
        (DISJOINT: disjoint a b)
        (SPLITSA: splits a a')
        (SPLITSB: splits b b'):
    splits (join a b) (join a' b').
  Proof.
    ii. apply Cell.splits_join; auto.
  Qed.

  Lemma splits_join_inv a b c
        (DISJOINT: disjoint a b)
        (SPLITS: splits (join a b) c):
    exists a' b',
      <<SPLITSA: splits a a'>> /\
      <<SPLITSB: splits b b'>> /\
      <<JOINC: c = join a' b'>>.
  Proof.
    exploit (@choice Loc.t (Cell.t * Cell.t)
                     (fun loc ab =>
                        <<SPLITSA: Cell.splits (a loc) ab.(fst)>> /\
                        <<SPLITSB: Cell.splits (b loc) ab.(snd)>> /\
                        <<JOINC: (c loc) = Cell.join ab.(fst) ab.(snd)>>)).
    - i. exploit Cell.splits_join_inv; eauto. i. des.
      eexists (_, _). splits; eauto.
    - i. des.
      exists (fun loc => (f loc).(fst)), (fun loc => (f loc).(snd)). splits.
      + ii. specialize (x0 loc). des. auto.
      + ii. specialize (x0 loc). des. auto.
      + extensionality loc. specialize (x0 loc). des. auto.
  Qed.

  Inductive add (declare1 global1 declare2:t): forall (global2:t), Prop :=
  | add_intro
      ctx addendum
      (JOIN: global1 = join declare1 ctx)
      (DISJOINT: Memory.disjoint declare1 ctx)
      (SPLITS: Memory.splits declare1 declare2)
      (ADDENDUM: Memory.disjoint global1 addendum):
      add declare1 global1 declare2 (Memory.join (Memory.join declare2 ctx) addendum)
  .

  Inductive remove (loc:Loc.t) (from to:Time.t) (msg:Message.t) (lhs rhs:t): Prop :=
  | remove_intro
      (LT: Time.lt from to)
      (DISJOINT: disjoint rhs (singleton loc msg LT))
      (JOIN: lhs = join rhs (singleton loc msg LT))
  .

  Inductive future (lhs rhs:t): Prop :=
  | future_intro
      lhs'
      (SPLITS: splits lhs lhs')
      (LE: le lhs' rhs):
      future lhs rhs
  .

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. inv LE. inv LE0.
    exploit (@splits_join_inv lhs' ohs lhs'0); eauto. i. des. subst.
    rewrite <- join_assoc. econs.
    - etransitivity; eauto.
    - apply le_join_l.
      symmetry in DISJOINT0. apply join_disjoint in DISJOINT0. des.
      apply join_disjoint. splits.
      + eapply splits_disjoint; [|eauto].
        symmetry. eapply splits_disjoint; [|eauto].
        symmetry. auto.
      + symmetry. auto.
  Qed.

  Lemma le_future: le <2= future.
  Proof.
    i. econs; eauto. reflexivity.
  Qed.

  Lemma splits_future: splits <2= future.
  Proof.
    i. econs; eauto. reflexivity.
  Qed.

  Lemma join2_splits
        a b c d
        (AB: disjoint a b)
        (CD: disjoint c d)
        (AC: splits a c)
        (EQ: join a b = join c d):
    a = c /\ b = d.
  Proof.
    splits.
    - extensionality loc.
      exploit Cell.join2_splits.
      + apply AB.
      + apply CD.
      + apply AC.
      + apply (fapp _ loc) in EQ. eauto.
      + i. des. auto.
    - extensionality loc.
      exploit Cell.join2_splits.
      + apply AB.
      + apply CD.
      + apply AC.
      + apply (fapp _ loc) in EQ. eauto.
      + i. des. auto.
  Qed.

  Lemma join2_inv
        a b c d
        (AB: disjoint a b)
        (CD: disjoint c d)
        (AC: disjoint a c)
        (EQ: join a b = join c d):
    exists e, <<B: b = join c e>> /\
         <<D: d = join a e>>.
  Proof.
    exploit (@choice Loc.t Cell.t
                     (fun loc e =>
                        <<B: b loc = Cell.join (c loc) e>> /\
                        <<D: d loc = Cell.join (a loc) e>>)).
    - i. exploit (@Cell.join2_inv (a x) (b x) (c x) (d x)); eauto.
      eapply (fapp _ x) in EQ. ss.
    - i. des. exists f. splits.
      + extensionality loc. exploit x0; eauto. i. des. eauto.
      + extensionality loc. exploit x0; eauto. i. des. eauto.
  Qed.
End Memory.

Ltac memtac :=
  repeat
    (try match goal with
         | [H: Memory.le _ _ |- _] =>
           inv H
         | [H: Memory.remove _ _ _ _ _ _ |- _] =>
           inv H
         | [H: Memory.disjoint _ (Memory.join _ _) |- _] =>
           apply Memory.join_disjoint in H
         | [H: Memory.disjoint (Memory.join _ _) _ |- _] =>
           symmetry in H; apply Memory.join_disjoint in H

         | [H1: Memory.join ?a _ = Memory.join ?b _,
            H2: Memory.disjoint ?a ?b |- _] =>
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?a _ = Memory.join ?c ?b,
            H2: Memory.disjoint ?a ?b |- _] =>
           rewrite (@Memory.join_comm c b) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?c ?a = Memory.join ?b _,
            H2: Memory.disjoint ?a ?b |- _] =>
           rewrite (@Memory.join_comm c a) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?c ?a = Memory.join ?d ?b,
            H2: Memory.disjoint ?a ?b |- _] =>
           rewrite (@Memory.join_comm c a) in H1;
           rewrite (@Memory.join_comm d b) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]

         | [H1: Memory.join ?a _ = Memory.join ?b _,
            H2: Memory.disjoint ?b ?a |- _] =>
           symmetry in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?a _ = Memory.join ?c ?b,
            H2: Memory.disjoint ?b ?a |- _] =>
           symmetry in H1;
           rewrite (@Memory.join_comm c b) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?c ?a = Memory.join ?b _,
            H2: Memory.disjoint ?b ?a |- _] =>
           symmetry in H1;
           rewrite (@Memory.join_comm c a) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]
         | [H1: Memory.join ?c ?a = Memory.join ?d ?b,
            H2: Memory.disjoint ?b ?a |- _] =>
           symmetry in H1;
           rewrite (@Memory.join_comm c a) in H1;
           rewrite (@Memory.join_comm d b) in H1;
           apply Memory.join2_inv in H1; [|clear H1|clear H1|clear H1]

         | [H: Memory.disjoint ?a ?b |- Memory.disjoint ?b ?a] =>
           symmetry
         | [H1: Memory.disjoint ?a ?b, H2: Memory.splits ?a ?a' |- Memory.disjoint ?a' ?b] =>
           eapply (@Memory.splits_disjoint a b a'); eauto
         | [H1: Memory.disjoint ?a ?b, H2: Memory.splits ?a ?a' |- Memory.disjoint ?b ?a'] =>
           symmetry; eapply (@Memory.splits_disjoint a b a'); eauto
         | [H1: Memory.disjoint ?b ?a, H2: Memory.splits ?a ?a' |- Memory.disjoint ?a' ?b] =>
           symmetry in H1; eapply (@Memory.splits_disjoint a b a'); eauto
         | [H1: Memory.disjoint ?b ?a, H2: Memory.splits ?a ?a' |- Memory.disjoint ?b ?a'] =>
           symmetry; symmetry in H1; eapply (@Memory.splits_disjoint a b a'); eauto

         | [|- Memory.disjoint _ (Memory.join _ _)] =>
           apply Memory.join_disjoint
         | [|- Memory.disjoint (Memory.join _ _) _] =>
           symmetry; apply Memory.join_disjoint
         end;
     ss; des; try subst; auto).

Lemma memory_add_disjoint
      declare1 global1 declare2 global2 other
      (ADD: Memory.add declare1 global1 declare2 global2)
      (DISJOINT: Memory.disjoint declare1 other)
      (LE: Memory.le other global1):
  <<DISJOINT: Memory.disjoint declare2 other>> /\
  <<LE: Memory.le other global2>>.
Proof.
  inv ADD. memtac. splits; memtac.
  rewrite (Memory.join_comm _ (Memory.join other _)).
  rewrite <- ? Memory.join_assoc. econs; eauto.
  memtac. splits; memtac. splits; memtac.
Qed.

Lemma memory_add_future
      declare1 global1 declare2 global2
      (ADD: Memory.add declare1 global1 declare2 global2)
      (LE: Memory.le declare1 global1):
  <<FUTURE: Memory.future global1 global2>> /\
  <<LOCAL: Memory.le declare2 global2>>.
Proof.
  inv ADD. memtac. splits.
  - econs; memtac.
    + apply Memory.splits_join; memtac. reflexivity.
    + apply Memory.le_join_l. memtac. splits; memtac.
  - rewrite <- Memory.join_assoc.
    apply Memory.le_join_l. memtac. splits; memtac.
Qed.
