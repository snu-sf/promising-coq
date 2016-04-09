Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.

Set Implicit Arguments.


Module Commit.
  Structure t := mk {
    current: Snapshot.t;
    released: LocFun.t Snapshot.t;
    acquirable: Snapshot.t;
  }.

  Definition init: t := mk Snapshot.init (LocFun.init Snapshot.init) Snapshot.init.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: Snapshot.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Snapshot.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Snapshot.le lhs.(acquirable) rhs.(acquirable))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etransitivity; eauto.
  Qed.

  Inductive read
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | read_intro
      (MONOTONE: le tc1 tc2)
      (READABLE: Snapshot.readable tc1.(current) loc ts)
      (READ: Time.le ts (Times.get loc tc2.(current).(Snapshot.reads)))
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le released tc2.(current))
      (ACQUIRABLE: Snapshot.le released tc2.(acquirable))
  .

  Inductive write
            (tc1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | write_intro
      (MONOTONE: le tc1 tc2)
      (WRITABLE: Snapshot.writable tc1.(current) loc ts)
      (WRITE: Time.le ts (Times.get loc tc2.(current).(Snapshot.writes)))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord),
          Snapshot.le tc2.(current) released)
      (RELEASED: Snapshot.le (LocFun.find loc tc2.(Commit.released)) released)
  .

  Inductive fence
            (tc1:t) (ord:Ordering.t)
            (tc2:t): Prop :=
  | fence_intro
      (MONOTONE: le tc1 tc2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le tc2.(acquirable) tc2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          Snapshot.le tc2.(current) (LocFun.find loc tc2.(released)))
  .
End Commit.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Definition syntax := lang.(Language.syntax).

    Structure t := mk {
      state: lang.(Language.state);
      commit: Commit.t;
      local: Memory.t;
    }.

    Definition init (s:syntax) :=
      mk (lang.(Language.init) s)
         Commit.init
         Memory.init.

    Inductive is_terminal (th:t): Prop :=
    | is_terminal_intro
        (STATE: lang.(Language.is_terminal) th.(state))
        (LOCAL: th.(local) = Memory.init)
    .

    Inductive memory_step (th1:t) (mem1:Memory.t): forall (th2:t), Prop :=
    | step_read
        loc val ts released ord st2 commit2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.read loc val ord))) st2)
        (READ: Commit.read th1.(commit) loc ts released ord commit2)
        (MESSAGE: Memory.get loc ts mem1 = Some (Message.mk val released))
        (LOCAL: Memory.get loc ts th1.(local) = None):
        memory_step th1 mem1
                    (mk st2 commit2 th1.(local))
    | step_write
        loc val ts released ord st2 commit2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.write loc val ord))) st2)
        (WRITE: Commit.write th1.(commit) loc ts released ord commit2)
        (MESSAGE: Memory.get loc ts th1.(local) = Some (Message.mk val released)):
        memory_step th1 mem1
                    (mk st2 commit2 (Memory.remove loc ts th1.(local)))
    | step_update
        loc valr tsr releasedr valw tsw releasedw ord st3 commit2 commit3
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.update loc valr valw ord))) st3)
        (READ: Commit.read th1.(commit) loc tsr releasedr ord commit2)
        (WRITE: Commit.write commit2 loc tsw releasedw ord commit3)
        (RELEASE: Snapshot.le releasedr releasedw)
        (MESSAGE1: Memory.get loc tsr mem1 = Some (Message.mk valr releasedr))
        (MESSAGE2: Memory.get loc tsw th1.(local) = Some (Message.mk valw releasedw)):
        memory_step th1 mem1
                    (mk st3 commit3 (Memory.remove loc tsw th1.(local)))
    | step_fence
        ord st2 commit2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.fence ord))) st2)
        (FENCE: Commit.fence th1.(commit) ord commit2):
        memory_step th1 mem1
                    (mk st2 commit2 th1.(local))
    | step_None
        st2 commit2
        (STATE: lang.(Language.step) th1.(state) None st2)
        (COMMIT: Commit.le th1.(commit) commit2):
        memory_step th1 mem1
                    (mk st2 commit2 th1.(local))
    .

    Inductive declare_step (th1:t) (mem1:Memory.t): forall (th2:t) (mem2:Memory.t), Prop :=
    | declare_step_intro
        loc from to msg st2 commit2 local2 mem2
        (STATE: th1.(state) = st2)
        (COMMIT: Commit.le th1.(commit) commit2)
        (LOCAL: Memory.declare loc from to msg th1.(local) local2)
        (MEMORY: Memory.declare loc from to msg mem1 mem2):
        declare_step th1 mem1
                     (mk st2 commit2 local2) mem2
    .

    Inductive step: forall (e:option Event.t) (th1:t) (mem1:Memory.t) (th2:t) (mem2:Memory.t), Prop :=
    | step_memory
        th1 th2 mem
        (STEP: memory_step th1 mem th2):
        step None th1 mem th2 mem
    | step_declare
        th1 mem1 th2 mem2
        (STEP: declare_step th1 mem1 th2 mem2):
        step None th1 mem1 th2 mem2
    | step_external
        st1 st2 commit1 commit2 mem e
        (STATE: lang.(Language.step) st1 (Some (ThreadEvent.syscall e)) st2)
        (COMMIT: Commit.le commit1 commit2):
        step (Some e)
             (mk st1 commit1 Memory.init) mem
             (mk st2 commit2 Memory.init) mem
    .

    Inductive internal_step (c1 c2:t * Memory.t): Prop :=
    | internal_step_intro
        (STEP: step None c1.(fst) c1.(snd) c2.(fst) c2.(snd))
    .

    Definition consistent (th1:t) (mem:Memory.t): Prop :=
      forall mem1
        (LOCAL: Memory.le th1.(local) mem1)
        (FUTURE: Memory.future mem mem1),
      exists th2 mem2,
        <<STEPS: rtc internal_step (th1, mem1) (th2, mem2)>> /\
        <<DECLARE: th2.(local) = Memory.init>>.

    Lemma disjoint_memory_step
          th1 mem1 th2 mem_o
          (STEP: memory_step th1 mem1 th2)
          (DISJOINT: Memory.disjoint th1.(local) mem_o)
          (LE: Memory.le mem_o mem1):
      Memory.disjoint th2.(local) mem_o.
    Proof.
      inv STEP; simpl in *; auto.
      - apply Memory.remove_disjoint. auto.
      - apply Memory.remove_disjoint. auto.
    Qed.

    Lemma disjoint_declare_step
          th1 mem1 th2 mem2 mem_o
          (STEP: declare_step th1 mem1 th2 mem2)
          (DISJOINT: Memory.disjoint th1.(local) mem_o)
          (LE: Memory.le mem_o mem1):
      <<DISJOINT: Memory.disjoint th2.(local) mem_o>> /\
      <<LE: Memory.le mem_o mem2>>.
    Proof.
      inv STEP. splits; s.
      - admit.
      - admit.
    Admitted.

    Lemma disjoint_step
          th1 mem1 th2 mem2 e mem_o
          (STEP: step e th1 mem1 th2 mem2)
          (DISJOINT: Memory.disjoint th1.(local) mem_o)
          (LE: Memory.le mem_o mem1):
      <<DISJOINT: Memory.disjoint th2.(local) mem_o>> /\
      <<LE: Memory.le mem_o mem2>>.
    Proof.
      inv STEP.
      - splits; auto.
        eapply disjoint_memory_step; eauto.
      - eapply disjoint_declare_step; eauto.
      - simpl in *. splits; auto.
    Qed.

    Lemma disjoint_internal_step
          th1 mem1 th2 mem2 mem_o
          (STEP: Thread.internal_step (th1, mem1) (th2, mem2))
          (DISJOINT: Memory.disjoint th1.(local) mem_o)
          (LE: Memory.le mem_o mem1):
      <<DISJOINT: Memory.disjoint th2.(local) mem_o>> /\
      <<LE: Memory.le mem_o mem2>>.
    Proof.
      inv STEP. eapply disjoint_step; eauto.
    Qed.

    Lemma disjoint_rtc_internal_step
          thm1 thm2 mem_o
          (STEPS: rtc Thread.internal_step thm1 thm2)
          (DISJOINT: Memory.disjoint thm1.(fst).(local) mem_o)
          (LE: Memory.le mem_o thm1.(snd)):
      <<DISJOINT: Memory.disjoint thm2.(fst).(local) mem_o>> /\
      <<LE: Memory.le mem_o thm2.(snd)>>.
    Proof.
      revert DISJOINT LE. induction STEPS; auto. i.
      destruct x, y. exploit disjoint_internal_step; eauto. i. des.
      apply IHSTEPS; auto.
    Qed.

    Lemma future_step
          th1 mem1 th2 mem2 e
          (STEP: step e th1 mem1 th2 mem2)
          (LE: Memory.le th1.(local) mem1):
      <<FUTURE: Memory.future mem1 mem2>> /\
      <<LE: Memory.le th2.(local) mem2>>.
    Proof.
      inv STEP; ss.
      - splits; [reflexivity|].
        inv STEP0; ss; auto.
        + apply Memory.remove_le. auto.
        + apply Memory.remove_le. auto.
      - inv STEP0. s. splits.
        + eapply Memory.declare_future. eauto.
        + eapply Memory.declare_le; eauto.
      - splits; auto. reflexivity.
    Qed.

    Lemma future_internal_step
          th1 mem1 th2 mem2
          (STEP: Thread.internal_step (th1, mem1) (th2, mem2))
          (LE: Memory.le th1.(local) mem1):
      <<FUTURE: Memory.future mem1 mem2>> /\
      <<LE: Memory.le th2.(local) mem2>>.
    Proof.
      inv STEP. eapply future_step; eauto.
    Qed.

    Lemma future_rtc_internal_step
          thm1 thm2
          (STEPS: rtc Thread.internal_step thm1 thm2)
          (LE: Memory.le thm1.(fst).(local) thm1.(snd)):
      <<FUTURE: Memory.future thm1.(snd) thm2.(snd)>> /\
      <<LE: Memory.le thm2.(fst).(local) thm2.(snd)>>.
    Proof.
      induction STEPS.
      { splits; auto. reflexivity. }
      destruct x, y. apply future_internal_step in H; auto. des.
      exploit IHSTEPS; eauto. i. des.
      splits; auto.
      rewrite FUTURE. auto.
    Qed.
  End Thread.
End Thread.
