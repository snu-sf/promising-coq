Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import DRFBase.
Require Import SmallStep.
Require Import Race.
Require Import PIStep.

Require Import FulfillStep.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import ReorderStep.

Set Implicit Arguments.

Definition ThreadEvent_is_locally_sync (e: ThreadEvent.t) : bool :=
  match e with
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le ord Ordering.acqrel
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => Ordering.le ordw Ordering.acqrel
  | ThreadEvent.fence _ ordw => Ordering.le ordw Ordering.acqrel
  | ThreadEvent.syscall _ => false
  | _ => true
  end.

SearchAbout Memory.get.

Lemma program_step_msg_forward
      lang e th1 th2 loc ts msg
      (STEP: @Thread.program_step lang e th1 th2)
      (NOPRM: Memory.get loc ts th1.(Thread.local).(Local.promises) = None)
      (MSG: Memory.get loc ts th1.(Thread.memory) = Some msg):
  Memory.get loc ts th2.(Thread.memory) = Some msg.
Proof.
Admitted.

Lemma program_step_msg_backward
      lang e th1 th2 loc ts msg
      (STEP: @Thread.program_step lang e th1 th2)
      (NORW: forall from1 val1 rel1 ord1,
             ~ ThreadEvent.is_writing e = Some (loc, from1, ts, val1, rel1, ord1))
      (MSG: Memory.get loc ts th2.(Thread.memory) = Some msg):
  Memory.get loc ts th1.(Thread.memory) = Some msg.
Proof.
Admitted.

Lemma fence_step_local
      lc1 lc2 sc1 sc2 sc' ordr ordw
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (ORD: Ordering.le ordw Ordering.acqrel):
  Local.fence_step lc1 sc' ordr ordw lc2 sc'.
Proof.
  inv STEP. destruct ordw; [..|by exfalso; eauto]; by erewrite f_equal2; [econs|..]; eauto.
Qed.

Lemma write_step_local
      lc1 lc2 sc1 sc2 sc' mem1 mem2 loc from to val relm rel ord kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val relm rel ord lc2 sc2 mem2 kind)
      (ORD: Ordering.le ord Ordering.acqrel):
  Local.write_step lc1 sc' mem1 loc from to val relm rel ord lc2 sc' mem2 kind.
Proof.
  inv STEP. inv WRITABLE. 
  destruct ord; [..|by exfalso; eauto]
  ; by erewrite f_equal4; [econs|..]; eauto using sym_eq, TimeMap.le_join_l, TimeMap.bot_spec.
Qed.

Lemma locally_sync_sc_eq
      tid e c1 c2
      (STEP: small_step false tid e c1 c2)
      (LSYNC: ThreadEvent_is_locally_sync e):
  c1.(Configuration.sc) = c2.(Configuration.sc).
Proof.
  inv STEP; inv STEP0; inv STEP; try done; try inv LOCAL; try inv LOCAL2; try destruct ord; try destruct ordw
  ; ss; esplits; eauto using sym_eq, TimeMap.le_join_l, TimeMap.bot_spec; exfalso; eauto.
Qed.

Lemma inter_thread_reorder_read_forward
      e1 tid1 c1 e2 tid2 c2 lang2 st2 lc2 th sc
      (WF: Configuration.wf c1)
      (STEP1: small_step false tid1 e1 c1 c2)
      (TID2: IdentMap.find tid2 c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
      (STEP2: Thread.program_step e2 (Thread.mk _ st2 lc2 sc c1.(Configuration.memory)) th)
      (TNEQ: tid1 <> tid2)
      lang1 st1 lc1 loc ts val rel ord 
      (TID1: IdentMap.find tid1 c1.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
      (RD: ThreadEvent.is_reading e1 = Some (loc, ts, val, rel, ord))
      (NORDPRM: Memory.get loc ts lc2.(Local.promises) = None):
  Local.read_step lc1 th.(Thread.memory) loc ts val rel ord 
                  (Local.mk (TView.read_tview lc1.(Local.tview) loc ts rel ord) lc1.(Local.promises)).
Proof.
  erewrite <- small_step_find in TID2; eauto.

  assert (MGET: exists from, Memory.get loc ts th.(Thread.memory) = Some (from, Message.mk val rel)).
  { inv STEP1; inv STEP; inv STEP0; try done
    ; by inv RD; try inv LOCAL; try inv LOCAL1; exploit program_step_msg_forward; eauto. 
  }
  des.

  inv STEP1. rewrite TID1 in TID. depdes TID.
  inv STEP; inv STEP0; inv RD; try inv LOCAL; try inv LOCAL1; econs; eauto.
Qed.

Lemma inter_thread_reorder_read_backward
      e1 tid1 c1 e2 tid2 c2 lang2 st2 lc2 th
      (WF: Configuration.wf c1)
      (STEP1: small_step false tid1 e1 c1 c2)
      (TID2: IdentMap.find tid2 c1.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
      (STEP2: Thread.program_step e2 (Thread.mk _ st2 lc2 c2.(Configuration.sc) c2.(Configuration.memory)) th)
      (TNEQ: tid1 <> tid2)
      loc ts val rel ord 
      (RD: ThreadEvent.is_reading e2 = Some (loc, ts, val, rel, ord))
      (NORW: forall from1 val1 rel1 ord1,
             ~ ThreadEvent.is_writing e1 = Some (loc, from1, ts, val1, rel1, ord1)):
  Local.read_step lc2 c1.(Configuration.memory) loc ts val rel ord 
                  (Local.mk (TView.read_tview lc2.(Local.tview) loc ts rel ord) lc2.(Local.promises)).
Proof.
  assert (MGET: exists from, Memory.get loc ts c1.(Configuration.memory) = Some (from, Message.mk val rel)).
  { inv STEP1; inv STEP; [by inv STEP0|].
    inv STEP2; try done
    ; by inv RD; try inv LOCAL; try inv LOCAL1; exploit program_step_msg_backward; eauto. 
  }
  des.

  inv STEP2; inv RD; try inv LOCAL; try inv LOCAL1; econs; eauto.
Qed.

Lemma inter_thread_reorder_nowrite_all
      e1 tid1 c1 e2 tid2 c2 c3
      (WF: Configuration.wf c1)
      (STEP1: small_step false tid1 e1 c1 c2)
      (STEP2: small_step false tid2 e2 c2 c3)
      (TNEQ: tid1 <> tid2)
      (EVTW: ThreadEvent.is_writing e1 = None)
      (LSYNC: ThreadEvent_is_locally_sync e1 \/ ThreadEvent_is_locally_sync e2)
      (NORDPRM: forall loc ts val rel ord lang2 st2 lc2
                  (RD: ThreadEvent.is_reading e1 = Some (loc, ts, val, rel, ord))
                  (TID2: IdentMap.find tid2 c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2)),
                Memory.get loc ts lc2.(Local.promises) = None):
  exists c2',
  <<STEP1: small_step false tid2 e2 c1 c2'>> /\
  <<STEP2: small_step false tid1 e1 c2' c3>>.
Proof.
  assert (MEMEQ: c1.(Configuration.memory) = c2.(Configuration.memory)).
  { inv STEP1. inv STEP; inv STEP0; try done. }

  inv STEP2. inv STEP; [inv STEP0; done|..].
  rewrite <-MEMEQ in STEP0.
  assert (RDSTEP:= inter_thread_reorder_read_forward WF STEP1 TID STEP0 TNEQ).

  inv STEP1; inv STEP; inv STEP1; try done; inv STEP0
  ; des; assert (X:=LSYNC); eapply locally_sync_sc_eq in X; eauto; ss; subst 
  ; rewrite IdentMap.gso in NORDPRM; eauto; rewrite IdentMap.gso in TID; eauto;
  try by 
    eexists (Configuration.mk (IdentMap.add tid2 (existT _ _ _, _) c1.(Configuration.threads)) _ _);
    split; [by eauto 10 using fence_step_local, write_step_local|];
    econs; s; [rewrite IdentMap.gso | | rewrite IdentMap.add_add |]; eauto 10 using fence_step_local, write_step_local;
    inv LOCAL; eauto.
Qed.

Lemma inter_thread_reorder_write_nowrite
      e1 tid1 c1 e2 tid2 c2 c3
      (WF: Configuration.wf c1)
      (STEP1: small_step false tid1 e1 c1 c2)
      (STEP2: small_step false tid2 e2 c2 c3)
      (TNEQ: tid1 <> tid2)
      (EVTW1: ThreadEvent.is_writing e1 <> None)
      (EVTW2: ThreadEvent.is_writing e2 = None)
      (LSYNC: ThreadEvent_is_locally_sync e1 \/ ThreadEvent_is_locally_sync e2)
      (NORDPRM: forall loc ts val rel ord lang2 st2 lc2
                  (RD: ThreadEvent.is_reading e1 = Some (loc, ts, val, rel, ord))
                  (TID2: IdentMap.find tid2 c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2)),
                Memory.get loc ts lc2.(Local.promises) = None)
      (NORW: forall loc ts from1 val1 rel1 ord1 val2 rel2 ord2
               (RD: ThreadEvent.is_reading e2 = Some (loc, ts, val2, rel2, ord2)),
             ~ ThreadEvent.is_writing e1 = Some (loc, from1, ts, val1, rel1, ord1)):
  exists c2',
  <<STEP1: small_step false tid2 e2 c1 c2'>> /\
  <<STEP2: small_step false tid1 e1 c2' c3>>.
Proof.
  assert (MEMEQ: c2.(Configuration.memory) = c3.(Configuration.memory)).
  { inv STEP2. inv STEP; inv STEP0; try done. }

  inv STEP1; inv STEP; inv STEP0; try done; try (by exfalso; eauto)
  ; inv STEP2; inv STEP; inv STEP0; try done
  ; des; assert (X:=LSYNC); eapply locally_sync_sc_eq in X; eauto; ss; subst
  ; rewrite IdentMap.gso in NORDPRM; eauto; rewrite IdentMap.gso in TID0; eauto;
  try by 
    eexists (Configuration.mk (IdentMap.add tid2 (existT _ _ _, _) c1.(Configuration.threads)) _ _);
    split; [by rr; eauto 10 using fence_step_local, write_step_local, inter_thread_reorder_read_backward|];
    econs; s; [rewrite IdentMap.gso | | rewrite IdentMap.add_add |]; eauto 10 using fence_step_local, write_step_local;
    try inv LOCAL; try inv LOCAL0; eauto.
Qed.

Lemma inter_thread_reorder
      e1 tid1 c1 e2 tid2 c2 c3
      (WF: Configuration.wf c1)
      (STEP1: small_step false tid1 e1 c1 c2)
      (STEP2: small_step false tid2 e2 c2 c3)
      (TNEQ: tid1 <> tid2)
      (NORDPRM: forall loc ts val rel ord lang2 st2 lc2
                  (RD: ThreadEvent.is_reading e1 = Some (loc, ts, val, rel, ord))
                  (TID2: IdentMap.find tid2 c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2)),
                Memory.get loc ts lc2.(Local.promises) = None)
      (LSYNC: ThreadEvent_is_locally_sync e1 \/ ThreadEvent_is_locally_sync e2)
      (NORW: forall loc ts from1 val1 rel1 ord1 val2 rel2 ord2
               (RD: ThreadEvent.is_reading e2 = Some (loc, ts, val2, rel2, ord2)),
             ~ ThreadEvent.is_writing e1 = Some (loc, from1, ts, val1, rel1, ord1)):
  exists c2',
  <<STEP1: small_step false tid2 e2 c1 c2'>> /\
  <<STEP2: small_step false tid1 e1 c2' c3>>.
Proof.
  destruct (ThreadEvent.is_writing e1) as [[[[[[loc1 from1]ts1]val1]rel1]ord1]|] eqn: WRT1; cycle 1.
  { eauto using inter_thread_reorder_nowrite_all. }

  destruct (ThreadEvent.is_writing e2) as [[[[[[loc2 from2]ts2]val2]rel2]ord2]|] eqn: WRT2; cycle 1.
  { by eapply inter_thread_reorder_write_nowrite; try rewrite WRT1; eauto. }

  inv STEP1; inv STEP; inv STEP0; try done; inv STEP2; inv STEP; inv STEP0; try done; inv WRT1; inv WRT2.
  - admit.
  - admit. (* using inter_thread_reorder_read_forward *)
  - admit. (* using inter_thread_reorder_read_backward *)  
  - admit. (* using inter_thread_reorder_read_forward, inter_thread_reorder_read_backward *)  
Admitted.

