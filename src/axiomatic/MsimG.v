(******************************************************************************)
(** * Simulation between axiomatic and operational machines *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.
Require Import Time.
Require Import Configuration.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Thread.
Require Import TView.

Require Import Gevents.
Require Import model.
Require Import Gstep GstepRead GstepWrite GstepFence GstepOther.
Require Import Machine.
Require Import SimRel SimPreservation.

Set Implicit Arguments.
Remove Hints plus_n_O.

Require Import Setoid Permutation.

Hint Resolve gstep_wf gstep_inc coh_wf.

Lemma foo (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

Lemma gstep_tm_to_a acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  tm l 
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' l ;; hb acts' sb' rmw' rf') (tm acts' sb' rmw' rf' sc' l))
  (TM_MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc l x y -> In y acts)
   x (CUR: t_cur tm acts sb rmw rf sc (thread a) l x) :
   tm acts' sb' rmw' rf' sc' l x a.
Proof.
red in CUR; red in CUR; desc.
red in CUR; desc.
unfold seq, eqv_rel in *.
desc; subst.
apply TM_HB; exists y; split.
apply TM_MON; done.
apply sb_in_hb; eapply gstep_sb; eauto.
right; red; repeat (eexists; splits; eauto).
Qed.

(******************************************************************************)
(** * Lemmas for the read step   *)
(******************************************************************************)

Lemma Readable_cur_tm acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  tm (CUR: max_value f (t_cur tm acts sb rmw rf sc (thread a) l) t) 
  (WRITE : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> is_write x)
  (ACTS : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> In x acts)
  (COHERENT: forall c, mo' b c -> tm acts' sb' rmw' rf' sc' l c a -> False)
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' l ;; hb acts' sb' rmw' rf') 
                    (tm acts' sb' rmw' rf' sc' l))
  (TM_MON: inclusion (tm acts sb rmw rf sc l) (tm acts' sb' rmw' rf' sc' l))
  (TM_DOMa: doma (tm acts sb rmw rf sc l) (fun e => loc e = Some l))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc l x y -> In y acts)
  (RFb: rf' b a) : Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in CUR; desf.
apply Time.bot_spec.
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP; desf. 
eapply monotone_converse with (acts:=(a :: acts)); ins; eauto using rf_acta, rf_doma.
- by eapply rf_acta in RFb; try eassumption.
- eapply rf_doma in RFb; eauto.
- by destruct INam; desc; pattern a_max; eapply c_cur_doma; eauto.
- by eapply loceq_rf in RFb; eauto; unfold loc in *; rewrite LABa in RFb.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  cdes WF'; eauto.
- intro.
  eapply COHERENT; eauto.
  eapply gstep_non_write_mo with (acts:=acts) (mo:=mo); eauto.
  eapply gstep_tm_to_a; eauto.
Qed.

Lemma Readable_msg_sc acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) t)
  (RFb: rf' b a) (SC: is_sc a): Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in MSG; desf.
apply Time.bot_spec.
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP. 
eapply monotone_converse with (acts:=(a :: acts)); eauto.
- right; eapply acta_msg_scr; eauto.
- eapply rf_acta in RFb; eauto. rewrite <- ACT_STEP; eauto.
- eauto with rel.
- eapply rf_doma in RFb; eauto.
- eauto with rel.
- eapply loceq_rf in RFb; eauto. unfold loc in *. rewrite LABa in RFb. auto.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  rewrite <- ACT_STEP.
  cdes WF'; eauto.
- intro. 
  eapply (Coherent_m_scr COH'); eauto. 
  eapply gstep_non_write_mo with (mo:=mo); eauto.
  eapply (gstep_msg_rel_scr_nonwrite COH GSTEP); eauto. 
Qed.

Lemma Readable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  view rel
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) (View.sc rel.(View.unwrap) l))
  (CUR: sim_cur f acts sb rmw rf sc view (thread a))
  (RFb: rf' b a): 
    TView.readable view l (f b) rel o.
Proof.
red in CUR; desc.
constructor; try intro.
-  eapply Readable_cur_tm; eauto using Coherent_urr, urr_hb, urr_mon with rel acts.
   by eapply urr_actb; eauto.
- eapply Readable_cur_tm; eauto using rwr_hb, rwr_mon with rel acts.
  ins; eapply Coherent_rwr with (mo:=mo'); eauto.
  right; splits; eauto with acts.
  eapply rwr_actb; eauto.
- eapply Readable_cur_tm; eauto using scr_hb, scr_mon with rel acts.
  ins; eapply Coherent_scr_rf with (mo:=mo');  eauto with acts.
  eapply scr_actb; eauto.
- eapply Readable_msg_sc; eauto with acts.
Qed.

(******************************************************************************)
(** * Lemmas for the write step   *)
(******************************************************************************)

Lemma Writable_cur_rwr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l) t) 
  (N_ZERO: Time.lt Time.bot (f' a)) : Time.lt t (f' a).
Proof.
red in CUR; desf; try done.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts. 
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP.
  cdes WF'; eauto.
- intro.
  eapply Coherent_rwr; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply rwr_hb.
  eapply rwr_mon; eauto.
  eapply rwr_actb; eauto.
- intro; subst; eauto with acts.
Qed.

Lemma Writable_cur_scr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l) t) 
  (SC: is_sc a) 
  (N_ZERO: Time.lt Time.bot (f' a)) : Time.lt t (f' a).
Proof.
red in CUR; desf; try done.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts.
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP; cdes WF'; eauto.
- intro.
  eapply Coherent_scr_eq; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply scr_hb.
  eapply scr_mon; eauto.
  eapply scr_actb; eauto.
- intro; subst; eauto with acts. 
Qed.

Lemma Writable_sc_map acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (SCMAP: max_value f (S_tm acts sb rmw rf l) t)
  (SC: is_sc a) 
  (N_ZERO: Time.lt Time.bot (f' a)) : Time.lt t (f' a).
Proof.
red in SCMAP; desf; try done.
eapply TimeFacts.le_lt_lt with (b:=f a_max); try done.
cdes GSTEP.
rewrite <- F; eauto with acts.
eapply monotone_converse_strict with (acts:=(a :: acts)); eauto.
- right; eauto with acts. 
- left; done.
- eauto with rel.
- eauto with acts.
- eauto with rel.
- unfold loc; rewrite LABa; done.
- rewrite <- ACT_STEP; cdes WF'; eauto.
- intro.
  eapply Coherent_scr_eq; eauto.
  red in INam; red in INam; desc.
  eapply S_tm_sc with (b:=y); eauto with acts.
  eapply S_tmr_mon; eauto.
  apply SC_AT_END; eauto 4 with acts.
  apply S_tmr_domb in INam; done.
  eapply S_tmr_actb; eauto.
  intro; subst; apply FRESH; eapply S_tmr_actb; eauto.
- intro; subst; eauto with acts. 
Qed.

Lemma Writable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  (COH: Coherent acts sb rmw rf mo sc) 
  (COH': Coherent acts' sb' rmw' rf' mo' sc') 
  f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') (N_ZERO: Time.lt Time.bot (f' a))
  l v o (LABa: lab a = Astore l v o)
  view sc_map
  (SC : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (sc_map l))
  (CUR: sim_cur f acts sb rmw rf sc view (thread a)):
  TView.writable view sc_map l (f' a) o.
Proof.
red in CUR; desc.
constructor; try intro.
eapply Writable_cur_rwr; eauto.
eapply Writable_cur_scr; eauto with acts.
eapply Writable_sc_map; eauto with acts.
Qed.

(******************************************************************************)
(** * Main Theorem: the operational machine simulates the axiomatic machine   *)
(******************************************************************************)

Definition proof_obligation ax_st G' op_st i lang st st' :=
  forall
   G (G_ : G = exec ax_st)
   (COH : Coherent (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G))
   (WF_OP_ST : Configuration.wf op_st)
   (STATES : ts ax_st = IdentMap.map fst (Configuration.threads op_st))
   ffrom fto 
  (TIME : sim_time (Configuration.threads op_st) (Configuration.sc op_st)
          (Configuration.memory op_st) G ffrom fto) tview
   j (THREAD: i = Some j)
   (TVIEW : sim_tview fto (acts G) (sb G) (rmw G) (rf G) (sc G) tview i)
   (LWF : TView.wf tview)
   (SPACE : forall x y (MO: mo G x y) (NRMW: ~ (rf G ;; rmw G) x y),
                 fto x <> ffrom y)
   (BSPACE : forall y (INy: In y (acts G)) (W: is_write y) (P: is_proper y)
                       (NRMW: ~ exists x, (rf G ;; rmw G) x y),
                 Time.bot <> ffrom y),
  exists te tview' sc' mem' op_st' threads' local', 
    << OP_ST': op_st' = Configuration.mk threads' sc' mem' >> /\ 
     << THREAD': threads' = IdentMap.add j (existT Language.state lang st', local') 
                                          (Configuration.threads op_st) >> /\ 
     << LOCAL': local' = Local.mk tview' Memory.bot >> /\ 
     << STEP: Thread.program_step te 
                    (Thread.mk lang st (Local.mk tview Memory.bot) 
                               (Configuration.sc op_st) (Configuration.memory op_st))
                    (Thread.mk lang st' local' sc' mem') >> /\
      exists ffrom' fto', 
      << F_FROM: forall b, In b (acts G) -> ffrom' b = ffrom b >> /\
      << F_TO: forall b, In b (acts G) -> fto' b = fto b >> /\
      << MONOTONE: monotone (mo G') fto' >> /\  
      << SIM_TVIEW: sim_tview fto' (acts G') (sb G') (rmw G') (rf G') (sc G') tview' i >> /\
      << SIM_SC_MAP: forall l, max_value fto' (S_tm (acts G') (sb G') (rmw G') (rf G') l) 
                                         (LocFun.find l sc')  >> /\
      << SIM_MEM: sim_mem ffrom' fto' (acts G') (sb G') (rmw G') (rf G') (sc G') mem'  >> /\
      << SPACE : forall x y (MO: mo G' x y) (NRMW: ~ (rf G' ;; rmw G') x y),
                 fto' x <> ffrom' y >> /\
      << BSPACE : forall y (INy: In y (acts G')) (W: is_write y) (P: is_proper y)
                       (NRMW: ~ exists x, (rf G' ;; rmw G') x y),
                 Time.bot <> ffrom' y >>.


Lemma ax_op_sim_step_read :
  forall op_st ths G G' a l v o (LABa : lab a = Aload l v o)
   (GSTEP : gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) 
          (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
   (COH' : Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
   lang st st' (STATE : Language.step lang (ProgramEvent.read l v o) st st'),
  proof_obligation {|ts:=ths; exec:=G|} G' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; desc.
  subst G0; destruct G, G'; simpl; ins.

generalize (gstep_read_rf COH GSTEP LABa); intro; desc.

assert (E: exists from rel, Memory.get l (fto b) (Configuration.memory op_st) = 
          Some (from, Message.mk v rel) /\ sim_mem_helper fto acts sb rmw rf sc b from v rel.(View.unwrap)).
{ cdes COH; cdes WF.
  by eexists; eapply sim_mem_get; eauto with acts; destruct b as [??[]]; ins; desf.
}

desc; red in E0; desc.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.
assert (LOC_B: Gevents.loc b = Some l). 
  unfold Gevents.loc; destruct (lab b); ins; desf.

eexists _,_,_,_,_,_,_.
splits; eauto.
- econs; [|eapply Local.step_read]; eauto.
  econstructor; eauto.
  red in TVIEW; red in SIMMSG; desc.
  eapply Readable_full;eauto. 
- exists ffrom, fto; splits; eauto.
  * rewrite <- gstep_non_write_mo; eauto with acts.
  * eapply tview_step_read with (acts := acts) (acts0 := acts0); eauto.
  * ins. eapply max_value_same_set; try edone.
    ins; rewrite gstep_S_tm_other; eauto with acts.
  * eapply memory_step_nonwrite with (acts := acts) (acts0 := acts0); eauto with acts.
  * ins; eapply SPACE.
      by eapply gstep_mo; eauto; intro; subst; 
         [eapply mo_doma in MO|eapply mo_domb in MO]; 
         eauto; destruct a as [??[]].
    intro X; apply (gstep_rf_rmw_nonwrite COH GSTEP) in X; eauto;
    by destruct a as [??[]].
  * cdes GSTEP; subst; ins. 
    destruct INy; subst.
    by destruct y as [??[]].
    apply BSPACE; eauto; intro; desc; apply NRMW; eexists.
    by eapply seq_mori; eauto using rf_mon, rmw_mon.
Qed.


Lemma memory_add_bot l from to val released (LT : Time.lt from to) 
      (WF : View.opt_wf released) :
  Memory.add Memory.bot l from to val released 
    (Memory.singleton l val released LT). 
Proof.
  econs; econs; eauto.
  red; ins; unfold DenseOrder.DOMap.find in *; ins.
  rewrite DenseOrder.DOMap.Raw.gempty in *; ins.
Qed.

Lemma memory_exists 
  mem (CLOSED: Memory.closed mem)
  from to (FROM: Time.lt from to)
  tview (CWF: TView.wf tview)
  released (RWF: View.opt_wf released)
  l (LE: Time.le (released.(View.unwrap).(View.rlx) l) to) 
  (DISJ: forall (to2 from2 : Time.t) (msg2 : Message.t),
           Memory.get l to2 mem = Some (from2, msg2) ->
           Interval.disjoint (from, to) (from2, to2)) v :
  exists mem', 
    Memory.write Memory.bot mem l from to v 
                 released Memory.bot mem' Memory.op_kind_add .
Proof.
  exploit (@Memory.add_exists mem l from to v); try edone.
  intro M; desc; exists mem2.
  econs; eauto using Memory.remove_singleton.
  econs; try apply (memory_add_bot _ _ FROM); eauto.
Qed.

Lemma memory_exists_write 
  mem (CLOSED: Memory.closed mem)
  from to (FROM: Time.lt from to)
  tview (CWF: TView.wf tview)
  l (CUR_LE: Time.le (View.rlx (TView.cur tview) l) to)
  (DISJ: forall (to2 from2 : Time.t) (msg2 : Message.t),
           Memory.get l to2 mem = Some (from2, msg2) ->
           Interval.disjoint (from, to) (from2, to2)) 
  rel (REL_WF: View.opt_wf rel)
  (REL_LE: Time.le (View.rlx (View.unwrap rel) l) to) 
  v o sc_map :
  exists mem', 
    Memory.write Memory.bot mem l from to v 
                 (TView.write_released tview sc_map l to rel o)
                 Memory.bot mem' Memory.op_kind_add .
Proof.
  eapply memory_exists; eauto.
  by apply TViewFacts.write_future0; ss. 
  assert (YY: Time.le (View.rlx (TView.rel tview l) l) to).
    by etransitivity; [|exact CUR_LE]; apply CWF.
  unfold TView.write_released.
  ins; desf; ins; unfold TimeMap.join; ins; desf;
  unfold LocFun.add; desf; try congruence; ins;
  repeat apply Time.join_spec; eauto using Time.bot_spec;
  try rewrite tm_singleton; try reflexivity.
Qed.

Lemma ffrom_helper
  acts sb rmw rf mo sc
  acts0 sb0 rmw0 rf0 mo0 sc0
  a prev (GSTEP : gstep acts sb rmw rf mo sc acts0 sb0 rmw0 rf0 mo0 sc0 prev a)
  (COH' : Coherent acts0 sb0 rmw0 rf0 mo0 sc0)
  ffrom
  (COH : Coherent acts sb rmw rf mo sc)
  (BSPACE : forall y : event,
           In y acts ->
           is_write y ->
           is_proper y -> ~ (exists x : event, (rf;; rmw) x y) -> Time.bot <> ffrom y):
    forall y, mo0 a y ->
      (forall z, mo0 a z -> mo0 z y -> In z acts -> False) -> Time.bot <> ffrom y.
Proof.
  ins. 
  exploit mo_actb; try edone.
  by eapply COH'.
  exploit mo_domb; try edone.
  by eapply COH'.
  intros K K'; cdes GSTEP; desf; ins; desf.
  by cdes WF'; exfalso; eapply WF_MO; eauto.
  assert (P: is_proper y).
    by eapply no_mo_to_init; eauto.
  destruct (classic (exists x : event, (rf;; rmw) x y)) as [C|]; desc; eauto.
  assert (INx: In x acts).
    by eapply seq_doma in C; [|eapply rf_acta]; eauto. 
  assert (NEQ: x <> a) by congruence.
  eapply seq_mori in C; eauto using rf_mon, rmw_mon.
  assert (IMM': immediate mo0 x y).
    split; [by eapply rf_rmw_mo in C; eauto|].
    red in C; desc; intros; cdes COH'; eapply Cat;
     try exact C; try exact C0; eauto.
  clear C; destruct IMM' as [C IMM'].
  cdes WF'; cdes WF_MO. 
  exploit (MO_LOC a y); eauto; intro; desc.
  exploit (MO_LOC x y); eauto; intro; desf.
  eapply WF_MO in NEQ; splits; eauto 3 with acts.
  exfalso; des; eauto.
Qed. 

Lemma ax_op_sim_step_write :
  forall op_st ths G G' a l v o (LABa : lab a = Astore l v o)
   (GSTEP : gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) 
      (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
   (COH' : Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G')) 
   lang st st' (STATE : Language.step lang (ProgramEvent.write l v o) st st'),
  proof_obligation {|ts:=ths; exec:=G|} G' op_st (thread a) lang st st'.
Proof.
  red; ins; red in TIME; ins; desc.
  subst G0; destruct G, G'; simpl; ins.

  edestruct new_f with (dom := fun l x => In x acts0 /\ is_write x /\ loc x = Some l) 
                       (a:=a) (acts:=acts) (mo := mo0) (f_to := fto) (f_from:=ffrom)
    as (f_from' & L); desc;
    try eassumption;
    try (by cdes GSTEP; ins; apply WF'). 
    ins; cdes GSTEP; cdes WF'; cdes WF_MO.
    exploit MO_ACTa; eauto; exploit MO_DOMa; eauto.
    exploit MO_ACTb; eauto; exploit MO_DOMb; eauto.
    by exploit MO_LOC; eauto; ins; desf; eauto 10.
    by ins; desf.
    by cdes GSTEP; subst; intros; desf.
    by cdes GSTEP; red; ins; eapply MONOTONE, gstep_mo; eauto; congruence.
    {
      ins; eapply SPACE. 
        cdes GSTEP; eapply gstep_mo; eauto;
        by try intro; subst; cdes WF'; eapply WF_MO; eauto.
      unfold seq; intro; desc.  
      eapply rf_mon in H; eauto.
      eapply rmw_mon in H0; eauto.
      by cdes COH'; eapply Cat with (a:= x) (b:= a) (c := y); eauto. 
    }
    eby eapply ffrom_helper.
    by ins; desc; eapply sim_mem_lt; eauto.
    by ins; desc; eapply sim_mem_disj; eauto.

  assert (FROM: Time.lt (f_from' a) (f_to' a)).
    eapply TWF; eauto.
    cdes GSTEP; desf.
    splits; eauto using in_eq with acts.
    by destruct a as [??[]]; ins; desf.

  assert (exists mem', Memory.write Memory.bot
                        (Configuration.memory op_st) l (f_from' a) (f_to' a) v
                        (TView.write_released tview op_st.(Configuration.sc) l (f_to' a) None o)
                        Memory.bot mem' Memory.op_kind_add).
  {
    eapply memory_exists_write; try edone; ins; try by econs.
    by destruct WF_OP_ST.
    red in TVIEW; desc.
    red in CUR; desc.
    specialize (CUR_RW l). 
    red in CUR_RW; unfold LocFun.find in CUR_RW; desf.
    by rewrite MAX0; eauto using Time.bot_spec.
    etransitivity; try eapply LB'.
    rewrite <- F_TO, Time.le_lteq; eauto using acts_cur_rwr; left.
    destruct (classic (a_max = a)) as [|N]; subst.
      by exfalso; apply GSTEP; eauto using acts_cur_rwr.
      {
        assert (mo0 a_max a \/ mo0 a a_max); des; eauto.
          eapply GSTEP with (l:=l); cdes GSTEP; ins; subst.
            by splits; eauto using in_eq, in_cons, acts_cur_rwr with rel.
          by splits; eauto 3 using in_eq, in_cons, acts_cur_rwr with rel;
             destruct a as [??[]]; ins; desf.
        unfold t_cur, c_cur, dom_rel, seq, eqv_rel in INam; desc; subst. 
        exfalso; eapply (Coherent_rwr_sb COH'); eauto. 
          by eapply rwr_mon; eauto.
        eapply gstep_sb; eauto.
        unfold sb_ext, Relation_Operators.union, seq, eqv_rel; eauto.
        eauto_red 10 using rwr_actb.
      }
      {
        desf; specialize (SIM_MEM l); desc.
        destruct msg2; eapply SIMCELL in H; desf.
        rewrite <- F_TO, <- F_FROM; ins.
        cdes GSTEP; desf; simpls.
        eapply DJ'; eauto; splits; eauto; try congruence;
        destruct a as [??[]]; ins; desf.
      }
    by unfold TimeMap.bot; eapply Time.bot_spec.
  }

  desc; eexists _,_,_,mem',_,_,_; splits; eauto.
  - econs; [|eapply Local.step_write]; eauto.
    econstructor; eauto.
    + cdes GSTEP; desf; red in TVIEW; desc; eapply Writable_full; 
      eauto using TimeFacts.le_lt_lt, Time.bot_spec, in_eq.
    + esplits; ss. apply Memory.bot_nonsynch_loc.
  - exists f_from', f_to'; splits; try done.
    * eapply tview_step_write; eauto.
    * eapply sc_map_step_write; eauto.
    * eapply memory_step_write; eauto.
      destruct WF_OP_ST; done.
    * clear H.
      cdes GSTEP; ins; subst.
      exploit mo_acta; try exact MO; try eassumption.
      exploit mo_actb; try exact MO; try eassumption.
      ins; desf; subst.
        eby intro X; rewrite X in *; eapply Time.lt_strorder. 
        by eapply NADJ_R; eauto.
        by eapply NADJ_L; eauto.
      rewrite F_FROM, F_TO; ins. 
      eapply SPACE; eauto.
      eapply gstep_mo; eauto; try congruence.
      by intro X; apply NRMW, (gstep_rf_rmw COH GSTEP); vauto.
    * clear H; cdes GSTEP; subst; ins; desf. 
      rewrite F_FROM; ins.
      apply BSPACE; eauto; intro; desc; apply NRMW; eexists.
      eapply seq_mori; eauto using rf_mon, rmw_mon.
Qed.

Lemma ax_op_sim_step_update :
  forall op_st ths G G'
         a_r l v_r o_r (LABar : lab a_r = Aload l v_r o_r)
         a_w v_w o_w (LABaw : lab a_w = Astore l v_w o_w)
         G_mid
  (GSTEPr : gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) 
              (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid)  (mo G_mid) (sc G_mid) a_r a_r)
  (GSTEPw : gstep (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid) (mo G_mid) (sc G_mid) 
            (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a_r a_w)
  (COHmid : Coherent (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid) (mo G_mid) (sc G_mid))
  (COH' : Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
   lang st st'
   (STATE : Language.step lang (ProgramEvent.update l v_r v_w o_r o_w) st st'),
  proof_obligation {|ts:=ths; exec:=G|} G' op_st (thread a_r) lang st st'.
Proof.
  red; ins; red in TIME; ins; desc.
  subst G0; destruct G, G', G_mid; simpl; ins.
  generalize (gstep_read_rf COH GSTEPr LABar); intro; desc.
  assert (E: exists rel, Memory.get l (fto b) (Configuration.memory op_st) = 
          Some (ffrom b, Message.mk v_r rel) /\ 
          sim_mem_helper fto acts sb rmw rf sc b (ffrom b) v_r rel.(View.unwrap)).
    by cdes COH; cdes WF; eapply sim_mem_get; eauto with acts; destruct b as [??[]]; ins; desf.
  desc; red in E0; desc; clear FROM.
  assert (WRITE_B: is_write b). 
    unfold is_write; destruct (lab b); ins.
  assert (LOC_B: Gevents.loc b = Some l). 
    unfold Gevents.loc; destruct (lab b); ins; desf.
  assert (INb1: In b acts1).
    by cdes GSTEPr; vauto.
  assert (INb0: In b acts0).
    by cdes GSTEPw; vauto.
  assert (SAME_THREAD: (thread a_w) = (thread a_r)).
    by cdes GSTEPw; red in RMW_STEP; desf; congruence.
  assert (RMW: rmw0 a_r a_w).
    eapply gstep_rmw; try edone.
    right; splits; try done.
    by intro; subst; destruct a_w as [??[]]; ins; desf.
    by destruct a_w as [??[]]; ins; desf.
  assert (INw: In a_w acts0).
    by cdes GSTEPw; vauto.
  assert (WRITEw: is_write a_w).
    by destruct a_w as [??[]]; ins.
  assert (LOCw: loc a_w = Some l).
    by destruct a_w as [??[]]; ins; desf.
  assert (NEQb: a_w <> b).
    by intro; subst; cdes GSTEPw; eapply FRESH; eauto.
  assert (MOb: mo0 b a_w).
    eapply wf_mo_tot with (acts:=acts0); eauto.
    by eapply COH'.
    ins; desf; ins; eauto.
    eby intro; eapply BasicRMW with (acts:=acts0); eauto; eapply rf_mon.
  assert (MONOTONEw : monotone mo1 fto).
    red; ins; eapply MONOTONE, gstep_mo; eauto.
    by eapply mo_doma in H; eauto; intro; subst; eauto; destruct a_r as [??[]]; ins; desf.
    by eapply mo_domb in H; eauto; intro; subst; eauto; destruct a_r as [??[]]; ins; desf.
  assert (SIM_SC_MAPw: forall l, max_value fto (S_tm acts1 sb1 rmw1 rf1 l)
                 (LocFun.find l (Configuration.sc op_st))).
    ins; eapply max_value_same_set; try edone.
    by ins; rewrite gstep_S_tm_other; eauto with acts.
  assert (SIM_MEMw : sim_mem ffrom fto acts1 sb1 rmw1 rf1 sc1 (Configuration.memory op_st)).
    by eapply memory_step_nonwrite with (acts := acts) (acts0 := acts1); eauto with acts.
  assert (SPACEw : forall x y : event, mo1 x y -> ~ (rf1;; rmw1) x y -> fto x <> ffrom y).
    ins; eapply SPACE.
    eapply gstep_mo; eauto; intro; subst;
      [eapply mo_doma in H|eapply mo_domb in H]; 
      eauto; destruct a_r as [??[]]; ins.
    intro X; apply (gstep_rf_rmw_nonwrite COH GSTEPr) in X; eauto;
    by destruct a_r as [??[]].
  assert (BSPACEw : forall y : event,
           In y acts1 ->
           is_write y ->
           is_proper y -> ~ (exists x : event, (rf1;; rmw1) x y) -> Time.bot <> ffrom y).
    cdes GSTEPr; subst; ins; destruct H; subst.
    by destruct y as [??[]].
    apply BSPACE; eauto; intro; desc; apply H2; eexists.
    by eapply seq_mori; eauto using rf_mon, rmw_mon.
  assert (TVIEWw: sim_tview fto acts1 sb1 rmw1 rf1 sc1 
    (TView.read_tview tview l (fto b) rel o_r) (thread a_r)).
    by eapply tview_step_read with (acts := acts) (acts0 := acts1); eauto.

  edestruct new_f with (dom := fun l x => In x acts0 /\ is_write x /\ loc x = Some l) 
                       (a:=a_w) (acts:=acts1) (mo := mo0) (f_to := fto) (f_from:=ffrom)
    as (f_from' & L); desc;
    try eassumption;
    try (by cdes GSTEPw; ins; apply WF'). 
    ins; cdes GSTEPw; cdes WF'; cdes WF_MO.
    exploit MO_ACTa; eauto; exploit MO_DOMa; eauto.
    exploit MO_ACTb; eauto; exploit MO_DOMb; eauto.
    by exploit MO_LOC; eauto; ins; desf; eauto 10.
    by ins; desf.
    by cdes GSTEPw; subst; intros; desf.
    by cdes GSTEPw; red; ins; eapply MONOTONEw, gstep_mo; eauto; congruence.
    {
      ins; eapply SPACEw. 
      cdes GSTEPw; eapply gstep_mo; eauto;
        by try intro; subst; cdes WF'; eapply WF_MO; eauto.
      unfold seq; intro; desc.  
      eapply rf_mon in H; eauto.
      eapply rmw_mon in H0; eauto.
      by cdes COH'; eapply Cat with (a:= x) (b:= a_w) (c := y); eauto. 
    }
    eby eapply ffrom_helper.
    by ins; desc; eapply sim_mem_lt; eauto.
    by ins; desc; eapply sim_mem_disj; eauto.

  assert (LT: Time.lt (fto b) (f_to' a_w)).
    by rewrite <- F_TO; try by cdes GSTEPr; subst; ins; auto.

  assert (exists mem', Memory.write Memory.bot
                    (Configuration.memory op_st) l (fto b) (f_to' a_w) v_w
                    (TView.write_released 
  (TView.read_tview tview l (fto b) rel o_r)
   op_st.(Configuration.sc) l (f_to' a_w) rel o_w)
                    Memory.bot mem' Memory.op_kind_add).
     {
      eapply memory_exists_write; try edone; ins.
  - by destruct WF_OP_ST.
  - eapply TViewFacts.read_future1; eauto; eby eapply WF_OP_ST.
  - red in TVIEWw; desc.
    red in CUR; desc.
    specialize (CUR_RW l). 
    unfold TView.read_tview in *; ins.
    red in CUR_RW; unfold LocFun.find in CUR_RW. 
    desc. destruct MAX as [MAX|MAX0]; desc.
    by rewrite MAX0; eauto using Time.bot_spec.
    etransitivity; try eapply LB'.
    rewrite <- F_TO, Time.le_lteq; eauto using acts_cur_rwr; left.
    destruct (classic (a_max = a_w)) as [|N]; subst.
    by exfalso; apply GSTEPw; eauto 3 using acts_cur_rwr.
    {
      assert (mo0 a_max a_w \/ mo0 a_w a_max); des; eauto.
      eapply GSTEPw with (l:=l); cdes GSTEPw; ins; subst.
      by splits; eauto using in_eq, in_cons, acts_cur_rwr with rel.
      unfold t_cur, c_cur, dom_rel, seq, eqv_rel in INam; desc; subst. 
      exfalso; eapply (Coherent_rwr_sb COH'); eauto. 
      by eapply rwr_mon; eauto.
      eapply gstep_sb with (acts:=acts1); eauto.
      unfold sb_ext, Relation_Operators.union, seq, eqv_rel; eauto.
      rewrite <- SAME_THREAD in INam1.
      eauto_red 10 using rwr_actb.
    } 
  - intro; ins; destruct LHS, RHS; ins.
    desf; specialize (SIM_MEMw l); desc.
    destruct msg2; eapply SIMCELL in H; desf.
    destruct (TimeFacts.le_lt_dec (f_to' b0) (f_to' a_w)).
    * cdes COH'.
      eapply Cat with (a:=b) (b:=b0) (c:=a_w); eauto.
      eapply wf_mo_tot with (acts:=acts0); eauto 2.
      by eapply COH'.
      by cdes GSTEPw; vauto.
      intro A; apply MON' in A.
      eapply Time.lt_strorder, Time.lt_strorder; eauto.
      rewrite !F_TO; eauto.
      eapply TimeFacts.lt_le_lt; eauto.
      intro; subst.
      eby clear -FROM TO0; eapply Time.lt_strorder, TimeFacts.lt_le_lt.
      eapply wf_mo_tot with (acts:=acts0); eauto 2.
      by eapply COH'.
      by cdes GSTEPw; vauto.
      intro A; apply MON' in A.
      eapply Time.lt_strorder, TimeFacts.lt_le_lt; eauto.
      by intro; subst; cdes GSTEPw; vauto.
      eby eapply rf_mon.
    * eapply DJ' with (x:=a_w) (y:=b0); splits; eauto.
      by intro; subst; cdes GSTEPw; vauto.
      by cdes GSTEPw; vauto.
      econs; ins; try eby right.
      by eapply TWF; splits; eauto 2.
      econs; ins; try by left.
      rewrite F_FROM; try done.
      eapply TimeFacts.lt_le_lt; eauto.
  - eby eapply WF_OP_ST.
  - red in SIMMSG; desc.
    specialize (RW l).
    red in RW; desf.
    by unfold LocFun.find in MAX0; rewrite MAX0; eauto using Time.bot_spec.
    unfold LocFun.find in LB'.
    destruct (classic (a_max = b)); subst; left; eapply TimeFacts.le_lt_lt; try edone.
    rewrite <- F_TO.
    2: by eapply acta_msg_rwr in INam; cdes GSTEPr; cdes COH; vauto.
    eapply MON'.
    cdes COH'; cdes WF; eapply WF_MO; try edone.
    eapply mo_mon; try edone; eapply mo_mon; try edone.
    eapply wf_mo_tot with (acts:=acts); eauto.
    by cdes COH; eapply WF0.
    by eapply acta_msg_rwr in INam; cdes GSTEPr; cdes COH; vauto.
    eby eapply msg_rel_rwr_doma1.
    eby eapply msg_rel_rwr_doma2.
    unfold msg_rel, m_rel, seq in *; desc.
    by intro; eapply Coherent_rwr_rel; try edone.
  }

    desc; eexists _,_,_,mem',_,_,_; splits; eauto.
    - econs; [|eapply Local.step_update]; eauto.
      * econstructor; eauto.
        red in TVIEW; red in SIMMSG; desc.
        eapply Readable_full with (acts':=acts1) ;eauto. 
      * econstructor; eauto.
        + cdes GSTEPw; desf; red in TVIEW; desc; eapply Writable_full; 
            eauto using TimeFacts.le_lt_lt, Time.bot_spec, in_eq.
          by rewrite SAME_THREAD; eapply TVIEWw.
        + by esplits; ss; apply Memory.bot_nonsynch_loc.
    - exists (upd ffrom a_w (fto b)), f_to'; splits; try done.
    * ins; rewrite updo; try done.
      by intro; subst; cdes GSTEPw; eapply FRESH; cdes GSTEPr; vauto.
    * ins; eapply F_TO; cdes GSTEPr; rewrite ACT_STEP in *; ins; auto.
    * rewrite <- SAME_THREAD.
      eapply tview_step_write with (acts:=acts1); eauto.
      by rewrite SAME_THREAD.
    * eapply sc_map_step_write with (acts:=acts1); eauto.
    * eapply memory_step_update with (acts:=acts1); eauto; try rewrite upds; try done.
      + ins; rewrite updo; try done.
        eby intro; subst; cdes GSTEPw; eapply FRESH.
      + by destruct WF_OP_ST.
      + eby rewrite SAME_THREAD.
      + red in SIM_MEMw; desc.
        specialize (SIM_MEMw l); desc.
        specialize (SIMCELL (fto b) (ffrom b) v_r rel E); desc.
        red in SIMCELL4; desc.
        assert (b=b0); subst; try done.
        eapply monotone_injective with (acts:= acts1) (f:= fto); try edone.
        by eapply COHmid.
   * clear H.
     cdes GSTEPw; ins; subst.
     exploit mo_acta; try exact MO; try eassumption.
     exploit mo_actb; try exact MO; try eassumption.
     ins; desf; subst; try rewrite upds.
     + eby exfalso; cdes WF'; eapply WF_MO.
     + rewrite updo; try by intro; subst; auto.
       rewrite <- F_FROM; try done.
       eby intro X; eapply NADJ_R.
     + rewrite F_TO; try done.
       intro X; eapply monotone_injective in X; eauto 2 with acts.
       subst.
       apply NRMW.
       exists a_r; splits; eauto.
       eby eapply rf_mon.
       by eapply mo_doma; eauto.
       by clear LOC_B; erewrite loceq_mo; eauto; destruct y as [??[]]; ins; desf.
       by eapply COHmid.
     + rewrite updo.
       rewrite F_TO; try done.
       eapply SPACEw; eauto.
       eapply gstep_mo; eauto; try congruence.
       by intro X; apply NRMW, (gstep_rf_rmw COHmid GSTEPw); vauto.
       by intro; subst; cdes GSTEPw; auto.
   * clear H; cdes GSTEPw; subst; ins; desf.
      + exfalso; apply NRMW.
        exists b, a_r; splits; eauto.
        eby eapply rf_mon.
    + rewrite updo.
      apply BSPACEw; eauto; intro; desc; apply NRMW; eexists.
      eapply seq_mori; eauto using rf_mon, rmw_mon.
      intro; subst; auto.
Qed.

Lemma ax_op_sim_step_fence :
  forall op_st ths G G'
         a o_r o_w (LABa : lab a = Afence o_r o_w)
   (GSTEP : gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) 
            (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
   (COH' : Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G')) 
   lang st st'
   (STATE : Language.step lang (ProgramEvent.fence o_r o_w) st st'),
  proof_obligation {|ts:=ths; exec:=G|} G' op_st (thread a) lang st st'.
Proof.
  ins; red; ins; red in TIME; ins; desc.
  subst G0; destruct G, G'; simpl; ins.
  eexists _,_,_,_,_,_,_; splits; eauto.
  econs; [|eapply Local.step_fence]; eauto.
  econstructor; eauto.
  { i. apply Memory.bot_nonsynch. }
  exists ffrom, fto; splits; eauto.
  * rewrite <- gstep_non_write_mo; eauto with acts.
  * destruct (classic (is_sc a)); 
      [ eapply tview_step_scfence|eapply tview_step_rafence]; eauto.
  * eby eapply sc_map_step_fence.
  * by eapply memory_step_nonwrite; eauto with acts.
  * ins; eapply SPACE.
      by eapply gstep_mo; eauto; intro; subst; 
         [eapply mo_doma in MO|eapply mo_domb in MO]; 
         eauto; destruct a as [??[]].
    intro X; apply (gstep_rf_rmw_nonwrite COH GSTEP) in X; eauto;
    by destruct a as [??[]].
  * cdes GSTEP; subst; ins; desf; [by destruct y as [??[]]|].
    apply BSPACE; eauto; intro; desc; apply NRMW; eexists.
    eapply seq_mori; eauto using rf_mon, rmw_mon.
Qed.

Lemma ax_op_sim_step_syscall :
  forall op_st ths G G'
         a (LABa : lab a = Afence Ordering.seqcst Ordering.seqcst)
   (GSTEP : gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G) 
            (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
   (COH' : Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G')) 
   lang st st' ee
   (STATE : Language.step lang (ProgramEvent.syscall ee) st st'),
  proof_obligation {|ts:=ths; exec:=G|} G' op_st (thread a) lang st st'.
Proof.
  ins; red; ins; red in TIME; ins; desc.
  subst G0; destruct G, G'; simpl; ins.
  eexists _,_,_,_,_,_,_; splits; eauto.
  econs; [|eapply Local.step_syscall]; eauto.
  econstructor; eauto.
  { i. apply Memory.bot_nonsynch. }
  exists ffrom, fto; splits; eauto.
  * rewrite <- gstep_non_write_mo; eauto with acts.
  * eapply tview_step_scfence; eauto; red; ins; desf.
  * eby eapply sc_map_step_fence.
  * by eapply memory_step_nonwrite; eauto with acts.
  * ins; eapply SPACE.
      by eapply gstep_mo; eauto; intro; subst; 
         [eapply mo_doma in MO|eapply mo_domb in MO]; 
         eauto; destruct a as [??[]].
    intro X; apply (gstep_rf_rmw_nonwrite COH GSTEP) in X; eauto;
    by destruct a as [??[]].
  * cdes GSTEP; subst; ins; desf; [by destruct y as [??[]]|].
    apply BSPACE; eauto; intro; desc; apply NRMW; eexists.
    eapply seq_mori; eauto using rf_mon, rmw_mon.
Qed.

Lemma ax_op_sim :
  forall op_st ax_st (SIM: MGsim op_st ax_st) ax_st' (AXSTEP: step ax_st ax_st'),
  exists e tid op_st', Configuration.step e tid op_st op_st' /\ MGsim op_st' ax_st'.
Proof.
  ins; red in SIM; desc.
  destruct AXSTEP.

  rewrite STATES in TID.
  apply find_mapD in TID; desc; destruct z as [? local]; ins; desf.
  destruct local as [tview promises].
  assert (TID' := TID).
  apply NO_PROMISES in TID'; ins; subst.

  cut (proof_obligation ax_st (exec ax_st') op_st (Some i) lang st st').
  {
    intro X; exploit X; eauto; clear X; ins; desc.
       by eapply TIME; eauto.
       by destruct WF_OP_ST; destruct WF; eapply THREADS; eauto.
    eexists _,i,_.
    apply foo; [|intro CSTEP].
  -  econstructor; try edone; try apply Thread.step_program; eauto.
     red; ins; eexists; splits; eauto; simpl; desf.
  - red; simpl; splits; eauto.
    * destruct MSTEP; eauto.
      by rewrite SAME_EXEC.
    * eapply Configuration.step_future; eauto.
      eby eapply no_promises_consistent.
    * intro; rewrite IdentMap.gsspec. ins; desf; simpl; eapply NO_PROMISES; eauto.
    * by rewrite IdentMap.map_add; simpl; rewrite MTS, STATES.
    * red in TIME; desc; exists ffrom', fto'; splits; eauto.
      red; simpl; splits; eauto; ins.
      clear CSTEP.
      rewrite IdentMap.gsspec in TID0; desf; ins; simpl.
      destruct MSTEP; subst.
      by desf; rewrite SAME_EXEC; eapply sim_tview_other_threads_silent; eauto. 
      all: eapply sim_tview_other_threads; eauto 2. 
      all: try eapply sim_tview_other_threads; eauto 2.
      all: try intro; subst; eauto. 
      all: congruence. 
   }
  clear f_from f_to TIME SPACE BSPACE.

  destruct MSTEP; ins; subst.
  { (** SILENT **)
    destruct ax_st, ax_st'; ins; desf.
    red; ins; eexists _,_,_,_,_,_,_.
    splits; eauto.
    econs; [|econs 1]; eauto.
    red in TIME; ins; desc; subst.
    exists ffrom, fto; splits; eauto.
  }
  all: try rewrite <- TIDa; try rewrite <- TIDar; try rewrite <- TIDaw.
  by eapply ax_op_sim_step_read; eauto.
  by eapply ax_op_sim_step_write; eauto.
  by eapply ax_op_sim_step_update; eauto.
  by eapply ax_op_sim_step_fence; eauto.
  by eapply ax_op_sim_step_syscall; eauto.
Qed.


