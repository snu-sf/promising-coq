(******************************************************************************)
(** * Simulation relation between axiomatic and operational machines *)
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
Require Import Commit.

Require Import Gevents.
Require Import model.
Require Import Gstep.
Require Import Machine.

Set Implicit Arguments.
Remove Hints plus_n_O.

Hint Resolve gstep_wf gstep_inc coh_wf.

Section Monotone.

Definition monotone (mo : event -> event -> Prop) f :=
  forall a b, mo a b -> Time.lt (f a) (f b).

Lemma new_f acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  prev a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' prev a)
  f (MON: monotone mo f): 
  exists f', << F: forall b, In b acts -> f' b = f b >> /\
             << MON: monotone mo' f' >> /\
             << N_ZERO: Time.lt Time.bot (f' a) >>.
Admitted.

Lemma new_from (f: event -> Time.t) a: 
  exists from, Time.lt from (f a) /\ forall b, Time.lt (f b) (f a) -> Time.lt (f b) from.
(* add finiteness assumption ?*)
Admitted. 

Lemma monotone_converse a b l f acts mo
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (MON: monotone mo f)
  (WF_MO: WfMO acts mo) (NOMO: ~ mo b a): Time.le (f a) (f b).
Proof.
apply Time.le_lteq.
destruct (classic (a=b)) as [|N]; desf; eauto.
eapply WF_MO in N; desf; eauto.
Qed.

Lemma monotone_converse_strict a b l f acts mo
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (MON: monotone mo f)
  (WF_MO: WfMO acts mo) (NOMO: ~ mo b a) (NEQ: a <> b) : Time.lt (f a) (f b).
Proof.
assert (mo a b).
  eapply wf_mo_tot; eauto.
apply MON; done.
Qed.

Lemma monotone_injective a b l f acts mo
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (MON: monotone mo f)
  (WF_MO: WfMO acts mo) (SAME_F: f a = f b) (NEQ: a <> b): False.
Proof.
eapply WF_MO in NEQ; eauto.
desf; apply MON in NEQ; rewrite SAME_F in NEQ; eapply Time.lt_strorder; eauto.
Qed.

Definition max_value f (INR : event -> Prop) val :=
 << UB: forall a (INa: INR a), Time.le (f a) val >> /\
 << MAX: ((forall a, ~ INR a) /\ val = Time.bot) \/
         (exists a_max, << INam: INR a_max >> /\ <<LB': Time.le val (f a_max)>>) >>.

End Monotone.

Require Import Setoid Permutation.

Add Parametric Morphism : (monotone) with signature 
  same_relation ==> eq ==> iff as monotone_more.
Proof.
  unfold monotone, same_relation, NW; intuition; eauto. 
Qed.

Section Simulation.

Variable f : event -> Time.t.

Variable acts : list event.  
Variable sb : event -> event -> Prop. 
Variable rmw : event -> event -> Prop. 
Variable rf : event -> event -> Prop. 
Variable mo : event -> event -> Prop. 
Variable sc : event -> event -> Prop. 

Definition sim_msg b  rel :=
  << UR: forall l, max_value f (fun a => msg_rel urr acts sb rmw rf sc l a b) (LocFun.find l rel.(Capability.ur)) >> /\
  << RW: forall l, max_value f (fun a => msg_rel rwr acts sb rmw rf sc l a b) (LocFun.find l rel.(Capability.rw)) >> /\
  << SC: forall l, max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) (LocFun.find l rel.(Capability.sc)) >>.

Definition sim_mem_helper b from v rel :=
  << VAL: Some v = (val b) >> /\
  << FROM: Time.lt from (f b) >> /\ 
(*   << FROMRMW: (forall a (RFRMW: (rf ;; rmw) a b), from = f a) >> /\ *)
  << SIMMSG: sim_msg b rel >>.

Definition sim_mem mem:=
  forall l, 
    << DOM: forall b, (In b acts) /\ (is_write b) /\ (loc b = Some l) -> 
                Memory.get l (f b) mem <> None >> /\
    << SIMCELL: forall to from v rel 
                (CELL: Memory.get l to mem = Some (from, (Message.mk v rel))),
                exists b, (In b acts) /\ (is_write b) /\ (loc b = Some l) /\ (f b = to) /\
                (sim_mem_helper b from v rel) >> /\
    << UPDATES: forall a b (RF_RMW: (rf ;; rmw) a b) (LOC: loc a = Some l),
                exists m, Memory.get l (f b) mem = Some ((f a), m) >>.

Definition sim_rel rel i :=
  << REL_UR: forall l' l, max_value f (t_rel urr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.ur)) >> /\
  << REL_UR: forall l' l, max_value f (t_rel rwr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.rw)) >> /\
  << REL_UR: forall l' l, max_value f (t_rel scr acts sb rmw rf sc i l' l) 
    (LocFun.find l (LocFun.find l' rel).(Capability.sc)) >>.

Definition sim_cur cur i :=
  << CUR_UR: forall l, max_value f (t_cur urr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.ur)) >> /\
  << CUR_RW: forall l, max_value f (t_cur rwr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.rw)) >> /\
  << CUR_SC: forall l, max_value f (t_cur scr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(Capability.sc)) >>.

Definition sim_acq acq i :=
  << ACQ_UR: forall l, max_value f (t_acq urr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.ur)) >> /\
  << ACQ_RW: forall l, max_value f (t_acq rwr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.rw)) >> /\
  << ACQ_SC: forall l, max_value f (t_acq scr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(Capability.sc)) >>.

Definition sim_commit commit i :=
  << CUR: sim_cur commit.(Commit.cur) i >> /\
  << ACQ: sim_acq commit.(Commit.acq) i >> /\
  << REL: sim_rel commit.(Commit.rel) i >>.

End Simulation.

Definition sim_time  (op_st: Configuration.t) (ax_st: Machine.configuration) f :=
  << MONOTONE: monotone (mo ax_st) f >> /\  
  << SIM_COMMIT: forall i foo local
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
        sim_commit f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) 
                   local.(Local.commit) (Some i) >> /\
  << SIM_SC_MAP: forall l, max_value f (S_tm (acts ax_st) (sb ax_st) (rmw ax_st) 
                                             (rf ax_st) l) 
                                     (LocFun.find l (Configuration.sc op_st))  >> /\
  << SIM_MEM: sim_mem f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) 
                      (Configuration.memory op_st) >>.

Definition sim (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << COH: Coherent (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (mo ax_st) (sc ax_st) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << CONS_OP_ST: Configuration.consistent op_st >> /\
  << NO_PROMISES: forall i foo local 
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: ts ax_st = IdentMap.map fst (Configuration.threads op_st) >> /\
  exists f, << TIME : sim_time op_st ax_st f >>. 

Lemma find_mapD A B tid (f: A -> B) x y :
  IdentMap.find tid (IdentMap.map f x) = Some y ->
  exists z, IdentMap.find tid x = Some z /\ y = f z.
Proof.
  rewrite IdentMap.Facts.map_o; unfold option_map; ins; desf; eauto.
Qed.

Lemma tm_join a b l :
  TimeMap.join a b l =  Time.join (a l) (b l).
Proof.  ins. Qed.

Lemma tm_find_join l a b :
  LocFun.find l (TimeMap.join a b) = 
  Time.join (LocFun.find l a) (LocFun.find l b).
Proof.  done. Qed.

Lemma tm_find_singleton l l' t  :
  LocFun.find l (TimeMap.singleton l' t) = 
    if (Loc.eq_dec l l') then t else Time.bot.
Proof.  desf. Qed.

Lemma tm_singleton l t : TimeMap.singleton l t l = t.
Proof.  apply Loc.eq_dec_eq; done. Qed.

Lemma time_join_bot a : Time.join a Time.bot =  a.
Proof.
Admitted.

Lemma tm_find_bot l : LocFun.find l TimeMap.bot = Time.bot.
Proof. done. Qed.

Lemma tm_join_bot a  :
  TimeMap.join a TimeMap.bot =  a.
Proof.
eapply TimeMap.antisym.
apply TimeMap.join_spec.
apply TimeMap.le_PreOrder.
apply TimeMap.bot_spec.
apply TimeMap.join_l.
Qed.

Lemma cap_join_bot a  :
  Capability.join a Capability.bot =  a.
Proof.
eapply Capability.antisym.
apply Capability.join_spec.
apply Capability.le_PreOrder.
apply Capability.bot_spec.
apply Capability.join_l.
Qed.

Lemma max_value_singleton f b t (T: t = f b):
  max_value f (eq b) t.
Proof.
red; splits; ins; desc; subst.
by apply Time.le_lteq; eauto.
right; exists b; splits; try apply Time.le_lteq; eauto.
Qed.

Lemma max_value_new_f f f' P t 
  (MAX: max_value f P t) (F: forall x, P x -> f' x = f x):
  max_value f' P t.
Proof.
unfold max_value in *; ins; desf; splits; ins.
all: try rewrite F; auto.
right; exists a_max; rewrite F; auto.
Qed.

Lemma max_value_same_set f P P' t 
  (MAX: max_value f P t) (SAME: forall x, P' x <-> P x):   
  max_value f P' t.
Proof.
  unfold max_value in *; ins; desf; splits; ins.
  all: try specialize (SAME a); desf; eauto.
  left; split; eauto; ins; intro;  eapply MAX0; apply SAME; edone.
  right; exists a_max; specialize (SAME a_max); desf; split; auto.
Qed.

Lemma max_value_join f P P' P'' t t'
  (MAX: max_value f P t) (MAX':  max_value f P' t')
  (SAME: forall x, P'' x <-> P x \/ P' x):
  max_value f P'' (Time.join t t').
Proof.
unfold max_value in *; ins; desf; splits; ins.
all: try apply SAME in INa; desf.
all: try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- left; split; eauto. ins; intro. 
  specialize (MAX1 a). specialize (MAX0 a).
  apply SAME in H; desf.
- right; exists a_max; splits.
  rewrite SAME; eauto.
  apply Time.join_spec; eauto; etransitivity; eauto; rewrite Time.le_lteq; eauto.
  apply Time.le_lteq. apply Time.bot_spec.
- right; exists a_max; splits.
  rewrite SAME; eauto.
  apply Time.join_spec; eauto; etransitivity; eauto; rewrite Time.le_lteq; eauto.
  apply Time.le_lteq. apply Time.bot_spec.
- right;
  destruct (Time.le_lt_dec (f a_max) (f a_max0)); [exists a_max0|exists a_max]; splits.
  all: try rewrite SAME; eauto.
  all: try (apply Time.join_spec; eauto;
       etransitivity; eauto; rewrite Time.le_lteq; eauto). 
Qed.

Lemma max_value_loc f f' P P' t b
  (MAX: max_value f P t)
  (SAME: forall x, P' x <-> P x \/ x = b)
  (F: forall x, P x -> f' x = f x):
  max_value f' P'  (Time.join t (f' b)).
Proof.
eapply max_value_join with (P':= eq b); eauto.
eapply max_value_new_f with (f:=f); eauto.
eapply max_value_singleton; done.
ins; specialize (SAME x); desf; split; ins.
apply SAME in H; desf; eauto.
apply SAME0; desf; eauto.
Qed.

Lemma max_value_empty f P (SAME: forall x, ~ P x):
  max_value f P Time.bot.
Proof.
red; splits.
ins; exfalso; eapply SAME; edone.
left; splits; eauto.
Qed.
