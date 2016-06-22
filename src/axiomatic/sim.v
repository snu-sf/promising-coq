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
Require Import Memory.
Require Import Thread.
Require Import Commit.

Require Import Gevents.
Require Import model.
Require Import Gsteps.
Require Import Machine.

Set Implicit Arguments.
Remove Hints plus_n_O.

Hint Resolve gstep_coh gstep_inc coh_wf.


Section Simulation.

Variable f : event -> Time.t.

Variable acts : list event.  
Variable sb : event -> event -> Prop. 
Variable rmw : event -> event -> Prop. 
Variable rf : event -> event -> Prop. 
Variable mo : event -> event -> Prop. 
Variable sc : event -> event -> Prop. 

Definition f_equal_max (INR : event -> Prop) val :=
 << UB: forall a (INa: INR a), Time.le (f a) val >> /\
 exists a_max, << INa: INR a_max >> /\ <<LB': Time.le val (f a_max)>>.
 
Definition valid :=
  forall a b, mo a b -> Time.lt (f a) (f b).

Lemma valid_converse a b l 
  (INa: In a acts) (INb: In b acts) (WRITEa: is_write a) (WRITEb: is_write b)
  (LOCa: loc a = Some l) (LOCb: loc b = Some l) (VALID: valid)
  (TOT_MO: forall l, is_total (fun a => (In a acts) /\ is_write a /\ loc a = Some l) mo)
  (NOMO: ~ mo b a): Time.le (f a) (f b).
Proof.
apply Time.le_lteq.
destruct (classic (a=b)) as [|N]; desf; eauto.
eapply TOT_MO in N; desf; eauto.
Qed.

Definition sim_msg (m: Message.t) b:=
  << VAL: Some m.(Message.val) = (val b) >> /\
  << UR: forall y, f_equal_max (fun a => (m_rel_ur acts sb rmw rf sc y a b)) ((m.(Message.released)).(Capability.ur) y) >> /\
  << RW: forall y, f_equal_max (fun a => (m_rel_rw acts sb rmw rf sc y a b)) ((m.(Message.released)).(Capability.rw) y) >> /\
  << SC: forall y, f_equal_max (fun a => (m_rel_sc acts sb rmw rf sc y a b)) ((m.(Message.released)).(Capability.sc) y) >>.

Definition sim_cell_helper b from msg :=
  << SIMMSG: sim_msg msg b >> /\ 
  << FROM: Time.lt from (f b) >> /\ 
  << FROMRMW: (forall a (RFRMW: (seq rf rmw) a b), from = f a) >>.

Definition sim_cell cell l  :=
  << DOM: forall b, is_write b /\ loc b = Some l <-> Cell.get (f b) cell <> None >> /\
  << SIMCELL: forall b (WRITE: is_write b) (LOC: loc b = Some l) 
                       from msg (CELL: Cell.get (f b) cell = Some (from, msg)),
                sim_cell_helper b from msg >>.

Definition sim_mem (mem: Memory.t) :=
  forall l, sim_cell (mem l) l.

Definition sim_cur cur i :=
  << CUR_UR: forall l, f_equal_max (c_cur_ur acts sb rmw rf sc i l) (cur.(Capability.ur) l) >> /\
  << CUR_RW: forall l, f_equal_max (c_cur_rw acts sb rmw rf sc i l) (cur.(Capability.rw) l) >> /\
  << CUR_SC: forall l, f_equal_max (c_cur_sc acts sb rmw rf sc i l) (cur.(Capability.sc) l) >>.

Definition sim_acq acq i :=
  << ACQ_UR: forall l, f_equal_max (c_acq_ur acts sb rmw rf sc i l) (acq.(Capability.ur) l) >> /\
  << ACQ_RW: forall l, f_equal_max (c_acq_rw acts sb rmw rf sc i l) (acq.(Capability.rw) l) >> /\
  << ACQ_SC: forall l, f_equal_max (c_acq_sc acts sb rmw rf sc i l) (acq.(Capability.sc) l) >>.

Definition sim_rel rel i :=
  << REL_UR: forall l' l, f_equal_max (c_rel_ur acts sb rmw rf sc i l' l) ((rel l').(Capability.ur) l) >> /\
  << REL_RW: forall l' l, f_equal_max (c_rel_rw acts sb rmw rf sc i l' l) ((rel l').(Capability.rw) l) >> /\
  << REL_SC: forall l' l, f_equal_max (c_rel_sc acts sb rmw rf sc i l' l) ((rel l').(Capability.sc) l) >>.

Definition sim_commit commit i :=
  << CUR: sim_cur commit.(Commit.cur) i >> /\
  << ACQ: sim_acq commit.(Commit.acq) i >> /\
  << REL: sim_rel commit.(Commit.rel) i >>.

Definition sim_local local i :=
  sim_commit local.(Local.commit) i.

End Simulation.

Require Import Setoid Permutation.

Add Parametric Morphism : (valid) with signature 
  eq ==> same_relation ==> iff as valid_more.
Proof.
  unfold valid, same_relation, NW; intuition; eauto. 
Qed.



Definition sim_f f (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << STATES: ts ax_st = IdentMap.map fst (Configuration.threads op_st) >> /\
  << LOCAL: forall i foo local 
                   (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
              sim_local f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) local i>> /\
  << SC: True  >> /\ (** TODO: SC map **)
  << MEM: sim_mem f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) op_st.(Configuration.memory) >>.

Definition sim (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << COH: Coherent (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (mo ax_st) (sc ax_st) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << CONS_OP_ST: Configuration.consistent op_st >> /\
  << NO_PROMISES: forall i foo local (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << TIME: exists f, << MONOTONE: valid f (mo ax_st) >> /\ 
                    << SIM: sim_f f op_st ax_st >>>>.

Lemma find_mapD A B tid (f: A -> B) x y :
  IdentMap.find tid (IdentMap.map f x) = Some y ->
  exists z, IdentMap.find tid x = Some z /\ y = f z.
Proof.
  rewrite IdentMap.Facts.map_o; unfold option_map; ins; desf; eauto.
Qed.

Lemma get_cell :
  forall f acts sb rmw rf sc mem 
    (MEM : sim_mem f acts sb rmw rf sc mem) a rf0 l v o
    (LAB' : lab a = Aload l v o) 
    (WF_RF : WfRF (a :: acts) rf0)
     b (RFba : rf0 b a) (INb : In b acts)
     o_b (Lb : lab b = Astore l v o_b),
  exists from rel,
    Cell.get (f b) (mem l) = Some (from, {| Message.val:=v; Message.released:=rel |}).
Proof.
  ins; desc.
  assert (X:= proj1 (MEM l) b).
  destruct (Cell.get (f b) (mem l)) as [[from [v' rel]]|] eqn:Y; cycle 1.
  - exfalso; apply X; try done.
    unfold is_write, loc; rewrite Lb in *; done.
  - assert (v'=v).
      apply (proj2 (MEM l)) in Y; try (unfold is_write, loc; rewrite Lb in *; done).
      red in Y; desc; red in SIMMSG; desc; ins.
      unfold val in *; rewrite Lb in *; ins; congruence.
  subst.
  eauto; reflexivity.
Qed.



(* 
 Lemma ur_join_if cond a b :
  Capability.ur (Capability.join_if cond a b) =
  TimeMap.join_if cond (Capability.ur a) (Capability.ur b).
Proof.
  destruct cond; ins.
Qed.


Lemma le_join_if1 x (cond: bool) a b :
  cond -> Time.le x a ->
  Time.le x (Time.join_if cond a b).
Proof.
ins; unfold Time.join_if; desf.
apply transitivity with (y:=a); try done.
apply Time.join_l.
Qed.

Lemma le_join_if2 x cond a b :
  Time.le x b ->
  Time.le x (Time.join_if cond a b).
Proof.
ins; unfold Time.join_if; desf.
apply transitivity with (y:=b); try done.
apply Time.join_r.
Qed. *)

Lemma tm_join a b l :
  TimeMap.join a b l =  Time.join (a l) (b l).
Proof.  ins. Qed.

Lemma tm_singleton l t  :
  TimeMap.singleton l t l = t.
Proof.
Admitted.

Lemma tm_singleton2 l l' t (NEQ: l <> l') :
  TimeMap.singleton l t l' = Time.bot.
Proof.
Admitted.


Lemma tm_join_singleton_to_if t1 t2 l l' :
  Time.join t1 (TimeMap.singleton l t2 l') = 
  Time.join t1 (if (Loc.eq_dec l l') then t2 else Time.bot).
Proof.
desf; [by rewrite tm_singleton|by rewrite tm_singleton2].
Qed.

Lemma tm_join_bot a  :
  TimeMap.join a TimeMap.bot =  a.
Proof.
Admitted.

Lemma f_equal_max_singleton f b :
  f_equal_max f (fun a => a = b) (f b).
Proof.
red; splits; ins; desc; subst.
by apply Time.le_lteq; eauto.
exists b; splits; try apply Time.le_lteq; eauto.
Qed.

Lemma f_equal_max_join f rel cap rel' cap' rel'' :
  f_equal_max f rel cap ->
  f_equal_max f rel' cap' ->
  (forall x, rel'' x <-> rel x \/ rel' x) ->
  f_equal_max f rel'' (Time.join cap cap').
Proof.
  unfold f_equal_max; ins; desf; splits; ins.
  rewrite H1 in *; desf; etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
  destruct (Time.le_lt_dec (f a_max) (f a_max0));
    [exists a_max0|exists a_max]; rewrite H1; split; eauto;
    apply Time.join_spec; eauto;
  etransitivity; eauto; rewrite Time.le_lteq; eauto.
Qed.


Lemma f_equal_max_join_if f P t P' t' (cond : bool) P'' :
  f_equal_max f P t ->
  f_equal_max f P' t' ->
  (forall x, P'' x <-> P x \/ P' x /\ cond) ->
  f_equal_max f P'' (Time.join t (if cond then t' else Time.bot)).
Proof.
unfold f_equal_max; ins; desf; splits; ins.
- rewrite H1 in *; desf; etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- destruct (Time.le_lt_dec (f a_max) (f a_max0));
  [exists a_max0|exists a_max]; rewrite H1; split; eauto;
  apply Time.join_spec; eauto;
  etransitivity; eauto; rewrite Time.le_lteq; eauto.
- rewrite H1 in *; desf; etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- exists a_max0.
  rewrite H1; splits; eauto.
  apply Time.join_spec; eauto using Time.bot_spec.
Qed.

Lemma f_equal_max_join_if2 f P t P' t' (pred:Prop) (cond : {pred} + {~pred}) P'' :
  f_equal_max f P t ->
  f_equal_max f P' t' ->
  (forall x, P'' x <-> P x \/ P' x /\ pred) ->
  f_equal_max f P'' (Time.join t (if cond then t' else Time.bot)).
Proof.
unfold f_equal_max; ins; desf; splits; ins.
- rewrite H1 in *; desf; etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- destruct (Time.le_lt_dec (f a_max) (f a_max0));
  [exists a_max0|exists a_max]; rewrite H1; split; eauto;
  apply Time.join_spec; eauto;
  etransitivity; eauto; rewrite Time.le_lteq; eauto.
- rewrite H1 in *; desf; etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- exists a_max0.
  rewrite H1; splits; eauto.
  apply Time.join_spec; eauto using Time.bot_spec.
Qed.



Lemma ax_op_sim :
  forall op_st ax_st (SIM: sim op_st ax_st) ax_st' (AXSTEP: m_step ax_st ax_st'),
  exists op_st' e tid, Configuration.step e tid op_st op_st' /\ sim op_st' ax_st'.
Proof.
destruct ax_st, ax_st'; ins.
destruct AXSTEP; ins.
unfold sim, sim_f in SIM; ins; desf.
apply find_mapD in TID; desc; destruct z as [? local]; ins; desf.

generalize (gstep_read_rf COH GSTEP LAB_STEP); intro; desc.

assert (NON_WRITE: ~ is_write a).
  unfold is_write; destruct (lab a); ins.
generalize (gstep_non_write_mo COH GSTEP NON_WRITE) as SAME_MO; intro; desc.
rewrite SAME_MO in *. 
clear NON_WRITE.

assert (E: exists from rel, Cell.get (f b) ((Configuration.memory op_st) l) = 
          Some (from, {| Message.val:=v; Message.released:=rel |})).
  cdes GSTEP; cdes INC; cdes COH0; cdes WF.
  eapply get_cell; try edone; rewrite <- ACT_STEP in *; try edone.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.

assert (LOC_B: loc b = Some l). 
  unfold loc; destruct (lab b); ins; desf.


cdes MEM.  
specialize (MEM l). 
red in MEM; desc.
specialize (SIMCELL b WRITE_B LOC_B from {| Message.val := v; Message.released := rel |} E).
red in SIMCELL; desc; red in SIMMSG; desc.

desf.

assert (READABLE: Commit.readable (Local.commit local) l (f b) rel o).
{
clear -LOCAL TID SAME_MO GSTEP COH INb MONOTONE RFb LAB_STEP SC0 LABb.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.

assert (LOC_B: loc b = Some l). 
  unfold loc; destruct (lab b); ins; desf.

  specialize (LOCAL (thread a) (existT _ lang st) local TID); desf.
  red in LOCAL; red in LOCAL; desc; red in CUR; desc.
  constructor.
  {
  specialize (CUR_UR l).
  red in CUR_UR; desf.
  eapply transitivity with (y:=f a_max); try done.
  eapply valid_converse with (acts:=(a :: acts)) (mo:=mo0); eauto.
  - right; eapply c_cur_ur_in_acts; eauto.
  - right; done.
  - eapply c_cur_ur_dom1; eauto.
  - eapply c_cur_ur_dom2; eauto.
  - cdes GSTEP; rewrite <- ACT_STEP; apply COH0.
  - intro; cdes GSTEP.
    eapply Coherent_ur with (mo:=mo0) (c:=a); eauto.
    eby eapply gstep_new_ur0 with (acts:=acts) (a:=a). 
  }
  {
  specialize (CUR_RW l).
  red in CUR_RW; desf; ins.
  eapply transitivity with (y:=f a_max); try done.
  eapply valid_converse with (acts:=(a :: acts)) (mo:=mo0); try edone.
  - right; eapply c_cur_rw_in_acts; cdes COH; desc; eauto.
  - right; done. 
  - eapply c_cur_rw_dom1; eauto.
  - eapply c_cur_rw_dom2; eauto.
  - cdes GSTEP; rewrite <- ACT_STEP; apply COH0.
  - intro; cdes GSTEP.
    eapply Coherent_rw with (mo:=mo0) (c:=a); try eauto.
    eby eapply gstep_new_rw0 with (acts:=acts).
    right; unfold is_rlx; rewrite LAB_STEP; eauto.
  }
  {
  specialize (CUR_SC l).
  red in CUR_SC; desf; ins.
  eapply transitivity with (y:=f a_max); try done.
  eapply valid_converse with (acts:=(a :: acts)) (mo:=mo0); try edone.
  - right; eapply c_cur_sc_in_acts; cdes COH; desc; eauto.
  - right; done. 
  - eapply c_cur_sc_dom1; eauto.
  - eapply c_cur_sc_dom2; eauto.
  - cdes GSTEP; rewrite <- ACT_STEP; apply COH0.
  - intro; cdes GSTEP.
    eapply Coherent_sc with (mo:=mo0) (c:=a); try eauto.
    unfold is_sc; rewrite LAB_STEP; eauto.
    eby eapply gstep_new_sc0 with (acts:=acts).
  }
  {
cdes SC0.
specialize (SC1 l); desc; ins.
apply transitivity with (y:=f a_max); try done.
  eapply valid_converse with (acts:=(a :: acts)) (mo:=mo0); try edone.
  - right; eapply m_rel_sc_acta; cdes COH; desc; eauto.
  - right; done. 
  - eapply m_rel_doma1; eauto.
  - eapply m_rel_doma2; eauto.
  - cdes GSTEP; rewrite <- ACT_STEP; apply COH0.
  - intro; cdes GSTEP.
    eapply Coherent_sc with (mo:=mo0) (c:=a); try eauto.
    unfold is_sc; rewrite LAB_STEP; eauto.
    eapply gstep_new_sc_relation with (acts:=acts); eauto.
    by repeat red; rewrite LAB_STEP; ins; destruct o.
  }
}

(*   {
  destruct WF_OP_ST; destruct WF; eapply THREADS; eauto. 
  }
  {
  destruct WF_OP_ST. destruct MEM0.
  specialize (CLOSED l from (f b) {| Message.val := v; Message.released := rel |}).
  apply CLOSED in E; desc.
  eauto.
  }

 *)
(* assert (LOCAL_STEP: Local.read_step local (Configuration.memory op_st) l (f b) v rel o
         {| Local.commit := CommitFacts.read_min l (f b) rel o (Local.commit local);
            Local.promises := Local.promises local |}).
  econstructor; eauto.
  destruct WF_OP_ST.
  eapply CommitFacts.read_min_closed; eauto.
  destruct WF; eapply THREADS; eauto.
 *)
eexists _,_,(thread a).

Lemma foo (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

apply foo; [|intro STEP].
{
econstructor; try edone.
- econstructor.
- apply Thread.step_some.
  apply Thread.step_program.
  eapply Thread.step_read; eauto.
  econstructor; edone.
- admit.
}



(* match goal with |- Configuration.step ?G (thread a) op_st ?G' /\ _ =>
  set (M := G); set (M' := G') end.
 *)
(* match goal with |- ?G /\ _ =>
  set (M := G) end.
 *) 
red; simpl; splits; eauto.
- eby eapply Configuration.step_future.
- eby eapply Configuration.step_future.
- ins; rewrite IdentMap.gsspec in TID0; desf; ins;
  eapply NO_PROMISES; edone.
- exists f; split; [by apply MONOTONE|].
  clear STEP; red; splits; ins.
  * by rewrite IdentMap.map_add.
  * rewrite IdentMap.gsspec in TID0; desf; ins;
    exploit LOCAL; clear LOCAL; eauto; intro LOCAL;
    unfold sim_local in *; ins.



unfold sim_commit, sim_acq, sim_cur, sim_rel in *; desc; splits; intro l';
simpl;
try rewrite tm_join_bot;
try rewrite !tm_join;
try rewrite fun_if; simpl;
try rewrite if_arg with (x := l'); simpl.
{
eapply f_equal_max_join_if; eauto.
ins; rewrite (gstep_c_cur_ur COH GSTEP l' _ RFb (thread a)).
unfold is_ra, is_ra_lab; rewrite LAB_STEP; simpl; split; ins; desf; eauto.
}
{
rewrite tm_join_singleton_to_if.
eapply f_equal_max_join_if with (P:= fun x => c_cur_rw acts sb rmw rf sc (thread a) l' x \/
(x = b /\ loc b = Some l')); eauto.
eapply f_equal_max_join_if2; eauto.
apply f_equal_max_singleton; eauto.
intro; split; intro; desf; eauto.
ins; rewrite (gstep_c_cur_rw COH GSTEP l' _ RFb (thread a)).
unfold is_ra, is_ra_lab; rewrite LAB_STEP; simpl; split; ins; desf; eauto.
}
{
rewrite tm_join_singleton_to_if.
eapply f_equal_max_join_if with (P:= fun x => c_cur_sc acts sb rmw rf sc (thread a) l' x \/
(x = b /\ loc b = Some l')); eauto.
eapply f_equal_max_join_if2 with (P':= fun x => x=b); eauto.
apply f_equal_max_singleton; eauto.
intro; split; intro; desf; eauto.
admit.

}
{
eapply f_equal_max_join_if; eauto.
ins; rewrite (gstep_c_cur_ur COH GSTEP l' _ RFb (thread a)).
unfold is_ra, is_ra_lab; rewrite LAB_STEP; simpl; split; ins; desf; eauto.



Admitted.


Lemma ax_sim_op :
  forall op_st ax_st (SIM: sim op_st ax_st) op_st' e tid (OPSTEP: Configuration.step tid e op_st op_st'),
  exists ax_st', m_step ax_st ax_st' /\ sim op_st' ax_st'.
Proof.

Admitted.
