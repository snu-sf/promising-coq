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
Require Import Commit.

Require Import Gevents.
Require Import model.
Require Import Gsteps.
Require Import Machine.

Set Implicit Arguments.
Remove Hints plus_n_O.

Hint Resolve gstep_coh gstep_inc coh_wf.

Section Monotone.

Definition monotone (mo : event -> event -> Prop) f :=
  forall a b, mo a b -> Time.lt (f a) (f b).

Lemma new_f acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  f (MON: monotone mo f): 
  exists f', << F: forall b, In b acts -> f' b = f b >> /\
             << MON: monotone mo' f' >>.
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

Definition max_value f (INR : event -> Prop) val :=
 << UB: forall a (INa: INR a), Time.le (f a) val >> /\
 << MAX: exists a_max, << INa: INR a_max >> /\ <<LB': Time.le val (f a_max)>> >>.

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

Definition sim_msg (m: Message.t) b:=
  << VAL: Some m.(Message.val) = (val b) >> /\
  << UR: forall l, max_value f (fun a => msg_rel urr acts sb rmw rf sc l a b) ((m.(Message.released)).(Capability.ur) l) >> /\
  << RW: forall l, max_value f (fun a => msg_rel rwr acts sb rmw rf sc l a b) ((m.(Message.released)).(Capability.rw) l) >> /\
  << SC: forall l, max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) ((m.(Message.released)).(Capability.sc) l) >>.

Definition sim_cell_helper b from msg :=
  << SIMMSG: sim_msg msg b >> /\ 
  << FROM: Time.lt from (f b) >> /\ 
  << FROMRMW: (forall a (RFRMW: (rf ;; rmw) a b), from = f a) >>.

Definition sim_cell cell l  :=
  << DOM: forall b, (is_write b) /\ (loc b = Some l) <-> Cell.get (f b) cell <> None >> /\
  << SIMCELL: forall b (WRITE: is_write b) (LOC: loc b = Some l) 
                       from msg (CELL: Cell.get (f b) cell = Some (from, msg)),
                sim_cell_helper b from msg >>.

Definition sim_mem (mem: Memory.t) :=
  forall l, sim_cell (mem l) l.

Definition sim_rel rel i :=
  << REL_UR: forall l' l, max_value f (t_rel urr acts sb rmw rf sc i l' l) ((rel l').(Capability.ur) l) >> /\
  << REL_RW: forall l' l, max_value f (t_rel rwr acts sb rmw rf sc i l' l) ((rel l').(Capability.rw) l) >> /\
  << REL_SC: forall l' l, max_value f (t_rel scr acts sb rmw rf sc i l' l) ((rel l').(Capability.sc) l) >>.

Definition sim_cur cur i :=
  << CUR_UR: forall l, max_value f (t_cur urr acts sb rmw rf sc i l) (cur.(Capability.ur) l) >> /\
  << CUR_RW: forall l, max_value f (t_cur rwr acts sb rmw rf sc i l) (cur.(Capability.rw) l) >> /\
  << CUR_SC: forall l, max_value f (t_cur scr acts sb rmw rf sc i l) (cur.(Capability.sc) l) >>.

Definition sim_acq acq i :=
  << ACQ_UR: forall l, max_value f (t_acq urr acts sb rmw rf sc i l) (acq.(Capability.ur) l) >> /\
  << ACQ_RW: forall l, max_value f (t_acq rwr acts sb rmw rf sc i l) (acq.(Capability.rw) l) >> /\
  << ACQ_SC: forall l, max_value f (t_acq scr acts sb rmw rf sc i l) (acq.(Capability.sc) l) >>.

Definition sim_commit commit i :=
  << CUR: sim_cur commit.(Commit.cur) i >> /\
  << ACQ: sim_acq commit.(Commit.acq) i >> /\
  << REL: sim_rel commit.(Commit.rel) i >>.

Definition sim_local local i :=
  sim_commit local.(Local.commit) i.

End Simulation.

Definition sim_f f (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << LOCAL: forall i foo local (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
                sim_local f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) local i >> /\
  << SC: forall l, max_value f (S_tm (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) l) (Configuration.sc op_st l)  >> /\
  << MEM: sim_mem f (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (sc ax_st) op_st.(Configuration.memory) >>.

Definition sim (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << COH: Coherent (acts ax_st) (sb ax_st) (rmw ax_st) (rf ax_st) (mo ax_st) (sc ax_st) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << CONS_OP_ST: Configuration.consistent op_st >> /\
  << NO_PROMISES: forall i foo local (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: ts ax_st = IdentMap.map fst (Configuration.threads op_st) >> /\
  << TIME: exists f, << MONOTONE: monotone (mo ax_st) f >> /\  << SIM: sim_f f op_st ax_st >>>>.

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


(* Next two lemmas from old Vbase:
 *)
Lemma fun_if 
(A B : Type) (f : A -> B) (b : bool) (vT vF : A)
: f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg 
(A B : Type) (x : A)  (b : bool)
: forall fT fF : A -> B,
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

Lemma if_same 
(A : Type) (b : bool): forall f : A,
  (if b then f else f) = f.
Proof. desf. Qed.

Lemma tm_join a b l :
  TimeMap.join a b l =  Time.join (a l) (b l).
Proof.  ins. Qed.

Lemma tm_singleton l t  :
  TimeMap.singleton l t l = t.
Proof.
unfold TimeMap.singleton, LocFun.add.
rewrite Loc.eq_dec_eq.
done.
Qed.

Lemma tm_singleton2 l l' t (NEQ: l <> l') :
  TimeMap.singleton l t l' = Time.bot.
Proof.
unfold TimeMap.singleton, LocFun.add.
rewrite Loc.eq_dec_neq.
by rewrite LocFun.init_spec; done.
by intro; subst; auto.
Qed.

Lemma tm_join_singleton_to_if t1 t2 l l' :
  Time.join t1 (TimeMap.singleton l t2 l') = 
  Time.join t1 (if (Loc.eq_dec l l') then t2 else Time.bot).
Proof.
desf; [by rewrite tm_singleton|by rewrite tm_singleton2].
Qed.

Lemma time_join_bot a  :
  Time.join a Time.bot =  a.
Proof.
Admitted.

Lemma tm_join_bot a  :
  TimeMap.join a TimeMap.bot =  a.
Proof.
eapply TimeMap.antisym.
apply TimeMap.join_spec.
apply TimeMap.le_PreOrder.
apply TimeMap.bot_spec.
apply TimeMap.join_l.
Qed.

Lemma max_value_singleton f b t (T: t = f b):
  max_value f (eq b) t.
Proof.
red; splits; ins; desc; subst.
by apply Time.le_lteq; eauto.
exists b; splits; try apply Time.le_lteq; eauto.
Qed.

Lemma max_value_same_set f f' P P' t :
  max_value f P t ->
  (forall x, P x <-> P' x) ->  
  (forall x, P x -> f' x = f x) ->  
  max_value f' P' t.
Proof.
  unfold max_value; ins; desf; splits; ins.
  rewrite H1; specialize (H0 a); desf; eauto.
  exists a_max; rewrite H1; specialize (H0 a_max); desf; split; auto.
Qed.



Lemma max_value_join_if f f' P P' P'' t t' (cond : bool):
  max_value f P t ->
  max_value f P' t' ->
  (forall x, P'' x <-> P x \/ P' x /\ cond) ->
  (forall x, P'' x -> f' x = f x) ->  
  max_value f' P'' (Time.join t (if cond then t' else Time.bot)).
Proof.
unfold max_value; ins; desf; splits; ins.
- rewrite H2; rewrite H1 in *; desf;
  try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- destruct (Time.le_lt_dec (f a_max) (f a_max0));
    [exists a_max0|exists a_max];
  splits; try by (rewrite H1; auto).
  all: rewrite H2.
  all: try (apply Time.join_spec; eauto;
       etransitivity; eauto; rewrite Time.le_lteq; eauto). 
  all: rewrite H1; eauto.
- rewrite H2; rewrite H1 in *; desf;
  try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- exists a_max0.
  rewrite H2; rewrite H1; splits; eauto.
  apply Time.join_spec; eauto using Time.bot_spec.
Qed.

Lemma max_value_join f f' P P' P'' t t':
  max_value f P t ->
  max_value f P' t' ->
  (forall x, P'' x <-> P x \/ P' x) ->
  (forall x, P'' x -> f' x = f x) ->  
  max_value f' P'' (Time.join t t').
Proof.
Admitted.

Lemma max_value_join_if2 f f' P P' P'' t t' (pred:Prop) (cond : {pred} + {~pred}):
  max_value f P t ->
  max_value f P' t' ->
  (forall x, P'' x <-> P x \/ P' x /\ pred) ->
  (forall x, P'' x -> f' x = f x) ->  
  max_value f' P'' (Time.join t (if cond then t' else Time.bot)).
Proof.
unfold max_value; ins; desf; splits; ins.
- rewrite H2; rewrite H1 in *; desf;
  try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- destruct (Time.le_lt_dec (f a_max) (f a_max0));
    [exists a_max0|exists a_max];
  splits; try by (rewrite H1; auto).
  all: rewrite H2.
  all: try (apply Time.join_spec; eauto;
       etransitivity; eauto; rewrite Time.le_lteq; eauto). 
  all: rewrite H1; eauto.
- rewrite H2; rewrite H1 in *; desf;
  try by etransitivity; eauto; eauto using Time.join_l, Time.join_r. 
- exists a_max0.
  rewrite H2; rewrite H1; splits; eauto.
  apply Time.join_spec; eauto using Time.bot_spec.
Qed.


(* Lemma my_Time_join_l a b c:
Time.le a b ->
Time.le a (Time.join b c).
Proof.
etransitivity; eauto using Time.join_l.
Qed.

Lemma my_Time_join_r a b c:
Time.le a c ->
Time.le a (Time.join b c).
Proof.
etransitivity; eauto using Time.join_r.
Qed.

Lemma my_Time_refl a:
Time.le a a.
Proof.
reflexivity.
Qed. *)

(* max_value f'
  (t_cur urr (acts ax_st') (sb ax_st') (rmw ax_st') (rf ax_st') (sc ax_st') (thread a) l')
  (Time.join (Capability.ur (Commit.cur (Local.commit local)) l')
     (if LocSet.Facts.eq_dec l l' then f' a else Time.bot))
 *)
Lemma max_value_join_loc f f' P P' t l l' b (LOC: loc b = Some l):
  max_value f P t ->
  (forall x, P' x <-> P x \/ x = b /\ loc x = Some l') ->
  (forall x, P x -> f' x = f x) ->  
  max_value f' P'
  (Time.join t
     (if LocSet.Facts.eq_dec l l' then (f' b) else Time.bot)).
Proof.
ins.
eapply max_value_join_if2 with (f:=f'); eauto.
eapply max_value_same_set; eauto.
apply max_value_singleton; eauto.
intro; specialize (H1 x); specialize (H0 x).
split; ins; desf; eauto.
apply H0 in H2; desf; eauto.
Qed.

Lemma max_value_join_if_loc f f' P P' P'' t t' (cond : bool) l l' b (LOC: loc b = Some l):
  max_value f P t ->
  max_value f P' t' ->
  (forall x, P'' x <-> P x \/ P' x /\ cond \/ x = b /\ loc x = Some l') ->
  (forall x, P' x -> f' x = f x) ->  
  (forall x, P x -> f' x = f x) ->  
  max_value f' P''
  (Time.join (Time.join t
     (if LocSet.Facts.eq_dec l l' then (f' b) else Time.bot))
     (if cond then t' else Time.bot)).
Proof.
ins.
eapply max_value_join_if with (f:=f') (P:= fun x=>P x \/ b = x /\ l = l') (P':=P'); 
try edone.
- eapply max_value_join_if2 with (f:=f'); eauto.
eapply max_value_same_set; eauto.
apply max_value_singleton; eauto.
- eapply max_value_same_set; eauto.
- intro; specialize (H1 x).
split; ins; desf; eauto.
apply H1 in H4; desf; eauto.
Qed.

Lemma sim_local_other_threads acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f i (NEQ: i <> thread a) local (LOCAL: sim_local f acts sb rmw rf sc local i):
    sim_local f acts' sb' rmw' rf' sc' local i.
Proof.
unfold sim_local, sim_commit, sim_cur, sim_acq, sim_rel in *; desf; splits;
ins; eapply max_value_same_set; try edone; intro; symmetry.
all: try eapply gstep_t_cur_other;  
     try eapply gstep_t_acq_other;  
     try eapply gstep_t_rel_other;  
     eauto 2 using gstep_urr_a, gstep_rwr_a, gstep_scr_a, urr_mon, rwr_mon, scr_mon.
Qed.

Lemma sim_local_other_threads' acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f f' i (NEQ: i <> thread a) local 
  (LOCAL: sim_local f acts sb rmw rf sc local i)
  (F: forall a, (In a acts) -> f' a = f a) :
    sim_local f' acts' sb' rmw' rf' sc' local i.
Proof.
unfold sim_local, sim_commit, sim_cur, sim_acq, sim_rel in *; desf; splits;
ins; eapply max_value_same_set; try edone; intro; symmetry.
all: try eapply gstep_t_cur_other;  
     try eapply gstep_t_acq_other;  
     try eapply gstep_t_rel_other;  
     eauto 2 using gstep_urr_a, gstep_rwr_a, gstep_scr_a, urr_mon, rwr_mon, scr_mon.
all: symmetry; apply F; eauto with acts.
Qed.

Lemma gstep_tm_to_a acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  tm 
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' ;; hb acts' sb' rmw' rf') (tm acts' sb' rmw' rf' sc'))
  (TM_MON: inclusion (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc'))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc x y -> In y acts)
   l x (CUR: t_cur tm acts sb rmw rf sc (thread a) l x) :
   tm acts' sb' rmw' rf' sc' x a.
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
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  tm (CUR: max_value f (t_cur tm acts sb rmw rf sc (thread a) l) t) 
  (WRITE : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> is_write x)
  (ACTS : forall x, t_cur tm acts sb rmw rf sc (thread a) l x -> In x acts)
  (COHERENT: forall c, mo' b c -> tm acts' sb' rmw' rf' sc' c a -> False)
  (TM_HB: inclusion (tm acts' sb' rmw' rf' sc' ;; hb acts' sb' rmw' rf') (tm acts' sb' rmw' rf' sc'))
  (TM_MON: inclusion (tm acts sb rmw rf sc) (tm acts' sb' rmw' rf' sc'))
  (TM_ACTS : forall x y, tm acts sb rmw rf sc x y -> In y acts)
  (RFb: rf' b a) : Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in CUR; desf.
eapply transitivity with (y:=f a_max); try done.
cdes GSTEP. 
eapply monotone_converse with (acts:=(a :: acts)); eauto.
- right; eauto. 
- eapply rf_acta in RFb; eauto. rewrite <- ACT_STEP; eauto.
- eapply rf_doma in RFb; eauto.
- red in INa; red in INa; desc. apply c_cur_doma2 in INa. edone.
- eapply loceq_rf in RFb; eauto. unfold loc in *. rewrite LABa in RFb. done.
- rewrite gstep_non_write_mo with (mo':=mo'); eauto.
  rewrite <- ACT_STEP.
  cdes COH0; cdes WF; eauto.
- intro.
  eapply COHERENT; eauto.
  eapply gstep_non_write_mo with (acts:=acts) (mo:=mo); eauto.
  eapply gstep_tm_to_a; eauto.
Qed.

Lemma Readable_msg_sc acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  (MSG: max_value f (fun a => msg_rel scr acts sb rmw rf sc l a b) t)
  (RFb: rf' b a) (SC: is_sc a): Time.le t (f b).
Proof.
assert (~ is_write a).
  intro; unfold is_write in *; destruct (lab a); ins.
red in MSG; desf.
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
  cdes COH0; cdes WF; eauto.
- intro. red in INa. red in INa.
  unfold seq, eqv_rel in INa; desc; subst.
  eapply Coherent_scr_rel; eauto.
  eapply gstep_non_write_mo with (mo:=mo); eauto.
  eapply scr_rel_mon; eauto.
  eexists; eauto.
Qed.

Lemma Readable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f (MON: monotone mo f) l v o b (LABa: lab a = Aload l v o)
  local rel
  (MSG: max_value f (fun a : event => msg_rel scr acts sb rmw rf sc l a b)
        (Capability.sc rel l))
  (URR: max_value f (t_cur urr acts sb rmw rf sc (thread a) l)
           (Capability.ur (Commit.cur (Local.commit local)) l))
  (RWR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l)
           (Capability.rw (Commit.cur (Local.commit local)) l))
  (SCR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l)
           (Capability.sc (Commit.cur (Local.commit local)) l))
  (RFb: rf' b a): 
    Commit.readable (Local.commit local) l (f b) rel o.
Proof.
constructor; try intro.
-  eapply Readable_cur_tm; eauto using Coherent_ur, urr_hb, urr_mon with rel acts.
   by eapply urr_actb; eauto.
- eapply Readable_cur_tm; eauto using rwr_hb, rwr_mon with rel acts.
  ins; eapply Coherent_rw with (mo:=mo'); eauto.
  right; splits; eauto with acts.
  eapply rwr_actb; eauto.
- eapply Readable_cur_tm; eauto using scr_hb, scr_mon with rel acts.
  ins; eapply Coherent_scr with (mo:=mo');  eauto with acts.
  eapply scr_actb; eauto.
- eapply Readable_msg_sc; eauto with acts.
Qed.

(******************************************************************************)
(** * Lemmas for the write step   *)
(******************************************************************************)

Lemma Writable_cur_rwr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l) t) 
   : Time.lt t (f' a).
Proof.
red in CUR; desf.
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
  cdes COH0; cdes WF; eauto.
- intro.
  eapply Coherent_rw; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply rwr_hb.
  eapply rwr_mon; eauto.
  eapply rwr_actb; eauto.
- intro; subst; eauto with acts. 
Qed.

Lemma Writable_cur_scr acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (CUR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l) t) 
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in CUR; desf.
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
  cdes COH0; cdes WF; eauto.
- intro.
  eapply Coherent_scr; eauto.
  eapply gstep_tm_to_a; eauto.
  eapply scr_hb.
  eapply scr_mon; eauto.
  eapply scr_actb; eauto.
- intro; subst; eauto with acts. 
Qed.

Lemma Writable_sc_map acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  t f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f') l v o (LABa: lab a = Astore l v o)
  (SCMAP: max_value f (S_tm acts sb rmw rf l) t)
  (SC: is_sc a) : Time.lt t (f' a).
Proof.
red in SCMAP; desf.
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
  cdes COH0; cdes WF; eauto.
- intro.
  eapply Coherent_scr; eauto.
  red in INa; red in INa; desc.
  eapply S_tm_sc; eauto with acts.
  eapply S_tmr_mon; eauto.
Qed.

Lemma Writable_full acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc'
  a (GSTEP: gstep acts sb rmw rf mo sc acts' sb' rmw' rf' mo' sc' a)
  (COH: Coherent acts sb rmw rf mo sc) 
  f f' (F : forall b, In b acts -> f' b = f b)
  (MON: monotone mo' f')
  l v o (LABa: lab a = Astore l v o)
  local sc_map
  (SC : forall l : Loc.t, max_value f (S_tm acts sb rmw rf l) (sc_map l))
  (RWR: max_value f (t_cur rwr acts sb rmw rf sc (thread a) l)
           (Capability.rw (Commit.cur (Local.commit local)) l))
  (SCR: max_value f (t_cur scr acts sb rmw rf sc (thread a) l)
           (Capability.sc (Commit.cur (Local.commit local)) l)):
  Commit.writable (Local.commit local) sc_map l (f' a) o.
Proof.
constructor; try intro.
eapply Writable_cur_rwr; eauto.
eapply Writable_cur_scr; eauto with acts.
eapply Writable_sc_map; eauto with acts.
Admitted.

(******************************************************************************)
(** * Main Theorem: the operational machine simulates the axiomatic machine   *)
(******************************************************************************)

Lemma foo (P Q : Prop) : P -> (P -> Q) -> P /\ Q.
Proof. tauto. Qed.

Lemma ax_op_sim_helper 
op_st ax_st (SIM: sim op_st ax_st) ax_st' (AXSTEP: step ax_st ax_st')
(NEXT: exists (e0 : option Event.t) (tid : Ident.t) threads sc_map memory,
  Configuration.step e0 tid op_st 
    {| Configuration.threads:=threads; Configuration.sc:=sc_map; 
       Configuration.memory:=memory  |}
  /\
  sim {| Configuration.threads:=threads; Configuration.sc:=sc_map; 
         Configuration.memory:=memory  |} ax_st') :
  exists e tid op_st', Configuration.step e tid op_st op_st' /\ sim op_st' ax_st'.
Proof.
desf.
eauto.
Qed.

Lemma ax_op_sim :
  forall op_st ax_st (SIM: sim op_st ax_st) ax_st' (AXSTEP: step ax_st ax_st'),
  exists e tid op_st', Configuration.step e tid op_st op_st' /\ sim op_st' ax_st'.
Proof.
ins.
destruct AXSTEP.
red in SIM; desc.
red in SIM. desc. 
rewrite STATES in TID.
apply find_mapD in TID; desc; destruct z as [? local]; ins; desf.

destruct MSTEP; subst.

(** SILENT **)
{
eexists _,i,_.
split.
econstructor; try edone.
eauto.
apply Thread.step_program.
eapply Thread.step_silent; edone.
admit.
admit.
}

(** READ **)
{
assert (SCa: is_sc a = Ordering.le Ordering.seqcst o).
  unfold is_sc; unfold ord; rewrite LABa; done.
assert (RAa: is_ra a = Ordering.le Ordering.acqrel o).
  unfold is_ra; unfold ord; rewrite LABa; done.
assert (RLXa: is_rlx a = Ordering.le Ordering.relaxed o).
  unfold is_rlx; unfold ord; rewrite LABa; done.

generalize (gstep_read_rf COH GSTEP LABa); intro; desc.

assert (~ is_wfence a /\ ~ is_write a).
  unfold is_write, is_wfence; destruct (lab a); ins.

assert (E: exists from rel, Cell.get (f b) ((Configuration.memory op_st) l) = 
          Some (from, {| Message.val:=v; Message.released:=rel |})).
  cdes GSTEP; cdes INC; cdes COH0; cdes WF.
  eapply get_cell; try edone. 
  rewrite <- ACT_STEP in *; try edone.

assert (WRITE_B: is_write b). 
  unfold is_write; destruct (lab b); ins.
assert (LOC_B: Gevents.loc b = Some l). 
  unfold Gevents.loc; destruct (lab b); ins; desf.

cdes MEM. specialize (MEM l); red in MEM; desc.
specialize (SIMCELL b WRITE_B LOC_B from 
  {| Message.val := v; Message.released := rel |} E).
red in SIMCELL; desc; red in SIMMSG; desc.

eexists _,(thread a),_.
apply foo; [|intro STEP].
{
econstructor; try edone.
eauto.
apply Thread.step_program; try edone.
  eapply Thread.step_read; eauto.
  econstructor; try edone.
  specialize (LOCAL (thread a) (existT _ lang st) local TID); desf.
  red in LOCAL; red in LOCAL; desc; red in CUR; desc.
  eapply Readable_full; eauto.
admit.
}
red; simpl; splits; eauto.
- eby eapply Configuration.step_future.
- eby eapply Configuration.step_future.
- ins; rewrite IdentMap.gsspec in TID0; desf; ins;
  eapply NO_PROMISES; edone.
- rewrite IdentMap.map_add. admit.
- clear STEP.

exists f; split.
* rewrite <- gstep_non_write_mo; eauto with acts.
* red; splits; ins.
  + ins; rewrite IdentMap.gsspec in TID0; desf; ins.
    Focus 2. by eapply sim_local_other_threads; eauto.
    red; ins; red; ins.
    exploit LOCAL; clear LOCAL; eauto; intro LOCAL; unfold sim_local in *; ins.
    unfold sim_commit, sim_acq, sim_cur, sim_rel in *; desc; splits; intro l';
    simpl;
    unfold TimeMap.bot.
    all: try (rewrite !tm_join; rewrite time_join_bot).
    all: try (rewrite !tm_join; rewrite tm_join_singleton_to_if).
    all: try rewrite !time_join_bot.
    all: try rewrite !fun_if; simpl.
    all: try rewrite !if_arg with (x := l'); simpl.
    all: unfold TimeMap.bot; simpl.
    all: try intro; try eapply max_value_join_if_loc; try edone; simpl.
    all: try intro; try eapply max_value_join_if; try edone.
    all: try intro; try eapply max_value_same_set; try edone.
    all: try rewrite <- RAa; try rewrite <- RLXa; try rewrite <- SCa.



    eapply gstep_t_cur_urr_read; eauto.
    eapply gstep_t_cur_rwr_read; eauto.
    eapply gstep_t_cur_scr_read; eauto.
    eapply gstep_t_acq_urr_read; eauto.
    admit.
    admit.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_urr_a, urr_mon.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_rwr_a, rwr_mon.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_scr_a, scr_mon.
+ eapply max_value_same_set; try edone.
admit.
+ admit.
}


(** Write **)
{
generalize (new_f GSTEP MONOTONE); intro; desc.

assert (LOC_A: Gevents.loc a = Some l). 
  unfold Gevents.loc; destruct (lab a); ins; desf.


eexists _,(thread a),_.
apply foo; [|intro STEP].
{
econstructor; try edone.
eauto.
apply Thread.step_program; try edone.
eapply Thread.step_write with (to:= f' a); eauto.
econstructor; try edone.
specialize (LOCAL (thread a) (existT _ lang st) local TID); desf.
red in LOCAL; red in LOCAL; desc; red in CUR; desc.
eapply Writable_full; eauto.
admit.
admit.
admit.
}

red; simpl; splits; eauto.
- eby eapply Configuration.step_future.
- eby eapply Configuration.step_future.
- ins; rewrite IdentMap.gsspec in TID0; desf; ins;
  eapply NO_PROMISES; edone.
- rewrite IdentMap.map_add. admit.
-
  exists f'; splits; try done.
   red; splits; ins.
  + ins; rewrite IdentMap.gsspec in TID0; desf; ins.
    Focus 2.  eapply sim_local_other_threads'; eauto.
    red; ins; red; ins.
    exploit LOCAL; clear LOCAL; eauto; intro LOCAL; unfold sim_local in *; ins.
    unfold sim_commit, sim_acq, sim_cur, sim_rel in *; desc; splits; intro l';
    simpl.
    all: unfold TimeMap.bot, LocFun.add; simpl.
    all: try (rewrite !tm_join; rewrite time_join_bot).
    all: try (rewrite !tm_join; rewrite tm_join_singleton_to_if).
    all: try rewrite !time_join_bot.
    all: try rewrite !fun_if; simpl.
    all: try rewrite !if_arg with (x := l'); simpl.
    all: unfold TimeMap.bot; simpl.
all: try rewrite !if_same.
    all: try rewrite !time_join_bot.


all: try eapply max_value_join_loc; eauto with acts; simpl.

    all: try intro; try eapply max_value_join_if_loc; eauto with acts; simpl.
    all: try intro; try eapply max_value_join_if; eauto with acts; simpl.


    all: try intro; try eapply max_value_same_set; try edone.
    all: try rewrite <- RAa; try rewrite <- RLXa; try rewrite <- SCa.
    eapply gstep_t_cur_urr_write; eauto.
    eapply gstep_t_cur_rwr_read; eauto.
    eapply gstep_t_cur_scr_read; eauto.
    eapply gstep_t_acq_urr_read; eauto.
    admit.
    admit.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_urr_a, urr_mon.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_rwr_a, rwr_mon.
    intro; symmetry; eapply gstep_t_rel_other; eauto using gstep_scr_a, scr_mon.
+ eapply max_value_same_set; try edone.
admit.
+ admit.



}
Admitted.

Lemma ax_sim_op :
  forall op_st ax_st (SIM: sim op_st ax_st) op_st' e tid (OPSTEP: Configuration.step tid e op_st op_st'),
  exists ax_st', m_step ax_st ax_st' /\ sim op_st' ax_st'.
Proof.

Admitted.
