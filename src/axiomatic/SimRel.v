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
Require Import TView.

Require Import Gevents.
Require Import model.
Require Import Gstep.
Require Import Machine.

Set Implicit Arguments.
Remove Hints plus_n_O.

Hint Resolve gstep_wf gstep_inc coh_wf.

Tactic Notation "eauto_red" integer(n) "using" constr(lemma) :=
  let H := fresh in assert (H := lemma); red in H; eauto n.

Tactic Notation "eauto_red" "using" constr(lemma) :=
  let H := fresh in assert (H := lemma); red in H; eauto.

Lemma find_mapD A B tid (f: A -> B) x y :
  IdentMap.find tid (IdentMap.map f x) = Some y ->
  exists z, IdentMap.find tid x = Some z /\ y = f z.
Proof.
  rewrite IdentMap.Facts.map_o; unfold option_map; ins; desf; eauto.
Qed.

Lemma lt_bot a (H: Time.lt a Time.bot) : False.
Proof.
  eapply Time.lt_strorder, TimeFacts.le_lt_lt; try edone.
  by eapply Time.bot_spec.
Qed.

Lemma in_interval a b (LT: Time.lt a b) : Interval.mem (a, b) b.
Proof.
econs; ins.
by rewrite Time.le_lteq; eauto.
Qed.

Lemma no_promises_consistent op_st 
  (NO_PROMISES: forall i foo local 
    (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
    local.(Local.promises) = Memory.bot):
  Configuration.consistent op_st.
Proof.
eexists; splits; try econs.
eby eapply NO_PROMISES.
Qed.

Section Monotone.

Definition monotone (mo : relation event) f :=
  forall a b, mo a b -> Time.lt (f a) (f b).

Definition monotone_acts acts (mo : relation event) f :=
  forall a b, mo a b -> In a acts -> In b acts -> Time.lt (f a) (f b).

Lemma no_imm_predecessor_simpl 
      (mo : relation event) (IRR: irreflexive mo) (T: transitive mo) acts a
      (NEG : ~
      (exists prev,
         In prev acts /\
         mo prev a /\
         (forall y : event, mo prev y -> mo y a -> In y acts -> False)))
      prev (IN: In prev acts) (MO: mo prev a) : False. 
Proof.
  ins; destruct NEG; revert prev IN MO.
  remember (length acts) as n; revert acts Heqn; induction n; ins.
    by destruct acts; ins; desf.
  destruct (classic (exists y, In y acts /\ mo y a /\ mo prev y)); desf;
  [|by exists prev; splits; eauto].
  apply in_split_perm in IN; desf.
  rewrite IN in *; ins; desf; try (by exfalso; eauto).
  edestruct IHn as [k N]; desc; eauto; exists k; splits; ins;
  rewrite IN in *; ins; desf; eauto.
Qed.

Lemma no_imm_successor_simpl 
      (mo : relation event) (IRR: irreflexive mo) (T: transitive mo) acts a
      (NEG : ~
      (exists next,
         In next acts /\
         mo a next /\
         (forall y : event, mo a y -> mo y next -> In y acts -> False)))
      next (IN: In next acts) (MO: mo a next) : False. 
Proof.
  ins; eapply no_imm_predecessor_simpl with (mo := fun x y => mo y x); eauto;
  red; ins; desf; eauto 10.
Qed.

Lemma find_free_interval acts mo (IRR: irreflexive mo) (T: transitive mo) 
      A (dom: A -> event -> Prop) 
      (D : forall x y, mo x y -> exists l, dom l x /\ dom l y)
      (DD : forall x l1 l2, dom l1 x -> dom l2 x -> l1 = l2)
      (TOT: forall l, is_total (dom l) mo) a 
  f_from f_to (MON: monotone_acts acts mo f_to) 
  (NADJ: forall x (MOx: mo x a)
                  (IMMx: forall z, mo x z -> mo z a -> In z acts -> False) 
                y (MOy: mo a y)
                  (IMMy: forall z, mo a z -> mo z y -> In z acts -> False), 
     f_to x <> f_from y)
  (NBOT: forall y (MO: mo a y) 
                  (IMM: forall z, mo a z -> mo z y -> In z acts -> False), 
            Time.bot <> f_from y)
  (WF: forall l x (INx: In x acts) (Dx: dom l x)
      (NB: f_from x <> Time.bot \/ f_to x <> Time.bot), Time.lt (f_from x) (f_to x))
  (NIN: ~ In a acts)
  (DJ: forall l x (INx: In x acts) (Dx: dom l x) y (NEQ: x <> y)
                  (INy: In y acts) (Dy: dom l y),
         Interval.disjoint (f_from x, f_to x) (f_from y, f_to y)) : 
  exists from' to',
    Time.lt from' to' /\ 
    (forall x, In x acts -> mo x a -> Time.le (f_to x) from') /\
    (forall x, In x acts -> mo a x -> Time.le to' (f_from x)).
Proof.
  destruct (classic (exists prev, In prev acts /\ mo prev a /\
                                  (forall y, mo prev y -> mo y a -> In y acts -> False))) 
    as [P|P'];
  [ desc; pose (from' := f_to prev) | pose (from' := Time.bot); 
    assert (P := no_imm_predecessor_simpl IRR T acts a P'); clear P' ];
  exists from'; 
  (destruct (classic (exists next, In next acts /\ mo a next /\
                                  (forall y, mo a y -> mo y next -> In y acts -> False))) 
     as [Q|Q'];
    [desc; exists (f_from next) |  exists (Time.incr from');
     assert (Q := no_imm_successor_simpl IRR T acts a Q'); clear Q' ]); subst from'.
  - assert (K: Interval.disjoint (f_from prev, f_to prev) (f_from next, f_to next)).
      destruct (D prev next); desc; eauto.
      by eapply DJ; eauto; ins; desf; intro; desf; eauto.
    exploit D; try exact P0; intro Dp; desc.
    exploit D; try exact Q0; intro Dn; desc.
    assert (l0 = l) by eauto; subst; clear Dp0.
    splits; ins. 
      red in K; destruct (Time.le_lt_dec (f_from next) (f_to prev)) as [LE|LT]; desf.
      exfalso; rewrite Time.le_lteq in *; desf; eauto.
      2: by eapply eq_sym, NADJ in LE; eauto.
      exploit (MON prev next); ins; eauto.
      eapply (K (f_to prev)); econs; ins; eauto.
      eapply WF; try edone.
      eby right; intro X; rewrite X in *; eapply lt_bot.
      by rewrite Time.le_lteq; eauto.
      by rewrite Time.le_lteq; eauto.
    rewrite Time.le_lteq.
    destruct (classic (x = prev)) as [|N]; desf; eauto.
      destruct (D _ _ H0) as [l' ?]; desc.
      eapply TOT in N; eauto; desf; eauto; try solve [exfalso; eauto].
      exploit (DD a l l'); eauto; ins; desf.
    rewrite Time.le_lteq.
    destruct (classic (x = next)) as [|N]; desf; eauto.
      destruct (D _ _ H0) as [l' ?]; desc.
      eapply TOT in N; eauto; desf; eauto; try solve [exfalso; eauto];
       exploit (DD a l l'); eauto; ins; desf.
    destruct (TimeFacts.le_lt_dec (f_from x) (f_from next)); eauto.
    destruct l as [l|]; eauto.
    assert (f_from next <> Time.bot \/ f_to next <> Time.bot).
      by left; intro X; eapply lt_bot; eapply MON in N; rewrite X in l; eauto.
    exfalso; eapply DJ with (x := x) (y:= next) (x0 := f_to next); eauto.
    by intro; desf; eauto.
    econs; ins.
    eapply TimeFacts.le_lt_lt.
    rewrite Time.le_lteq; eby left.
    eauto.
    eby rewrite Time.le_lteq; left; eapply MON.
    by apply in_interval; eauto.
  -
  splits; ins; eauto using Time.incr_spec; try solve [exfalso; eauto].
  rewrite Time.le_lteq.
  destruct (classic (x = prev)) as [|N]; desf; eauto.
    destruct (D _ _ P0) as [l ?], (D _ _ H0) as [l' ?]; desc.
    eapply TOT in N; eauto; desf; eauto; try solve [exfalso; eauto].
    by exploit (DD a l l'); eauto; ins; desf.
  - splits; ins.
    by generalize (Time.bot_spec (f_from next)); rewrite Time.le_lteq; 
      intro M; desf; eauto; eapply NBOT in M; ins.
    by exfalso; eauto.
    rewrite Time.le_lteq.
    destruct (classic (x = next)) as [|N]; desf; eauto.
      destruct (D _ _ Q0) as [l ?], (D _ _ H0) as [l' ?]; desc.
      eapply TOT in N; eauto; desf; eauto; try solve [exfalso; eauto];
      exploit (DD a l l'); eauto; ins; desf.
    destruct (TimeFacts.le_lt_dec (f_from x) (f_from next)); eauto.
    destruct l as [l|]; eauto.
    assert (f_from next <> Time.bot \/ f_to next <> Time.bot).
      by left; intro X; eapply lt_bot; eapply MON in N; rewrite X in l; eauto.
    exfalso; eapply DJ with (x := x) (y:= next) (x0 := f_to next); eauto.
    by intro; desf; eauto.
    econs; ins.
    eapply TimeFacts.le_lt_lt; try edone.
    eby left.
    eauto.
    eby rewrite Time.le_lteq; left; eapply MON.
    by apply in_interval; eauto.
  - by splits; intros; eauto using Time.incr_spec; try solve [exfalso; eauto]. 
Qed.


Lemma find_free_interval2 acts mo (IRR: irreflexive mo) (T: transitive mo) 
      A (dom: A -> event -> Prop) 
      (D : forall x y, mo x y -> exists l, dom l x /\ dom l y)
      (DD : forall x l1 l2, dom l1 x -> dom l2 x -> l1 = l2)
      (TOT: forall l, is_total (dom l) mo) a 
  f_from f_to (MON: monotone_acts acts mo f_to) 
  (NADJ: forall x (MOx: mo x a)
                  (IMMx: forall z, mo x z -> mo z a -> In z acts -> False) 
                y (MOy: mo a y)
                  (IMMy: forall z, mo a z -> mo z y -> In z acts -> False), 
     f_to x <> f_from y)
  (NBOT: forall y (MO: mo a y) 
                  (IMM: forall z, mo a z -> mo z y -> In z acts -> False), 
            Time.bot <> f_from y)
  (WF: forall l x (INx: In x acts) (Dx: dom l x) 
      (NB: f_from x <> Time.bot \/ f_to x <> Time.bot), Time.lt (f_from x) (f_to x))
  (NIN: ~ In a acts)
  (DJ: forall l x (INx: In x acts) (Dx: dom l x) y (NEQ: x <> y)
                  (INy: In y acts) (Dy: dom l y),
         Interval.disjoint (f_from x, f_to x) (f_from y, f_to y)) : 
  exists from' to',
    << WF': Time.lt from' to' >> /\ 
    << PREV': forall x, In x acts -> mo x a -> Time.lt (f_to x) from' >> /\
    << NEXT': forall x, In x acts -> mo a x -> Time.lt to' (f_from x) >> /\
    << NBOT': Time.bot <> from' >>.
Proof.
  edestruct find_free_interval as (from & to & K); eauto; desc.
  exists (Time.middle from to), (Time.middle (Time.middle from to) to).
  splits; ins.
  - by do 2 apply Time.middle_spec.
  - by eapply TimeFacts.le_lt_lt; eauto; apply Time.middle_spec.
  - by eapply TimeFacts.lt_le_lt; eauto; do 2 apply Time.middle_spec.
  - destruct (@Time.middle_spec from to); ins.
    intro X; rewrite <- X in *.
    eapply Time.lt_strorder; eauto using Time.bot_spec, TimeFacts.lt_le_lt.
Qed.

Lemma time_lt_trans x y z : Time.lt x y -> Time.lt y z -> Time.lt x z.
Proof. eby etransitivity. Qed.

Lemma new_f acts mo (IRR: irreflexive mo) (T: transitive mo) 
      A (dom: A -> event -> Prop) 
      (D : forall x y, mo x y -> exists l, dom l x /\ dom l y)
      (DD : forall x l1 l2, dom l1 x -> dom l2 x -> l1 = l2)
      (TOT: forall l, is_total (dom l) mo) a 
      (ACT : forall x l, dom l x -> In x (a :: acts))
  f_from f_to (MON: monotone_acts acts mo f_to) 
  (NADJ: forall x (MOx: mo x a)
                  (IMMx: forall z, mo x z -> mo z a -> In z acts -> False) 
                y (MOy: mo a y)
                  (IMMy: forall z, mo a z -> mo z y -> In z acts -> False), 
     f_to x <> f_from y)
  (NBOT: forall y (MO: mo a y) 
                  (IMM: forall z, mo a z -> mo z y -> In z acts -> False), 
            Time.bot <> f_from y)
  (WF: forall l x (INx: In x acts) (Dx: dom l x) 
      (NB: f_from x <> Time.bot \/ f_to x <> Time.bot), Time.lt (f_from x) (f_to x))
  (NIN: ~ In a acts)
  (DJ: forall l x (INx: In x acts) (Dx: dom l x) y (NEQ: x <> y)
                  (INy: In y acts) (Dy: dom l y),
         Interval.disjoint (f_from x, f_to x) (f_from y, f_to y)) : 
  exists f_from' f_to', 
    << F_FROM: forall b, In b acts -> f_from' b = f_from b >> /\
    << F_TO: forall b, In b acts -> f_to' b = f_to b >> /\
    << TWF: forall l x (Dx: dom l x) 
      (NB: f_from' x <> Time.bot \/ f_to' x <> Time.bot), Time.lt (f_from' x) (f_to' x) >> /\
    << MON': monotone mo f_to' >> /\
    << DJ' : forall l x (Dx: dom l x) y (NEQ: x <> y) (Dy: dom l y),
         Interval.disjoint (f_from' x, f_to' x) (f_from' y, f_to' y) >> /\ 
    << NADJ_L: forall y, mo y a -> f_to' y <> f_from' a >> /\
    << NADJ_R: forall y, mo a y -> f_to' a <> f_from' y >> /\
    << NBOT': Time.bot <> f_from' a >>.
Proof.
  edestruct find_free_interval2 as (from' & to' & K); eauto; desc.
  exists (upd f_from a from'), (upd f_to a to'); splits; simpls; rewrite ?upds; ins.
  - by ins; desf; desf; rewrite ?upds, ?updo; ins; intro; desf; eauto.
  - by ins; desf; desf; rewrite ?upds, ?updo; ins; intro; desf; eauto.
  - destruct (classic (x=a)) as [EQ|NEQ]; subst.
    by rewrite ?upds.
    destruct (ACT _ _ Dx).
    by exfalso; auto.
    by rewrite ?updo in *; eauto.
  - red; ins.
    exploit D; eauto; intro M; desc; generalize M, M0; ins; apply ACT in M; apply ACT in M0;
    desf; desf; rewrite ?upds, ?updo; eauto; subst; try intro; desf; desf;
    try solve [etransitivity; eauto | exfalso; eauto].
    eapply Time.lt_strorder.
    by eapply NEXT'; eauto.
    eapply WF; eauto; left.
    by intro X; eapply lt_bot;  rewrite <- X; eapply NEXT'; eauto.
  - ins; destruct (ACT _ _ Dx); desf; destruct (ACT _ _ Dy); desf;
      rewrite ?upds, ?updo; eauto; subst; try intro; desf; desf;
      eauto; ins; destruct LHS, RHS; ins; eauto;
    eapply TOT in NEQ; eauto;
    des; eapply Time.lt_strorder; 
         eauto using time_lt_trans, TimeFacts.le_lt_lt, TimeFacts.lt_le_lt. 
  - ins; desf; rewrite updo; try intro; desf; desf; eauto.
    exploit D; eauto; intro M; desc; apply ACT in M; desf; eauto.
    eapply Time.lt_strorder, PREV'; eauto. 
  - ins; desf; rewrite updo; try intro; desf; desf; eauto.
    exploit D; eauto; intro M; desc; apply ACT in M0; desf; eauto.
    eapply Time.lt_strorder, NEXT'; eauto. 
Qed.

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
  (WF_MO: WfMO acts mo) (SAME_F: f a = f b) : a=b.
Proof.
destruct (classic (a=b)) as [?|NEQ]; try done.
exfalso; eapply WF_MO in NEQ; eauto.
desf; apply MON in NEQ; rewrite SAME_F in NEQ; eapply Time.lt_strorder; eauto.
Qed.

Definition max_value f (INR : event -> Prop) val :=
 << UB: forall a (INa: INR a), Time.le (f a) val >> /\
 << MAX: ((forall a, ~ INR a) /\ val = Time.bot) \/
         (exists a_max, << INam: INR a_max >> /\ <<LB': Time.le val (f a_max)>>) >>.

Lemma max_value_singleton f b t (T: t = f b) : max_value f (eq b) t.
Proof.
red; splits; ins; desc; subst.
by apply Time.le_lteq; eauto.
right; exists b; splits; try apply Time.le_lteq; eauto.
Qed.

Lemma max_value_new_f f f' P t 
  (MAX: max_value f P t) (F: forall x, P x -> f' x = f x): max_value f' P t.
Proof.
unfold max_value in *; ins; desf; splits; ins.
all: try rewrite F; auto.
right; exists a_max; rewrite F; auto.
Qed.

Lemma max_value_same_set f P P' t 
  (MAX: max_value f P t) (SAME: forall x, P' x <-> P x): max_value f P' t.
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

Lemma max_value_empty f P (SAME: forall x, ~ P x): max_value f P Time.bot.
Proof.
red; splits.
ins; exfalso; eapply SAME; edone.
left; splits; eauto.
Qed.

Lemma max_value_le f b c tm l P
  (LE: Time.le (tm l) (f b))
  (MAX: max_value f P (LocFun.find l tm))
  (LT: Time.lt (f b) (f c))
  (IN: P c) : False.
Proof.
unfold LocFun.find in *.
red in MAX; desf.
eby eapply MAX0.
apply UB in IN.
eapply Time.lt_strorder; eauto using TimeFacts.le_lt_lt.
Qed.

Lemma max_value_lt f b tm l P t
  (LT1: Time.lt t (f b))
  (MAX: max_value f P (LocFun.find l tm))
  (LT2: Time.lt (tm l) t)
  (IN: P b) : False.
Proof.
unfold LocFun.find in *.
red in MAX; desf.
eby eapply MAX0.
apply UB in IN.
assert (Time.lt (tm l) (f b)).
  eapply Time.lt_strorder; eauto.
eapply Time.lt_strorder; eauto using TimeFacts.le_lt_lt.
Qed.

End Monotone.

Require Import Setoid Permutation.

Add Parametric Morphism : (monotone) with signature 
  same_relation ==> eq ==> iff as monotone_more.
Proof.
  unfold monotone, same_relation, NW; intuition; eauto. 
Qed.

Section Simulation.

Variables f_from f_to : event -> Time.t.

Variable acts : list event.
Variables sb rmw rf mo sc : relation event.

Definition sim_msg b  rel :=
  << UR: forall l, max_value f_to 
               (fun a => msg_rel urr acts sb rmw rf sc l a b \/
                         is_rlx_rw b /\ loc b = Some l /\ a = b) 
                             (LocFun.find l rel.(View.pln)) >> /\
  << RW: forall l, max_value f_to 
               (fun a => msg_rel rwr acts sb rmw rf sc l a b \/
                         is_rlx_rw b /\ loc b = Some l /\ a = b) 
                             (LocFun.find l rel.(View.rlx)) >>.

Definition sim_mem_helper b from v rel :=
  << VAL: Some v = (val b) >> /\
  << FROM: Time.lt from (f_to b) \/ 
    is_init b /\ from = Time.bot /\ (f_to b) = Time.bot >> /\ 
  << SIMMSG: sim_msg b rel >>.

Definition sim_mem mem :=
  forall l, 
    << DOM: forall b, (In b acts) /\ (is_write b) /\ (loc b = Some l) -> 
                Memory.get l (f_to b) mem <> None >> /\
    << SIMCELL: forall to from v rel 
                (CELL: Memory.get l to mem = Some (from, Message.mk v rel)),
                exists b, In b acts /\ is_write b /\ loc b = Some l 
                          /\ f_from b = from /\ f_to b = to /\
                          sim_mem_helper b from v rel.(View.unwrap) >> /\
    << UPDATES: forall a b (RF_RMW: (rf ;; rmw) a b) (LOC: loc a = Some l),
                exists m, Memory.get l (f_to b) mem = Some (f_to a, m) >>.

Definition sim_rel rel i :=
  << REL_UR: forall l' l, max_value f_to 
    (fun a => t_rel urr acts sb rmw rf sc i l' l a \/ 
            l = l' /\ In a acts /\ is_write a /\ loc a = Some l' /\ thread a = i)
    (LocFun.find l (LocFun.find l' rel).(View.pln)) >> /\
  << REL_RW: forall l' l, max_value f_to 
    (fun a => t_rel rwr acts sb rmw rf sc i l' l a \/ 
            l = l' /\ In a acts /\ is_write a /\ loc a = Some l' /\ thread a = i)
    (LocFun.find l (LocFun.find l' rel).(View.rlx)) >>.

Definition sim_cur cur i :=
  << CUR_UR: forall l, max_value f_to (t_cur urr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(View.pln)) >> /\
  << CUR_RW: forall l, max_value f_to (t_cur rwr acts sb rmw rf sc i l) 
    (LocFun.find l cur.(View.rlx)) >>.

Definition sim_acq acq i :=
  << ACQ_UR: forall l, max_value f_to (t_acq urr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(View.pln)) >> /\
  << ACQ_RW: forall l, max_value f_to (t_acq rwr acts sb rmw rf sc i l) 
    (LocFun.find l acq.(View.rlx)) >>.

Definition sim_tview tview i :=
  << CUR: sim_cur tview.(TView.cur) i >> /\
  << ACQ: sim_acq tview.(TView.acq) i >> /\
  << REL: sim_rel tview.(TView.rel) i >>.

End Simulation.

Definition sim_time (ths: Configuration.Threads.t) sc_map mem G f_from f_to :=
  << MONOTONE: monotone (mo G) f_to >> /\  
  << SIM_TVIEW: forall i foo local
        (TID: IdentMap.find i ths = Some (foo, local)),
        sim_tview f_to (acts G) (sb G) (rmw G) (rf G) (sc G) local.(Local.tview) (Some i) >> /\
  << SIM_SC_MAP: forall l, max_value f_to (S_tm (acts G) (sb G) (rmw G) (rf G) l) 
                                     (LocFun.find l sc_map)  >> /\
  << SIM_MEM: sim_mem f_from f_to (acts G) (sb G) (rmw G) (rf G) (sc G) mem >>.


Definition MGsim (op_st: Configuration.t) (ax_st: Machine.configuration) :=
  << COH: Coherent (acts (exec ax_st)) (sb (exec ax_st)) (rmw (exec ax_st)) 
    (rf (exec ax_st)) (mo (exec ax_st)) (sc (exec ax_st)) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << NO_PROMISES: forall i foo local 
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: (ts ax_st) = IdentMap.map fst (Configuration.threads op_st) >>/\
  exists f_from f_to, 
    << TIME: sim_time (Configuration.threads op_st)
     (Configuration.sc op_st) (Configuration.memory op_st) (exec ax_st) f_from f_to >> /\
    << SPACE : forall x y (MO: mo (exec ax_st) x y) (NRMW: ~ (rf (exec ax_st) ;; rmw (exec ax_st)) x y),
                 f_to x <> f_from y >> /\
    << BSPACE : forall y (INy: In y (acts (exec ax_st))) (W: is_write y) (P: is_proper y)
                       (NRMW: ~ exists x, (rf (exec ax_st) ;; rmw (exec ax_st)) x y),
                 Time.bot <> f_from y >>.

Definition GMsim op_st ax_st :=
  << COH: Coherent (acts (exec ax_st)) (sb (exec ax_st)) (rmw (exec ax_st)) 
    (rf (exec ax_st)) (mo (exec ax_st)) (sc (exec ax_st)) >> /\
  << WF_OP_ST: Configuration.wf op_st >> /\
  << NO_PROMISES: forall i foo local 
        (TID: IdentMap.find i (Configuration.threads op_st) = Some (foo, local)),
         local.(Local.promises) = Memory.bot>> /\
  << STATES: (ts ax_st) = IdentMap.map fst (Configuration.threads op_st) >>/\
  << TIME: exists f_from f_to, sim_time (Configuration.threads op_st)
     (Configuration.sc op_st) (Configuration.memory op_st) (exec ax_st) f_from f_to >>.

Lemma sim_mem_get :
  forall ffrom fto acts sb rmw rf mo sc mem 
    (MONOTONE: monotone mo fto) (WF: WfMO acts mo)
    (MEM : sim_mem ffrom fto acts sb rmw rf sc mem) 
    x l v (INx : In x acts) (WRITEx: is_write x) (LOCx: loc x = Some l)
(Valx: val x = Some v),
  exists rel, Memory.get l (fto x) mem = Some (ffrom x, Message.mk v rel) /\
                  (sim_mem_helper fto acts sb rmw rf sc x (ffrom x) v rel.(View.unwrap)).
Proof.
  ins; desc.
  assert (X:= proj1 (MEM l) x).
  destruct (Memory.get l (fto x) mem) as [[from [v' rel]]|] eqn:Y; cycle 1.
  by exfalso; apply X.
  apply (proj2 (MEM l)) in Y; desc.
  destruct (classic (x=b)); subst.
  - assert (v'=v); subst; eauto.
    by unfold sim_mem_helper in *; desc; congruence.
  - exfalso; eauto using monotone_injective.
Qed.

Lemma sim_mem_lt ffrom fto acts sb rmw rf mo sc mem
      (SIM_MEM : sim_mem ffrom fto acts sb rmw rf sc mem)
      (WF: Wf acts sb rmw rf mo sc)
      (MON: monotone mo fto)
      l x (IN : In x acts) (W: is_write x) (L: loc x = Some l) 
      (NBOT: ffrom x <> Time.bot \/ fto x <> Time.bot) :
    Time.lt (ffrom x) (fto x). 
Proof.
assert (exists v, val x = Some v); desc.
by destruct x as [??[]]; ins; exists v; unfold val; ins.
exploit sim_mem_get; try edone.
by eapply WF.
specialize (SIM_MEM l); desc.
intro G; desc.
unfold sim_mem_helper in *; apply SIMCELL in G; desf. 
Qed.

Lemma sim_mem_disj ffrom fto acts sb rmw rf mo sc mem
      (SIM_MEM : sim_mem ffrom fto acts sb rmw rf sc mem)
      (WF: Wf acts sb rmw rf mo sc)
      (MON: monotone mo fto)
      l x (INx: In x acts) (W: is_write x) (L: loc x = Some l) 
        y (NEQ: x <> y) (INy: In y acts) (W': is_write y) (L': loc y = Some l) :
  Interval.disjoint (ffrom x, fto x) (ffrom y, fto y).
Proof.
  ins; desc. cdes WF.
  assert (exists v_y, val y = Some v_y); desc.
    by destruct y as [??[]]; unfold val; ins; eauto.
  assert (exists v_x, val x = Some v_x); desc.
    by destruct x as [??[]]; unfold val; ins; eauto.
  assert (Gx := INx); eapply sim_mem_get in Gx; eauto; 
  assert (Gy := INy); eapply sim_mem_get in Gy; eauto; desc.
  unfold Memory.get, Cell.get in *; destruct (mem l); ins.
  eapply WF0; eauto. 
  intro M.
  cdes WF; eapply WF_MO in NEQ; des; splits; try eassumption;
  apply MON in NEQ; rewrite M in *; eapply Time.lt_strorder; eauto.
Qed.

(******************************************************************************)
(** * Simple helper Lemmas for timemaps and views         *)
(******************************************************************************)
Lemma tm_join a b l :
  TimeMap.join a b l =  Time.join (a l) (b l).
Proof.  ins. Qed.

Lemma tm_find_join l a b :
  LocFun.find l (TimeMap.join a b) = 
  Time.join (LocFun.find l a) (LocFun.find l b).
Proof.  done. Qed.

Lemma tm_find_singleton l l' t :
  LocFun.find l (TimeMap.singleton l' t) = 
    if (Loc.eq_dec l l') then t else Time.bot.
Proof.  desf. Qed.

Lemma tm_singleton l t : TimeMap.singleton l t l = t.
Proof.  apply Loc.eq_dec_eq; done. Qed.

Lemma time_join_bot a : Time.join a Time.bot =  a.
Proof.
  unfold Time.join; desf.
  rewrite Time.le_lteq in *; desf.
  exfalso; eapply Time.lt_strorder.
  eauto using TimeFacts.lt_le_lt, Time.bot_spec.
Qed.

Lemma tm_find_bot l : LocFun.find l TimeMap.bot = Time.bot.
Proof. done. Qed.

Lemma tm_join_bot a : TimeMap.join a TimeMap.bot =  a.
Proof.
eapply TimeMap.antisym.
apply TimeMap.join_spec.
apply TimeMap.le_PreOrder.
apply TimeMap.bot_spec.
apply TimeMap.join_l.
Qed.

Lemma cap_join_bot a : View.join a View.bot =  a.
Proof.
eapply View.antisym.
apply View.join_spec.
apply View.le_PreOrder.
apply View.bot_spec.
apply View.join_l.
Qed.

