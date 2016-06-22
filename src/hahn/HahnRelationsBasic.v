(******************************************************************************)
(** * Basic properties of relations *)
(******************************************************************************)

Require Import HahnBase HahnList.
Require Import Classical NPeano Omega Permutation List Setoid.
Require Export Relations.

Set Implicit Arguments.

(* Database of lemmas *)
Create HintDb rel discriminated. 


(** Definitions of relations *)
(******************************************************************************)

(* Make arguments implicit *)
Arguments clos_trans [A] R x y.
Arguments clos_refl_trans [A] R x y.
Arguments union [A] R1 R2 x y.
Arguments reflexive [A] R.
Arguments symmetric [A] R.
Arguments transitive [A] R.
Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.

Section RelDefs.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables rel rel' : relation A.
  Variables a b : A.

  Definition immediate :=
    rel a b /\ (forall c (R1: rel a c) (R2: rel c b), False).

  Definition irreflexive := forall x, rel x x -> False.

  Definition is_total X (cond: X -> Prop) (rel: relation X) :=
    forall a (IWa: cond a)
           b (IWb: cond b) (NEQ: a <> b),
      rel a b \/ rel b a.

  Definition restr_subset :=
    forall a (IWa: cond a)
           b (IWb: cond b) (REL: rel a b),
      rel' a b.

  Definition upward_closed (P: A -> Prop) :=
    forall x y (REL: rel x y) (POST: P y), P x.

  Definition singl_rel : relation A := fun x y => x = a /\ y = b.

  Definition inter_rel : relation A := fun x y => rel x y /\ rel' x y.

  Definition eq_rel : relation A := fun x y => f x = f y.

  Definition eqv_rel : relation A := fun x y => x = y /\ cond x.

  Definition eqv_dom_rel dom : relation A := 
    fun x y => x = y /\ In x dom.

  Definition restr_rel : relation A := 
    fun x y => rel x y /\ cond x /\ cond y.

  Definition restr_eq_rel : relation A :=
    fun x y => rel x y /\ f x = f y.

  Definition seq : relation A :=
  fun x y => exists z, rel x z /\ rel' z y.

  Definition clos_refl : relation A := fun x y => x = y \/ rel x y.

  Definition dom_rel := fun x => exists y, rel x y.
  Definition codom_rel := fun y => exists x, rel x y.

  Definition restr_dom := fun x y => rel x y /\ cond y.
  Definition restr_codom := fun x y => rel x y /\ cond y.

End RelDefs.

Definition acyclic A (rel: relation A) := irreflexive (clos_trans rel).

Notation "P +++ Q" := (union P Q) (at level 50, left associativity).
Notation "P ;; Q" := (seq P Q) (at level 45, right associativity).
Notation "a <--> b" := (same_relation a b)  (at level 110).
Notation "<| a |>" := (eqv_rel a).


(** Very basic properties of relations *)
(******************************************************************************)

Lemma r_refl A (R: relation A) x : clos_refl R x x.
Proof. vauto. Qed.

Lemma r_step A (R: relation A) x y : R x y -> clos_refl R x y.
Proof. vauto. Qed.

Hint Immediate r_refl r_step.

Section BasicProperties.

Variables A B : Type.
Variable dom : A -> Prop.
Variable f: A -> B.
Variables r r' r'' : relation A.

Lemma clos_trans_mon a b :
  clos_trans r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_trans r' a b.
Proof.
  induction 1; ins; eauto using clos_trans.
Qed.

Lemma clos_refl_trans_mon a b :
  clos_refl_trans r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_refl_trans r' a b.
Proof.
  induction 1; ins; eauto using clos_refl_trans.
Qed.

Lemma clos_refl_transE a b :
  clos_refl_trans r a b <-> a = b \/ clos_trans r a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto. 
Qed.

Lemma clos_trans_in_rt a b :
  clos_trans r a b -> clos_refl_trans r a b.
Proof.
  induction 1; vauto. 
Qed.

Lemma rt_t_trans a b c :
  clos_refl_trans r a b -> clos_trans r b c -> clos_trans r a c.
Proof.
  ins; induction H; eauto using clos_trans. 
Qed.

Lemma t_rt_trans a b c :
  clos_trans r a b -> clos_refl_trans r b c -> clos_trans r a c.
Proof.
  ins; induction H0; eauto using clos_trans. 
Qed.

Lemma t_step_rt x y : 
  clos_trans r x y <-> exists z, r x z /\ clos_refl_trans r z y.
Proof.
  split; ins; desf.
    by apply clos_trans_tn1 in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma t_rt_step x y : 
  clos_trans r x y <-> exists z, clos_refl_trans r x z /\ r z y.
Proof.
  split; ins; desf.
    by apply clos_trans_t1n in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma clos_trans_of_transitive (T: transitive r) x y : 
  clos_trans r x y -> r x y.
Proof.
  induction 1; eauto.
Qed.

Lemma ct_of_transitive (T: transitive r) x y :
  clos_trans r x y <-> r x y.
Proof.
  by split; ins; eauto using t_step; eapply clos_trans_of_transitive.
Qed.

Lemma crt_of_transitive (T: transitive r) x y :
  clos_refl_trans r x y <-> clos_refl r x y.
Proof.
  by ins; rewrite clos_refl_transE, ct_of_transitive; ins. 
Qed.

Lemma clos_trans_eq :
  forall B (f : A -> B) 
    (H: forall a b (SB: r a b), f a = f b) a b
    (C: clos_trans r a b),
  f a = f b.
Proof.
  ins; induction C; eauto; congruence.
Qed.

Lemma trans_irr_acyclic : 
  irreflexive r -> transitive r -> acyclic r.
Proof.
  eby repeat red; ins; eapply H, clos_trans_of_transitive. 
Qed.

Lemma cr_trans :
  transitive r -> transitive (clos_refl r).
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma restr_rel_trans :
  transitive r -> transitive (restr_rel dom r).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma is_total_restr :
  is_total dom r ->
  is_total dom (restr_rel dom r).
Proof.
  red; ins; eapply H in NEQ; eauto; desf; vauto.
Qed.

Lemma clos_trans_restrD x y :
  clos_trans (restr_rel dom r) x y -> dom x /\ dom y.
Proof.
  unfold restr_rel; induction 1; ins; desf. 
Qed.

Lemma clos_trans_restr_eqD x y : 
  clos_trans (restr_eq_rel f r) x y -> f x = f y.
Proof.
  unfold restr_eq_rel; induction 1; ins; desf; congruence. 
Qed.

Lemma irreflexive_inclusion:
  inclusion r r' ->
  irreflexive r' ->
  irreflexive r.
Proof.
  unfold irreflexive, inclusion; eauto.
Qed.

Lemma irreflexive_union :
  irreflexive (r +++ r') <-> irreflexive r /\ irreflexive r'.
Proof.
  unfold irreflexive, union; repeat split; 
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_seqC :
  irreflexive (r ;; r') <-> irreflexive (r' ;; r).
Proof.
  unfold irreflexive, seq; repeat split; 
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_restr :
  irreflexive r -> irreflexive (restr_rel dom r).
Proof.
  unfold irreflexive, restr_rel; ins; desf; eauto. 
Qed.

Lemma inclusion_acyclic :
  inclusion r r' ->
  acyclic r' ->
  acyclic r.
Proof.
  repeat red; ins; eapply H0, clos_trans_mon; eauto.
Qed.

Lemma ct_trans : transitive (clos_trans r).
Proof. vauto. Qed.

Lemma crt_trans : transitive (clos_refl_trans r).
Proof. vauto. Qed.

Lemma crt_refl : reflexive (clos_refl_trans r).
Proof. vauto. Qed.

Lemma restr_eq_trans :
  transitive r -> transitive (restr_eq_rel f r). 
Proof.
  unfold transitive, restr_eq_rel; ins; desf; split; eauto; congruence.
Qed.

Lemma irreflexive_restr_eq :
  irreflexive (restr_eq_rel f r) <-> irreflexive r.
Proof.
  unfold irreflexive, restr_eq_rel; split; ins; desf; eauto. 
Qed.

Lemma upward_closed_seq P :
  upward_closed r P ->
  upward_closed r' P ->
  upward_closed (r ;; r') P.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma upward_closed_ct P :
  upward_closed r P -> upward_closed (clos_trans r) P.
Proof.
  induction 2; eauto.
Qed.

Lemma upward_closed_rt P :
  upward_closed r P -> upward_closed (clos_refl_trans r) P.
Proof.
  induction 2; eauto.
Qed.

(** Lemmas about inclusion *)
(******************************************************************************)

Lemma inclusion_refl : reflexive (@inclusion A).
Proof. repeat red; ins. Qed.

Lemma inclusion_trans : transitive (@inclusion A).
Proof. repeat red; eauto. Qed.

Lemma inclusion_refl2 : inclusion r r.
Proof. done. Qed.

Lemma same_relation_refl2 : r <--> r.
Proof. split; ins. Qed.

Lemma inclusion_union_r1 : inclusion r (r +++ r').
Proof. vauto. Qed.

Lemma inclusion_union_r2 : inclusion r' (r +++ r').
Proof. vauto. Qed.

Lemma inclusion_union_l :
  inclusion r r'' ->
  inclusion r' r'' ->
  inclusion (r +++ r') r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r :
  inclusion r r' \/ inclusion r r'' ->
  inclusion r (r' +++ r'').
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_mon s s' :
  inclusion r r' -> 
  inclusion s s' -> 
  inclusion (r +++ s) (r' +++ s').
Proof.
  unfold inclusion, union; ins; desf; eauto.
Qed.

Lemma inclusion_seq_mon s s' :
  inclusion r r' -> 
  inclusion s s' -> 
  inclusion (r ;; s) (r' ;; s').
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma inclusion_seq_refl :
  inclusion r r'' ->
  inclusion r' r'' ->
  transitive r'' ->
  inclusion (r ;; clos_refl r') r''.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma inclusion_restr :
  inclusion (restr_rel dom r) r.
Proof.
  unfold inclusion, restr_rel; ins; desf.
Qed.

Lemma inclusion_restr_rel_l :
  inclusion r r' ->
  inclusion (restr_rel dom r) r'.
Proof.
  unfold inclusion, seq, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_restr_eq :
  inclusion (restr_eq_rel f r) r.
Proof.
  unfold restr_eq_rel, inclusion; ins; desf.
Qed.

Lemma inclusion_restr_eq_l :
  inclusion r r' ->
  inclusion (restr_eq_rel f r) r'.
Proof.
  unfold inclusion, seq, restr_eq_rel; ins; desf; eauto.
Qed.

(** Inclusions involving transitive closure. *)

Lemma inclusion_step_t : 
  inclusion r r' ->
  inclusion r (clos_trans r').
Proof.
  unfold seq; red; ins; desf; eauto using t_step.
Qed.

Lemma inclusion_t_rt :
  inclusion (clos_trans r) (clos_refl_trans r).
Proof.
  by red; ins; apply clos_trans_in_rt.
Qed.

Lemma inclusion_t_t :
  inclusion r r' ->
  inclusion (clos_trans r) (clos_trans r').
Proof.
  by red; ins; eapply clos_trans_mon. 
Qed.

Lemma inclusion_t_t2 :
  inclusion r (clos_trans r') ->
  inclusion (clos_trans r) (clos_trans r').
Proof.
  induction 2; eauto using clos_trans.
Qed.

Lemma inclusion_t_ind :
  inclusion r r' ->
  transitive r' ->
  inclusion (clos_trans r) r'.
Proof. unfold seq; induction 3; eauto. Qed.

Lemma inclusion_t_ind_left :
  inclusion r r' ->
  inclusion (r ;; r') r' ->
  inclusion (clos_trans r) r'.
Proof. 
  unfold seq, inclusion; ins.
  apply clos_trans_t1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_t_ind_right :
  inclusion r r' ->
  inclusion (r' ;; r) r' ->
  inclusion (clos_trans r) r'.
Proof. 
  unfold seq, inclusion; ins.
  apply clos_trans_tn1 in H1; induction H1; eauto.
Qed.

(** Inclusions involving reflexive-transitive closure. *)

Lemma inclusion_id_rt :
  inclusion (eqv_rel (fun _ => True)) (clos_refl_trans r').
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_step_rt : 
  inclusion r r' ->
  inclusion r (clos_refl_trans r').
Proof.
  unfold seq; red; ins; desf; eauto using rt_step.
Qed.

Lemma inclusion_r_rt : 
  inclusion r r' ->
  inclusion (clos_refl r) (clos_refl_trans r').
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto using rt_step, rt_refl.
Qed.

Lemma inclusion_rt_rt : 
  inclusion r r' ->
  inclusion (clos_refl_trans r) (clos_refl_trans r').
Proof.
  red; ins; eapply clos_refl_trans_mon; eauto. 
Qed.

Lemma inclusion_rt_rt2 :
  inclusion r (clos_refl_trans r') ->
  inclusion (clos_refl_trans r) (clos_refl_trans r').
Proof.
  induction 2; eauto using clos_refl_trans.
Qed.

Lemma inclusion_rt_ind :
  reflexive r' ->
  inclusion r r' ->
  transitive r' ->
  inclusion (clos_refl_trans r) r'.
Proof. unfold seq, eqv_rel; induction 4; eauto. Qed.

Lemma inclusion_rt_ind_left :
  reflexive r' ->
  inclusion (r ;; r') r' ->
  inclusion (clos_refl_trans r) r'.
Proof. 
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rt1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_rt_ind_right :
  reflexive r' ->
  inclusion (r' ;; r) r' ->
  inclusion (clos_refl_trans r) r'.
Proof. 
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rtn1 in H1; induction H1; eauto.
Qed.

Lemma inclusion_seq_trans t : 
  transitive t ->
  inclusion r t ->
  inclusion r' t ->
  inclusion (r ;; r') t.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma inclusion_seq_rt :
  inclusion r (clos_refl_trans r'') ->
  inclusion r' (clos_refl_trans r'') ->
  inclusion (r ;; r') (clos_refl_trans r'').
Proof. 
  unfold seq; red; ins; desf; eapply rt_trans; eauto. 
Qed.

End BasicProperties.


Hint Resolve same_relation_refl2.

Hint Resolve
     inclusion_refl2 same_relation_refl2
     inclusion_union_r1 inclusion_union_r2 
     inclusion_union_l inclusion_union_r
     inclusion_seq_mon 
     inclusion_restr_eq_l inclusion_restr_rel_l 
  : rel.

Hint Resolve 
     inclusion_step_t inclusion_t_t inclusion_t_ind inclusion_rt_rt 
     inclusion_r_rt inclusion_step_rt : rel.

Hint Resolve inclusion_acyclic : rel.

Hint Immediate crt_trans crt_refl ct_trans inclusion_t_rt : rel.

Lemma clos_trans_of_clos_trans A (r : relation A) x y :
  clos_trans (clos_trans r) x y <->
  clos_trans r x y.
Proof.
  apply ct_of_transitive; vauto.
Qed.


Lemma clos_trans_of_clos_trans1 A (r r' : relation A) x y :
  clos_trans (fun a b => clos_trans r a b \/ r' a b) x y <->
  clos_trans (fun a b => r a b \/ r' a b) x y.
Proof.
  split; induction 1; desf; 
  eauto using clos_trans, clos_trans_mon.
Qed.



(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

(** First, for inclusion. *)

Add Parametric Relation (X : Type) : (relation X) (@inclusion X) 
 reflexivity proved by (@inclusion_refl _)
 transitivity proved by (@inclusion_trans _)
 as inclusion_rel.

Add Parametric Morphism X : (@inclusion X) with signature 
  inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof.
  unfold inclusion, Basics.impl; ins; eauto. 
Qed.

Add Parametric Morphism X : (@union X) with signature 
  inclusion ==> inclusion ==> inclusion as union_mori.
Proof.
  unfold inclusion, union; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature 
  inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof.
  unfold inclusion, inter_rel; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@seq X) with signature 
  inclusion ==> inclusion ==> inclusion as seq_mori.
Proof.
  unfold inclusion, seq; intuition; desf; eauto. 
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature 
  inclusion --> Basics.impl as irreflexive_mori.
Proof.
  unfold inclusion, irreflexive, Basics.impl; intuition; desf; eauto. 
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature 
  inclusion ==> inclusion as clos_trans_mori.
Proof.
  unfold inclusion; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature 
  inclusion ==> inclusion as clos_refl_trans_mori.
Proof.
  unfold inclusion; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature 
  inclusion ==> inclusion as clos_refl_mori.
Proof.
  unfold inclusion, clos_refl; intuition; eauto.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature 
  inclusion ==> inclusion as restr_rel_mori.
Proof.
  unfold inclusion, restr_rel; intuition; eauto. 
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature 
  eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof.
  unfold inclusion, restr_eq_rel; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@acyclic X) with signature 
  inclusion --> Basics.impl as acyclic_mori.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity. 
Qed.

Add Parametric Morphism X : (@is_total X) with signature 
  eq ==> inclusion ==> Basics.impl as is_total_mori.
Proof.
  unfold inclusion, is_total, Basics.impl; ins; desf. 
  eapply H0 in NEQ; desf; eauto.
Qed.

(** Second, for equivalence. *)

Lemma same_relation_exp A (r r' : relation A) (EQ: r <--> r') :
  forall x y, r x y <-> r' x y.
Proof. split; apply EQ. Qed.

Lemma same_relation_refl A : reflexive (@same_relation A).
Proof. split; ins. Qed.


Lemma same_relation_sym A : symmetric (@same_relation A).
Proof. unfold same_relation; split; ins; desf. Qed.

Lemma same_relation_trans A : transitive (@same_relation A).
Proof. unfold same_relation; split; ins; desf; red; eauto. Qed.

Add Parametric Relation (X : Type) : (relation X) (@same_relation X) 
 reflexivity proved by (@same_relation_refl X)
 symmetry proved by (@same_relation_sym X)
 transitivity proved by (@same_relation_trans X)
 as same_rel.

Add Parametric Morphism X : (@inclusion X) with signature 
  same_relation ==> same_relation ==> iff as inclusion_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@union X) with signature 
  same_relation ==> same_relation ==> same_relation as union_more.
Proof.
  unfold same_relation, union; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature 
  same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof.
  unfold same_relation, inter_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@seq X) with signature 
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof.
  unfold same_relation, seq; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@eqv_dom_rel X) with signature 
  (@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof.
  by unfold same_relation, eqv_dom_rel; ins; desf; split; red; ins; desf; 
     rewrite H in *. 
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature 
  same_relation ==> same_relation as restr_rel_more.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature 
  eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof.
  unfold same_relation, restr_eq_rel; intuition; eauto using restr_eq_rel_mori. 
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature 
  same_relation ==> same_relation as clos_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature 
  same_relation ==> same_relation as clos_relf_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; 
  eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature 
  same_relation ==> same_relation as clos_relf_more.
Proof.
  unfold same_relation, clos_refl; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature 
  same_relation ==> iff as irreflexive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@acyclic X) with signature 
  same_relation ==> iff as acyclic_more.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism X : (@transitive X) with signature 
  same_relation ==> iff as transitive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature 
  same_relation ==> eq ==> eq ==> iff as clos_trans_more'.
Proof.
  unfold same_relation; ins; desf; split; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature 
  same_relation ==> eq ==> eq ==> iff as clos_refl_trans_more'.
Proof.
  unfold same_relation; ins; desf; split; ins; desf; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@is_total X) with signature 
  eq ==> same_relation ==> iff as is_total_more.
Proof.
  unfold is_total, same_relation; split; ins; eapply H0 in NEQ; desf; eauto.
Qed.

Lemma same_relation_restr X (f : X -> Prop) rel rel' :
   (forall x (CONDx: f x) y (CONDy: f y), rel x y <-> rel' x y) ->
   (restr_rel f rel <--> restr_rel f rel').
Proof.
  unfold restr_rel; split; red; ins; desf; rewrite H in *; eauto.
Qed.

Lemma union_restr X (f : X -> Prop) rel rel' :
  union (restr_rel f rel) (restr_rel f rel')
  <--> restr_rel f (union rel rel').
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
Qed.

Lemma clos_trans_restr X (f : X -> Prop) rel (UC: upward_closed rel f) :
  clos_trans (restr_rel f rel) 
  <--> restr_rel f (clos_trans rel).
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
    split; [|by apply clos_trans_restrD in H].
    by eapply clos_trans_mon; eauto; unfold restr_rel; ins; desf.
  clear H0; apply clos_trans_tn1 in H.
  induction H; eauto 10 using clos_trans.
Qed.

Lemma seq_union_l X (r1 r2 r : relation X) :
  seq (union r1 r2) r <--> union (seq r1 r) (seq r2 r). 
Proof.
  unfold seq, union; split; red; ins; desf; eauto. 
Qed.

Lemma seq_union_r X (r r1 r2 : relation X) :
  seq r (union r1 r2) <--> union (seq r r1) (seq r r2). 
Proof.
  unfold seq, union; split; red; ins; desf; eauto. 
Qed.

Lemma seqA X (r1 r2 r3 : relation X) :
  seq (seq r1 r2) r3 <--> seq r1 (seq r2 r3).
Proof.
  unfold seq, union; split; red; ins; desf; eauto. 
Qed.

Lemma unionA X (r1 r2 r3 : relation X) :
  union (union r1 r2) r3 <--> union r1 (union r2 r3).
Proof.
  unfold seq, union; split; red; ins; desf; eauto. 
Qed.

Lemma unionC X (r1 r2 : relation X) :
  union r1 r2 <--> union r2 r1.
Proof.
  unfold seq, union; split; red; ins; desf; eauto. 
Qed.

Lemma unionAC A (r r' r'' : relation A) :
  r +++ (r' +++ r'') <--> r' +++ (r +++ r'').
Proof.
  rewrite <- !unionA, (unionC r r'); vauto.
Qed.

Lemma unionK A (r : relation A) :
  r +++ r <--> r.
Proof.
  split; eauto with rel.
Qed.

Lemma rtE_left X (r r' : relation X) :
  r ;; clos_refl_trans r' <--> r +++ ((r ;; r') ;; clos_refl_trans r').
Proof.
  split; unfold union, seq, inclusion; ins; desf; eauto using clos_refl_trans. 
  rewrite clos_refl_transE, t_step_rt in *; desf; eauto 8.
Qed.

Lemma rtE_right X (r r' : relation X) :
  clos_refl_trans r' ;; r <--> r +++ (clos_refl_trans r' ;; r' ;; r).
Proof.
  split; unfold union, seq, inclusion; ins; desf; eauto using clos_refl_trans. 
  rewrite clos_refl_transE, t_rt_step in *; desf; eauto 8.
Qed.

Lemma t_step_rt2 X (r : relation X) :
  clos_trans r <--> r ;; clos_refl_trans r.
Proof.
  split; unfold seq, inclusion; ins; rewrite t_step_rt in *; ins.
Qed.

Lemma seqFr X (r : relation X) :
  (fun _ _ => False) ;; r <--> (fun _ _ => False).
Proof.
  split; unfold seq, inclusion; ins; desf. 
Qed.

Lemma seqrF X (r : relation X) :
  r ;; (fun _ _ => False) <--> (fun _ _ => False).
Proof.
  split; unfold seq, inclusion; ins; desf. 
Qed.

Lemma unionrF X (r : relation X) :
  r +++ (fun _ _ => False) <--> r.
Proof.
  split; unfold union, inclusion; ins; desf; eauto.
Qed.

Lemma unionFr X (r : relation X) :
  (fun _ _ => False) +++ r <--> r.
Proof.
  split; unfold union, inclusion; ins; desf; eauto.
Qed.

Lemma crt_seq_swap X (r r' : relation X) :
  clos_refl_trans (r ;; r') ;; r <-->
  r ;; clos_refl_trans (r' ;; r).
Proof.
  split; ins; unfold seq; red; ins; desf.

  revert y H0; rename H into J; apply clos_rt_rtn1 in J.
  induction J; desf; eauto using rt_refl.
  ins; eapply IHJ in H; desf; eauto 10 using clos_refl_trans.

  revert x H; rename H0 into J; apply clos_rt_rt1n in J.
  induction J; desf; eauto using rt_refl.
  ins; eapply IHJ in H0; desf; eauto 10 using clos_refl_trans.
Qed.

Lemma crt_double X (r : relation X) :
  clos_refl_trans r <-->
  clos_refl r ;; clos_refl_trans (r ;; r).
Proof.
  unfold seq, clos_refl; split; red; ins; desc.
  rename H into J; apply clos_rt_rt1n in J; induction J; desf;
  eauto 8 using clos_refl_trans.
  eapply rt_trans with z; [desf; vauto|clear H];
  induction H0; desf; vauto.
Qed.


Lemma seq_id_l A (rel: relation A) : 
   eqv_rel (fun _ => True) ;; rel <--> rel.
Proof.
  unfold eqv_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_id_r A (rel: relation A) : 
   rel ;; eqv_rel (fun _ => True) <--> rel.
Proof.
  unfold eqv_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_eqvK A (dom : A -> Prop) :
  eqv_rel dom ;; eqv_rel dom <--> eqv_rel dom.
Proof.
  unfold eqv_rel, seq; split; red; ins; desf; eauto.
Qed.

Hint Rewrite seqFr seqrF unionrF unionFr unionK : rel.
Hint Rewrite seq_id_l seq_id_r seq_eqvK : rel.

Ltac rel_simpl :=
  repeat first [rewrite seqFr | rewrite seqrF | 
                rewrite unionFr | rewrite unionrF |
                rewrite seq_id_l|rewrite seq_id_r|
                rewrite seq_union_l|rewrite seq_union_r];
    eauto 8 with rel.

Lemma seq_eqv_r A (rel : relation A) dom : 
  rel ;; eqv_rel dom <--> (fun x y => rel x y /\ dom y). 
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma seq_eqv_l A (rel : relation A) dom : 
  eqv_rel dom ;; rel <--> (fun x y => dom x /\ rel x y). 
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_l A (rel : relation A) dom : 
  inclusion (eqv_rel dom ;; rel) rel.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_r A (rel : relation A) dom : 
  inclusion (rel ;; eqv_rel dom) rel.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma ct_begin A (rel : relation A) : 
  clos_trans rel <--> rel ;; clos_refl_trans rel.
Proof.
  unfold seq; split; red; ins; desf; rewrite t_step_rt in *; eauto.
Qed.

Lemma ct_end A (rel : relation A) : 
  clos_trans rel <--> clos_refl_trans rel ;; rel.
Proof.
  unfold seq; split; red; ins; desf; rewrite t_rt_step in *; eauto.
Qed.

Lemma rt_rt A (rel : relation A) : 
  clos_refl_trans rel ;; clos_refl_trans rel <--> clos_refl_trans rel.
Proof.
  unfold seq; split; red; ins; desf; eauto using rt_trans, rt_refl. 
Qed.

Lemma rt_ct A (rel : relation A) : 
  clos_refl_trans rel ;; clos_trans rel <--> clos_trans rel.
Proof.
  unfold seq; split; red; ins; desf; eauto using rt_t_trans, rt_refl. 
Qed.

Lemma ct_rt A (rel : relation A) : 
  clos_trans rel ;; clos_refl_trans rel <--> clos_trans rel.
Proof.
  unfold seq; split; red; ins; desf; eauto using t_rt_trans, rt_refl. 
Qed.

Lemma ct_ct A (rel : relation A) : 
  inclusion (clos_trans rel ;; clos_trans rel) (clos_trans rel).
Proof.
  unfold seq; red; ins; desf; eauto using t_trans.
Qed.

Lemma ct_of_ct A (rel : relation A) :
  clos_trans (clos_trans rel) <--> clos_trans rel. 
Proof.
  split; eauto with rel.
Qed.

Lemma rt_of_ct A (rel : relation A) :
  clos_refl_trans (clos_trans rel) <--> clos_refl_trans rel. 
Proof.
  split; eauto using inclusion_rt_rt2 with rel.
Qed.

Lemma ct_of_trans A (r: relation A) (T: transitive r) :
  clos_trans r <--> r.
Proof.
  split; eauto with rel. 
Qed.

Lemma crtE A (r: relation A) :
  clos_refl_trans r <--> eqv_rel (fun _ => True) +++ clos_trans r.
Proof.
  unfold eqv_rel, union, same_relation, inclusion.
  split; ins; rewrite clos_refl_transE in *; tauto.
Qed.

Lemma crE A (r: relation A) :
  clos_refl r <--> eqv_rel (fun _ => True) +++ r.
Proof.
  unfold eqv_rel, union, same_relation, inclusion, clos_refl.
  split; ins; tauto.
Qed.

Lemma crt_of_trans A (r: relation A) (T: transitive r) :
  clos_refl_trans r <--> clos_refl r.
Proof.
  rewrite crtE, crE, ct_of_trans; vauto.
Qed.

Lemma cr_of_t A (rel : relation A) :
  clos_refl (clos_trans rel) <--> clos_refl_trans rel. 
Proof.
  rewrite <- crt_of_trans, rt_of_ct; vauto.
Qed.

Lemma crt_begin A (rel : relation A) : 
  clos_refl_trans rel <--> eqv_rel (fun _ => True) +++ rel ;; clos_refl_trans rel.
Proof.
  rewrite <- ct_begin, <- crtE; vauto. 
Qed.

Lemma crt_end A (rel : relation A) : 
  clos_refl_trans rel <--> eqv_rel (fun _ => True) +++ clos_refl_trans rel ;; rel.
Proof.
  rewrite <- ct_end, <- crtE; vauto. 
Qed.

Lemma restr_eq_union:
  forall (X : Type) (rel rel' : relation X) (B : Type) (f : X -> B),
  restr_eq_rel f (rel +++ rel') <--> 
  restr_eq_rel f rel +++ restr_eq_rel f rel'.
Proof.
  unfold restr_eq_rel, union, same_relation, inclusion; intuition.
Qed.

Lemma restr_eq_elim : 
  forall X (rel : relation X) B (f: X -> B)
         (R: forall x y, rel x y -> f x = f y),
   restr_eq_rel f rel <--> rel.
Proof.
  unfold restr_eq_rel; split; red; ins; intuition.
Qed.

Lemma restr_eq_seq_eqv_rel X (rel : relation X) (B : Type) (f : X -> B) dom :
  restr_eq_rel f (rel ;; eqv_rel dom) <--> 
  restr_eq_rel f rel ;; eqv_rel dom.
Proof.
  ins; rewrite !seq_eqv_r; unfold restr_eq_rel.
  split; red; ins; desf.
Qed.

Lemma clos_refl_union1 X (rel rel' : relation X) :
  clos_refl (rel +++ rel') <--> clos_refl rel +++ rel'.
Proof.
  by rewrite !crE, unionA.
Qed.


Lemma acyclic_mon X (rel rel' : relation X) :
  acyclic rel -> inclusion rel' rel -> acyclic rel'.
Proof.
  eby repeat red; ins; eapply H, clos_trans_mon.
Qed.


(** Misc properties *)
(******************************************************************************)


Lemma clos_trans_imm :
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive R) L (ND: NoDup L) a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans (immediate R) a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (R a x /\ R x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
    exploit (D c); eauto; intro; desf; exfalso; eauto.
Qed.



Lemma clos_trans_rotl A (r r' : relation A) :
  clos_trans (r ;; r') <--> r ;; clos_refl_trans (r' ;; r) ;; r'.
Proof.
  split; red; ins; unfold seq in *; desf.
    by induction H; desf; eauto 10 using clos_refl_trans.
  cut (exists m, clos_refl_trans (r ;; r') x m /\ r m z0); unfold seq in *.
    by ins; desf; eapply t_rt_step; eauto.
  clear H1; induction H0 using clos_refl_trans_ind_left; desf; 
  eauto 8 using clos_refl_trans.
Qed.

Lemma acyclic_rotl A (r r' : relation A) :
  acyclic (r ;; r') <-> acyclic (r' ;; r).
Proof.
  unfold acyclic; rewrite clos_trans_rotl.
  unfold irreflexive, seq; ins; desf; intuition; desf; [|eapply H]; 
    rewrite t_rt_step in *; desf; eauto 10.
Qed.


Lemma immediate_clos_trans_elim A (r : relation A) a b : 
  immediate (clos_trans r) a b ->
  r a b /\ (forall c, clos_trans r a c -> clos_trans r c b -> False).
Proof.
  unfold immediate; ins; desf; split; ins.
  apply t_step_rt in H; desf.
  apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
  clos_trans (immediate r) a b -> r a b.
Proof.
  unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
      (T: transitive r) (IRR: irreflexive r) dom
      (D: forall a b (R: r a b), In b dom) a b :
  r a b ->
  clos_trans (immediate r) a b.
Proof.
  assert (D': forall c, r a c -> r c b -> In c dom).
    by ins; apply D in H; desf.
  clear D; revert a b D'.
  remember (length dom) as n; revert dom Heqn; induction n.
    by destruct dom; ins; vauto.
  ins; destruct (classic (exists c, r a c /\ r c b)); desf.
  2: by eapply t_step; split; ins; eauto.
  exploit D'; eauto; intro X; apply in_split in X; desf.
  rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
  apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins; exploit (D' c0); eauto;
  rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma clos_trans_imm2 :
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive R) L a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans (immediate R) a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup L); ins;
  try rewrite in_undup_iff; eauto using nodup_undup.
Qed.


Lemma total_immediate_unique:
  forall X (rel: X -> X -> Prop) (P: X -> Prop)
         (Tot: is_total P rel)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate rel a c)
         (ibc: immediate rel b c),
    a = b.
Proof.
  ins; destruct (classic (a = b)) as [|N]; eauto.
  exfalso; unfold immediate in *; desf.
  eapply Tot in N; eauto; desf; eauto.
Qed.



Lemma acyclic_case_split A (R : relation A) f :
  acyclic R <->
  acyclic (restr_rel f R) /\ (forall x (NEG: ~ f x) (CYC: clos_trans R x x), False).
Proof.
  unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
    by eapply H, clos_trans_mon; eauto; instantiate; ins; desf. 
  destruct (classic (f x)) as [X|X]; eauto.
  assert (M: clos_refl_trans (fun a b => R a b /\ f a /\ f b) x x) by vauto.
  generalize X; revert H0 M X; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans. 
  by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf. 
Qed.

Lemma seqA2 X (r r' r'' : relation X) x y :
  seq (seq r r') r'' x y <-> seq r (seq r' r'') x y.
Proof.
  unfold seq; split; ins; desf; eauto 8.
Qed.


Lemma seq2 A (r r' r'': relation A) (L : r ;; r' <--> r'') s :
   r ;; r' ;; s <--> r'' ;; s.
Proof.
  rewrite <- L, seqA; vauto.
Qed.



Lemma inclusion_t_r_t A (rel rel' rel'': relation A) : 
  inclusion rel rel'' ->
  inclusion rel' (clos_refl_trans rel'') ->
  inclusion (clos_trans rel ;; rel') (clos_trans rel'').
Proof.
  by ins; rewrite H, H0, ct_rt.
Qed.

Lemma inclusion_r_t_t A (rel rel' rel'': relation A) : 
  inclusion rel (clos_refl_trans rel'') ->
  inclusion rel' rel'' ->
  inclusion (rel ;; clos_trans rel') (clos_trans rel'').
Proof.
  by ins; rewrite H, H0, rt_ct.
Qed.

Lemma inclusion_step2_ct A (rel rel' rel'': relation A) : 
  inclusion rel rel'' ->
  inclusion rel' rel'' ->
  inclusion (rel ;; rel') (clos_trans rel'').
Proof.
  ins; rewrite H, H0, <- ct_ct; eauto with rel.
Qed.

Lemma clos_trans_union_ct A (rel rel' : relation A) : 
  clos_trans (clos_trans rel +++ rel') 
  <--> clos_trans (rel +++ rel').
Proof.  
  split; eauto 8 with rel.
Qed.

Lemma inclusion_ct_seq_eqv_l A dom (rel : relation A) :
  inclusion (clos_trans (eqv_rel dom;; rel))
            (eqv_rel dom;; clos_trans rel).
Proof.
  by rewrite ct_begin, seqA, inclusion_seq_eqv_l with (rel:=rel), <- ct_begin.
Qed.
