(******************************************************************************)
(** * Basic properties of relations *)
(******************************************************************************)

Require Import Vbase NPeano Omega Permutation List Relations Setoid Classical.

Set Implicit Arguments.

Lemma list_seq_split :
  forall x a y, 
    x <= y ->
    List.seq a y = List.seq a x ++ List.seq (x + a) (y - x).
Proof.
  induction x; ins; rewrite ?Nat.sub_0_r; ins.
  destruct y; ins; try omega.
  f_equal; rewrite IHx; repeat (f_equal; try omega).
Qed.

Require Import extralib.

(** Definitions of relations *)
(******************************************************************************)

(** Make arguments implicit *)
Arguments clos_trans [A] R x y.
Arguments clos_refl_trans [A] R x y.
Arguments union [A] R1 R2 x y.
Arguments reflexive [A] R.
Arguments symmetric [A] R.
Arguments transitive [A] R.
Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.

Definition immediate X (rel : relation X) (a b: X) :=
  rel a b /\ (forall c (R1: rel a c) (R2: rel c b), False).

Definition irreflexive X (rel : relation X) := forall x, rel x x -> False.

Definition acyclic X (rel : relation X) := irreflexive (clos_trans rel).

Definition is_total X (cond: X -> Prop) (rel: relation X) :=
  forall a (IWa: cond a)
         b (IWb: cond b) (NEQ: a <> b),
    rel a b \/ rel b a.

Definition restr_subset X (cond: X -> Prop) (rel rel': relation X) :=
  forall a (IWa: cond a)
         b (IWb: cond b) (REL: rel a b),
    rel' a b.

Definition restr_rel X (cond : X -> Prop) (rel : relation X) : relation X :=
  fun a b => rel a b /\ cond a /\ cond b.

Definition restr_eq_rel A B (f : A -> B) rel x y :=
  rel x y /\ f x = f y.

Definition upward_closed (X: Type) (rel: relation X) (P: X -> Prop) :=
  forall x y (REL: rel x y) (POST: P y), P x.

Definition max_elt (X: Type) (rel: relation X) (a: X) :=
  forall b (REL: rel a b), False.

Notation "r 'UNION1' ( a , b )" := 
  (fun x y => x = a /\ y = b \/ r x y) (at level 100). 

Notation "a <--> b" := (same_relation a b)  (at level 110).

Definition seq (X:Type) (r1 r2 : relation X) : relation X :=
  fun x y => exists z, r1 x z /\ r2 z y.

Definition clos_refl A (R: relation A) x y := x = y \/ R x y.

Definition eqv_rel A f (x y : A) := x = y /\ f x.

Definition eq_rel A B (f : A -> B) x y := f x = f y.

Notation "P +++ Q" := (union P Q) (at level 50, left associativity).
Notation "P ;; Q" := (seq P Q) (at level 45, right associativity).

Definition dom_rel A (rel : relation A) x := exists y, rel x y.
Definition codom_rel A (rel : relation A) x := exists y, rel y x.

(** Very basic properties of relations *)
(******************************************************************************)

Lemma r_refl A (R: relation A) x : clos_refl R x x.
Proof. vauto. Qed.

Lemma r_step A (R: relation A) x y : R x y -> clos_refl R x y.
Proof. vauto. Qed.

Hint Immediate r_refl r_step.

Section BasicProperties.

Variable A : Type.
Variable dom : A -> Prop.
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

Lemma restr_rel_trans :
  transitive r -> transitive (restr_rel dom r).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma upward_clos_trans P :
  upward_closed r P -> upward_closed (clos_trans r) P.
Proof.
  ins; induction 1; eauto.
Qed.

Lemma max_elt_clos_trans a b:
  max_elt r a -> clos_trans r a b -> False.
Proof.
  ins; apply clos_trans_t1n in H0; induction H0; eauto.
Qed.

Lemma is_total_restr :
  is_total dom r ->
  is_total dom (restr_rel dom r).
Proof.
  red; ins; eapply H in NEQ; eauto; desf; vauto.
Qed.

Lemma clos_trans_restrD f x y :
  clos_trans (restr_rel f r) x y -> f x /\ f y.
Proof.
  unfold restr_rel; induction 1; ins; desf. 
Qed.

Lemma clos_trans_restr_eqD B (f: A -> B) x y : 
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
  irreflexive (union r r') <-> irreflexive r /\ irreflexive r'.
Proof.
  unfold irreflexive, union; repeat split; 
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_seqC :
  irreflexive (seq r r') <-> irreflexive (seq r' r).
Proof.
  unfold irreflexive, seq; repeat split; 
  try red; ins; desf; eauto.
Qed.

Lemma clos_trans_inclusion :
  inclusion r (clos_trans r).
Proof.
  vauto. 
Qed.

Lemma clos_trans_inclusion_clos_refl_trans:
  inclusion (clos_trans r) (clos_refl_trans r).
Proof.
  by red; ins; apply clos_trans_in_rt.
Qed.

Lemma clos_trans_monotonic :
  inclusion r r' ->
  inclusion (clos_trans r) (clos_trans r').
Proof.
  by red; ins; eapply clos_trans_mon. 
Qed.

Lemma clos_refl_trans_monotonic :
  inclusion r r' ->
  inclusion (clos_refl_trans r) (clos_refl_trans r').
Proof.
  by red; ins; eapply clos_refl_trans_mon. 
Qed.

Lemma inclusion_seq_mon s s' :
  inclusion r r' -> 
  inclusion s s' -> 
  inclusion (r ;; s) (r' ;; s').
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma inclusion_clos_refl :
  inclusion r r' -> 
  inclusion (clos_refl r) (clos_refl r').
Proof.
  unfold inclusion, clos_refl; ins; desf; eauto.
Qed.

Lemma inclusion_seq_trans t : 
  transitive t ->
  inclusion r t ->
  inclusion r' t ->
  inclusion (seq r r') t.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma inclusion_seq_rt :
  inclusion r (clos_refl_trans r'') ->
  inclusion r' (clos_refl_trans r'') ->
  inclusion (seq r r') (clos_refl_trans r'').
Proof. 
  unfold seq; red; ins; desf; eapply rt_trans; eauto. 
Qed.

Lemma inclusion_union_l :
  inclusion r r'' ->
  inclusion r' r'' ->
  inclusion (union r r') r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r :
  inclusion r r' \/ inclusion r r'' ->
  inclusion r (union r' r'').
Proof.
  unfold union; red; intros; desf; auto.
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

Lemma inclusion_step_t : 
  inclusion r r' ->
  inclusion r (clos_trans r').
Proof.
  unfold seq; red; ins; desf; eauto using t_step.
Qed.

Lemma inclusion_t_t : 
  inclusion r r' ->
  inclusion (clos_trans r) (clos_trans r').
Proof.
  red; ins; eapply clos_trans_mon; eauto. 
Qed.

Lemma inclusion_acyclic :
  inclusion r r' ->
  acyclic r' ->
  acyclic r.
Proof.
  repeat red; ins; eapply H0, clos_trans_mon; eauto.
Qed.

Lemma irreflexive_restr :
  irreflexive r -> irreflexive (restr_rel dom r).
Proof.
  unfold irreflexive, restr_rel; intuition; eauto. 
Qed.

Lemma inclusion_restr :
  inclusion (restr_rel dom r) r.
Proof.
  unfold inclusion, restr_rel; intuition.
Qed.

End BasicProperties.

Lemma transitive_restr_eq A B (f: A -> B) r :
  transitive r -> transitive (restr_eq_rel f r). 
Proof.
  unfold transitive, restr_eq_rel; intuition; eauto; congruence.
Qed.

Lemma irreflexive_restr_eq A B (f: A -> B) r :
  irreflexive (restr_eq_rel f r) <-> irreflexive r.
Proof.
  unfold irreflexive, restr_eq_rel; intuition; eauto. 
Qed.

Lemma clos_trans_of_clos_trans1 A (r r' : relation A) x y :
  clos_trans (fun a b => clos_trans r a b \/ r' a b) x y <->
  clos_trans (fun a b => r a b \/ r' a b) x y.
Proof.
  split; induction 1; desf; 
  eauto using clos_trans, clos_trans_mon.
Qed.

Lemma clos_trans_of_clos_trans A (r : relation A) x y :
  clos_trans (clos_trans r) x y <->
  clos_trans r x y.
Proof.
  apply ct_of_transitive; vauto.
Qed.

Lemma inclusion_union :
  forall {A : Type} (R1 R1' R2 R2' : relation A)
         (HINC1 : inclusion R1' R1)
         (HINC2 : inclusion R2' R2),
    inclusion (union R2' R1') (union R2 R1).
Proof.
  intros.
  intros x y HUN.
  inversion HUN; [left; auto | right; auto].
Qed.

Lemma inclusion_restr_rel_l :
  forall {A : Type} (dom : A -> Prop) (R1 R1' : relation A)
         (HINC: inclusion R1' R1),
    inclusion (restr_rel dom R1') R1.
Proof.
  unfold inclusion, seq, clos_refl, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_seq_refl :
  forall (A : Type) (R1 R2 R3 : relation A)
         (INC1: inclusion R1 R3)
         (INC2: inclusion R2 R3)
         (TRANS: transitive R3),
    inclusion (seq R1 (clos_refl R2)) R3.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma inclusion_rt_l X (r r' : relation X) :
   reflexive r' ->
   inclusion (seq r r') r' ->
   inclusion (clos_refl_trans r) r'.
Proof.
  red; ins; eapply clos_rt_rt1n in H1; induction H1; ins; eapply H0; vauto.
Qed.

Lemma inclusion_rt_rt2 :
  forall (A : Type) (r t : relation A),
  inclusion r (clos_refl_trans t) ->
  inclusion (clos_refl_trans r) (clos_refl_trans t).
Proof.
  red; ins; induction H0; eauto using clos_refl_trans.
Qed.

Lemma inclusion_restr_eq A B (f: A -> B) r :
  inclusion (restr_eq_rel f r) r.
Proof.
  unfold restr_eq_rel, inclusion; intuition. 
Qed.

Hint Resolve
     inclusion_restr_eq inclusion_restr
     inclusion_acyclic inclusion_restr_rel_l
     inclusion_step_t inclusion_union_r inclusion_union
     inclusion_seq_refl : inclusion.

Hint Resolve inclusion_rt_rt inclusion_r_rt inclusion_step_rt : inclusion.



(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

(** First, for inclusion. *)

Lemma inclusion_refl A : reflexive (@inclusion A).
Proof. repeat red; ins. Qed.

Lemma inclusion_trans A : transitive (@inclusion A).
Proof. repeat red; eauto. Qed.

Add Parametric Relation (X : Type) : (relation X) (@inclusion X) 
 reflexivity proved by (@inclusion_refl X)
 transitivity proved by (@inclusion_trans X)
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

Add Parametric Morphism X : (@seq X) with signature 
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof.
  unfold same_relation, seq; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature 
  same_relation ==> same_relation as restr_rel_more.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
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


Hint Rewrite seqFr seqrF unionrF unionFr : samerel.






(******************************************************************************)
(** ** Lemmas about cycles *)
(******************************************************************************)

Lemma min_cycle X (rel rel' : relation X) (dom : X -> Prop)
    (TOT: is_total dom rel') 
    (T : transitive rel')
    (INCL: inclusion rel' (clos_trans rel))
    (INV: forall a b (R: rel a b) (R': rel' b a), False) :
    acyclic rel <->
    acyclic (restr_rel (fun x => ~ dom x) rel) /\
    (forall x (CYC: rel x x) (D: dom x), False) /\
    (forall c1 b1 (R: rel c1 b1) b2 
       (S : clos_refl rel' b1 b2) c2 
       (R': rel b2 c2) (S': clos_refl_trans (restr_rel (fun x => ~ dom x) rel) c2 c1)
       (D1 : dom b1) (D2: dom b2) (ND1: ~ dom c1) (ND2: ~ dom c2), False).
Proof.
  split; intros A; repeat split; ins; desc; eauto.
    by intros x P; eapply A, clos_trans_mon; eauto; unfold restr_rel; ins; desf.
    by eauto using t_step.
    eapply (A c1), t_trans, rt_t_trans, t_rt_trans; eauto using t_step;
      try (by eapply clos_refl_trans_mon; eauto; unfold restr_rel; ins; desf).
    by red in S; desf; eauto using clos_refl_trans, clos_trans_in_rt.
  assert (INCL': forall a b (R: rel a b) (D: dom a) (D': dom b), rel' a b).
    by ins; destruct (classic (a = b)) as [|N]; 
       [|eapply TOT in N]; desf; exfalso; eauto.
  intros x P.

  assert (J: clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x x \/
             rel' x x /\ dom x /\ dom x \/
          dom x /\ (exists m n k, clos_refl rel' x m /\ rel m n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) n k 
            /\ clos_refl rel k x 
            /\ dom m /\ ~ dom n /\ ~ dom k) \/
          (exists k m,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x k /\
            rel k m /\ clos_refl rel' m x /\
            ~ dom k /\ dom m /\ dom x) \/
          (exists k m m' n,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x k /\
            rel k m /\ clos_refl rel' m m' /\ rel m' n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) n x /\
            ~ dom k /\ dom m /\ dom m' /\ ~ dom n)).
    by vauto.
  revert P J; generalize x at 1 4 6 8 11 13 14 16.
  unfold restr_rel in *; ins; apply clos_trans_tn1 in P; induction P; eauto.
  { rename x0 into x; desf; eauto.
    destruct (classic (dom x)); rewrite clos_refl_transE in *; desf; eauto using clos_trans. 
      by destruct (clos_trans_restrD J); desf. 
    by destruct (clos_trans_restrD J); eapply A, t_trans, t_step; vauto. 

    unfold clos_refl in J3; desf.
      by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.
    destruct (classic (dom x)).
      by eapply A1 with (c1 := k) (b2 := m); eauto; 
         unfold clos_refl in *; desf; eauto.
    by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.

    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    by eapply A1 with (c1 := k) (b2 := x); eauto 8 using rt_trans, rt_step.

    destruct (classic (dom x)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    by eapply A1 with (c1 := k) (b2 := m'); eauto 8 using rt_trans, rt_step.
  }
  eapply clos_tn1_trans in P; desf.
  {
    destruct (classic (dom y)).
      rewrite clos_refl_transE in J; desf.
        destruct (classic (dom x0)).
          by eapply IHP; right; left; eauto using t_step.
        eapply IHP; do 2 right; left; split; ins.
        by eexists y,x0,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      destruct (clos_trans_restrD J).
      apply IHP; right; right; left; split; ins.
      by eexists y,z,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
    rewrite clos_refl_transE in J; desf.
      destruct (classic (dom x0)).
        eapply IHP; do 3 right; left.
        by eexists y,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      by eapply IHP; left; vauto.
    by destruct (clos_trans_restrD J); eapply IHP; left; 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
  }
  {
    destruct (classic (dom y)).
      by apply IHP; eauto 8 using clos_trans.
    apply IHP; do 3 right; left; eexists y, z; 
    repeat eexists; vauto; eauto using clos_trans_in_rt. 
  }
  { destruct (classic (dom y)).
      by eapply IHP; do 2 right; left; split; ins; eexists m; repeat eexists; 
         eauto; red in J0; red; desf; eauto. 
    destruct (classic (dom x0)).
    
    destruct (classic (m = x0)) as [|NEQ]; subst.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto. 
    eapply TOT in NEQ; desf.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto;
         eauto; red; red in J0; desf; eauto. 
    by red in J3; desf; eapply A1 with (c1 := k) (b2 := m); 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.

    by eapply IHP; do 4 right; eexists y,z; repeat eexists; vauto; 
       unfold clos_refl in *; desf; vauto.
  }

  { destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    destruct (classic (y = m)) as [|NEQ]; desf.
      by unfold clos_refl in *; desf; eauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; 
           apply IHP; right; left; eauto using t_rt_trans, t_step.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 3 right; left; eexists k, m; repeat eexists; vauto.
  }

    destruct (classic (dom x0)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    destruct (classic (y = m)) as [|NEQ]; desf.
      by eapply IHP; do 2 right; left; split; ins; eexists m', n; repeat eexists; vauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; eapply IHP; do 2 right; left; split; ins; 
           eexists m', n; repeat eexists; vauto;
           eauto using rt_trans, clos_trans_in_rt.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 4 right; eexists k,m,m'; repeat eexists; vauto.
Qed.



Lemma path_decomp_u1 X (rel : relation X) a b c d : 
  clos_trans (rel UNION1 (a, b)) c d ->
  clos_trans rel c d \/ 
  clos_refl_trans rel c a /\ clos_refl_trans rel b d.
Proof.
  induction 1; desf; eauto using clos_trans, clos_refl_trans, clos_trans_in_rt.
Qed.

Lemma cycle_decomp_u1 X (rel : relation X) a b c : 
  clos_trans (rel UNION1 (a, b)) c c ->
  clos_trans rel c c \/ clos_refl_trans rel b a.
Proof.
  ins; apply path_decomp_u1 in H; desf; eauto using clos_refl_trans.
Qed.

Lemma path_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b) x y
    (C: clos_trans (fun a b => rel1 a b \/ rel2 a b) x y),
    clos_trans rel1 x y \/
    (exists m n, 
      clos_refl_trans rel1 x m /\ clos_trans rel2 m n /\ clos_refl_trans rel1 n y) \/
    (exists m n, 
      clos_refl_trans rel1 m n /\ clos_trans rel2 n m).
Proof.
  ins; induction C; desf; eauto 8 using rt_refl, clos_trans.
  by right; left; exists m, n; eauto using clos_trans_in_rt, rt_trans.
  by right; left; exists m, n; eauto using clos_trans_in_rt, rt_trans.

  destruct (classic (m = n0)) as [|NEQ]; desf.
  by right; left; exists m0, n; eauto using t_trans, rt_trans.
  eapply T in NEQ; desf.
    by right; right; exists n0, m; eauto 8 using clos_trans, rt_trans.
    by right; left; exists m0, n; eauto 8 using clos_trans, rt_trans.
    by apply t_step_rt in IHC0; desf; eapply D in IHC0; desf.
    by apply t_rt_step in IHC4; desf; eapply D in IHC6; desf.
Qed.

Lemma cycle_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b) x
    (C: clos_trans (fun a b => rel1 a b \/ rel2 a b) x x),
    clos_trans rel1 x x \/
    (exists m n, clos_refl_trans rel1 m n /\ clos_trans rel2 n m).
Proof.
  ins; exploit path_decomp_u_total; eauto; ins; desf; eauto 8 using rt_trans.
Qed.

Lemma clos_trans_disj_rel :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x y
    (R: clos_trans rel x y) z
    (R': clos_trans rel' y z),
    False.
Proof.
  ins; induction R; eauto; induction R'; eauto.
Qed.

Lemma path_decomp_u_1 :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x y
    (T: clos_trans (union rel rel') x y),
    clos_trans rel x y \/ clos_trans rel' x y
    \/ exists z, clos_trans rel' x z /\ clos_trans rel z y.
Proof.
  unfold union; ins.
  induction T; desf; eauto 6 using clos_trans;
    try by exfalso; eauto using clos_trans_disj_rel.
Qed.

Lemma cycle_decomp_u_1 :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x
    (T: clos_trans (union rel rel') x x),
    clos_trans rel x x \/ clos_trans rel' x x. 
Proof.
  ins; exploit path_decomp_u_1; eauto; ins; desf; eauto.
  exfalso; eauto using clos_trans_disj_rel.
Qed.

Lemma cycle_disj :
  forall X (rel : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel y z), False) x
    (T: clos_trans rel x x), False.
Proof.
  ins; inv T; eauto using clos_trans_disj_rel.
Qed.

Lemma clos_trans_restr_trans_mid : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    z (B : rel y z) w
    (C : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) z w),
    clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x w.
Proof.
  ins; eapply t_trans, t_trans; vauto.
  eapply t_step; repeat split; eauto.
    by apply clos_trans_restrD in A; desc.
  by apply clos_trans_restrD in C; desc.
Qed.

Lemma clos_trans_restr_trans_cycle : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    (B : rel y x),
    clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x x.
Proof.
  ins; eapply t_trans, t_step; eauto. 
  by red; apply clos_trans_restrD in A; desf; auto.
Qed.

Lemma path_tur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (T: transitive r)
         (A: forall x y (R: r' x y), adom x)
         (B: forall x y (R: r' x y), bdom y) x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    r x y \/
    exists z,
      clos_trans (fun x y => r x y /\ adom y \/ r' x y) x z /\
      (z = y \/ r z y /\ bdom z).
Proof.
  ins; apply clos_trans_tn1 in P; induction P; desf; eauto 14 using clos_trans; clear P.
  apply clos_trans_t1n in IHP; induction IHP; intuition; desf; eauto 14 using clos_trans.
Qed.

Lemma path_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r' x y), adom x)
         (B: forall x y (R: r' x y), bdom y) x y   
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    clos_trans r x y \/
    exists z,
      clos_trans (fun x y => clos_trans r x y /\ adom y \/ r' x y) x z /\
      (z = y \/ clos_trans r z y /\ bdom z).
Proof.
  ins; eapply path_tur; ins; vauto.
  by eapply clos_trans_mon; eauto; instantiate; ins; desf; eauto using t_step.
Qed. 

Lemma path_tur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (T: transitive r')  
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y) x y   
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    r' x y \/
    exists z,
      (x = z \/ r' x z /\ adom z) /\
      clos_trans (fun x y => r x y \/ r' x y /\ bdom x) z y.
Proof.
  ins; apply clos_trans_t1n in P; induction P; desf; eauto 14 using clos_trans; clear P.
  apply clos_trans_tn1 in IHP0; induction IHP0; intuition; desf; eauto 14 using clos_trans.
Qed. 

Lemma path_ur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y) x y   
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    clos_trans r' x y \/
    exists z,
      (x = z \/ clos_trans r' x z /\ adom z) /\
      clos_trans (fun x y => r x y \/ clos_trans r' x y /\ bdom x) z y.
Proof.
  ins; eapply path_tur2; ins; vauto.
  by eapply clos_trans_mon; eauto; instantiate; ins; desf; eauto using t_step.
Qed. 

Lemma cycle_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y) x   
    (P: clos_trans (fun x y => r x y \/ r' x y) x x),
    clos_trans r' x x \/
    exists x, 
      clos_trans (fun x y => r x y \/ clos_trans r' x y /\ bdom x /\ adom y) x x.
Proof.
  ins; eapply path_ur2 with (adom:=adom) (bdom:=bdom) in P; desf; eauto. 
  eapply clos_trans_mon, 
    path_tur with (adom:=adom) (bdom:=bdom) (r':=r)
                  (r:=fun a b => clos_trans r' a b /\ bdom a)  in P0;
  desf; try split; ins; desc; vauto; try tauto.
  right; exists z; eapply clos_trans_mon; eauto; instantiate; ins; tauto.

  eapply t_step_rt in P0; desf. 
    rewrite clos_refl_transE in *; desf; eauto using clos_trans.
    right; exists z1; eapply t_trans with z0; eauto 7 using clos_trans. 
    eapply clos_trans_mon; eauto; instantiate; ins; tauto.
  right; exists z0; eapply t_trans, t_step_rt; eauto 8 using t_step.
  eexists; split; eauto; eapply clos_refl_trans_mon; eauto; instantiate; ins; tauto.

  eapply clos_trans_mon with 
    (r' := fun x y => clos_trans r' x y /\ bdom x \/ r x y) in P0; try tauto.
  eapply path_tur with (adom:=adom) (bdom:=bdom) in P0; desf; eauto using clos_trans.

  eapply t_rt_step in P0; desf. 
    rewrite clos_refl_transE in *; desf; eauto using clos_trans.
    right; exists z; eapply t_trans with z0; eauto 7 using clos_trans. 
    eapply clos_trans_mon; eauto; instantiate; ins; tauto.
  right; exists z0; eapply t_trans, t_step_rt; eauto 8 using t_step.
  eexists; split; eauto; eapply clos_refl_trans_mon; eauto; instantiate; ins; tauto.

  right; exists z; eapply t_trans with z0; eauto 8 using clos_trans.
  eapply clos_trans_mon; eauto; instantiate; ins; tauto.

  by red; ins; desf; vauto.
Qed. 

Lemma restr_eq_union : 
  forall X (rel rel' : relation X) B (f: X -> B) x y
         (R: forall x y, rel' x y -> f x = f y),
   restr_eq_rel f (fun x y => rel x y \/ rel' x y) x y <->
   restr_eq_rel f rel x y \/ rel' x y.
Proof.
  unfold restr_eq_rel; ins; intuition.
Qed.

Lemma clos_trans_restr_eq_union : 
  forall X (rel rel' : relation X) B (f: X -> B)
         (R: forall x y, rel' x y -> f x = f y),
   clos_trans (restr_eq_rel f (fun x y => rel x y \/ rel' x y)) <-->
   clos_trans (fun x y => restr_eq_rel f rel x y \/ rel' x y).
Proof.
  split; red; ins; eapply clos_trans_mon; eauto; ins; instantiate;
  rewrite restr_eq_union in *; eauto.
Qed.

Lemma acyclic_mon X (rel rel' : relation X) :
  acyclic rel -> inclusion rel' rel -> acyclic rel'.
Proof.
  eby repeat red; ins; eapply H, clos_trans_mon.
Qed.

(** Extension of a partial order to a total order *)
(******************************************************************************)

Section one_extension.

  Variable X : Type.
  Variable elem : X.
  Variable rel : relation X.

  Definition one_ext : relation X := 
    fun x y =>
      clos_trans rel x y 
      \/ clos_refl_trans rel x elem /\ ~ clos_refl_trans rel y elem.

  Lemma one_ext_extends x y : rel x y -> one_ext x y. 
  Proof. vauto. Qed.

  Lemma one_ext_trans : transitive one_ext.
  Proof. 
    red; ins; unfold one_ext in *; desf; desf; 
      intuition eauto using clos_trans_in_rt, t_trans, rt_trans.
  Qed.
 
  Lemma one_ext_irr : acyclic rel -> irreflexive one_ext.
  Proof.
    red; ins; unfold one_ext in *; desf; eauto using clos_trans_in_rt.
  Qed.

  Lemma one_ext_total_elem : 
    forall x, x <> elem -> one_ext elem x \/ one_ext x elem.
  Proof.
    unfold one_ext; ins; rewrite !clos_refl_transE; tauto.
  Qed.

End one_extension.

Fixpoint tot_ext X (dom : list X) (rel : relation X) : relation X :=
  match dom with 
    | nil => clos_trans rel
    | x::l => one_ext x (tot_ext l rel) 
  end.

Lemma tot_ext_extends : 
  forall X dom (rel : relation X) x y, rel x y -> tot_ext dom rel x y. 
Proof. 
  induction dom; ins; eauto using t_step, one_ext_extends.
Qed.

Lemma tot_ext_trans X dom (rel : relation X) :  transitive (tot_ext dom rel).
Proof. 
  induction dom; ins; vauto; apply one_ext_trans. 
Qed.

Lemma tot_ext_irr : 
  forall X (dom : list X) rel, acyclic rel -> irreflexive (tot_ext dom rel).
Proof.
  induction dom; ins.
  apply one_ext_irr, trans_irr_acyclic; eauto using tot_ext_trans.
Qed.

Lemma tot_ext_total : 
  forall X (dom : list X) rel, is_total (fun x => In x dom) (tot_ext dom rel).
Proof.
  induction dom; red; ins; desf.
  eapply one_ext_total_elem in NEQ; desf; eauto.
  eapply not_eq_sym, one_ext_total_elem in NEQ; desf; eauto.
  eapply IHdom in NEQ; desf; eauto using one_ext_extends.
Qed.

Lemma tot_ext_inv :
  forall X dom rel (x y : X),
    acyclic rel -> tot_ext dom rel x y -> ~ rel y x.
Proof.
  red; ins; eapply tot_ext_irr, tot_ext_trans, tot_ext_extends; eauto.
Qed.

Lemma tot_ext_extends_dom 
  X dom dom' (rel : relation X) x y :  
    tot_ext dom rel x y ->
    tot_ext (dom' ++ dom) rel x y.
Proof.
  induction dom'; ins; eauto using one_ext_extends.
Qed.

Definition tot_ext_nat rel (x y: nat) := 
  exists k, tot_ext (rev (List.seq 0 k)) rel x y.

Lemma tot_ext_nat_extends (rel : relation nat) x y : 
  rel x y -> tot_ext_nat rel x y. 
Proof.
  exists 0; eauto using tot_ext_extends.
Qed.

Lemma tot_ext_nat_trans rel :  transitive (tot_ext_nat rel).
Proof. 
  unfold tot_ext_nat; red; ins; desf.
  destruct (le_lt_dec k k0) as [LE|LE]; [|apply Nat.lt_le_incl in LE];
    [exists k0|exists k]; eapply tot_ext_trans; eauto;
    rewrite (list_seq_split _ LE), rev_app_distr; eauto using tot_ext_extends_dom.
Qed.

Lemma tot_ext_nat_irr : 
  forall rel, acyclic rel -> irreflexive (tot_ext_nat rel).
Proof.
  red; unfold tot_ext_nat; ins; desf; eapply tot_ext_irr; eauto.
Qed.

Lemma tot_ext_nat_total : 
  forall rel, is_total (fun _ => true) (tot_ext_nat rel).
Proof.
  unfold tot_ext_nat; red; ins.
  eapply tot_ext_total with (rel:=rel) (dom := rev (List.seq 0 (S (a + b)))) in NEQ;
    desf; eauto; rewrite <- in_rev, in_seq; omega.
Qed.

Lemma tot_ext_nat_inv :
  forall rel x y,
    acyclic rel -> tot_ext_nat rel x y -> ~ rel y x.
Proof.
  red; ins; eapply tot_ext_nat_irr, tot_ext_nat_trans, tot_ext_nat_extends; eauto.
Qed.


Add Parametric Morphism X : (@one_ext X) with signature 
  eq ==> same_relation ==> same_relation as one_ext_more.
Proof.
  unfold one_ext, same_relation, inclusion; intuition; 
  eauto 8 using clos_trans_mon, clos_refl_trans_mon. 
Qed.

Add Parametric Morphism X : (@tot_ext X) with signature 
  eq ==> same_relation ==> same_relation as tot_ext_more.
Proof.
  induction y; ins; eauto using clos_trans_more, one_ext_more. 
Qed.

Add Parametric Morphism : tot_ext_nat with signature 
  same_relation ==> same_relation as tot_ext_nat_more.
Proof.
  unfold tot_ext_nat; split; red; ins; desf; exists k;
  eapply tot_ext_more; eauto; symmetry; eauto.
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


(** Preferential union *)
(******************************************************************************)


Definition pref_union X (r r' : relation X) x y :=
  r x y \/ r' x y /\ ~ r y x.

Lemma acyclic_pref_union : 
  forall X (r r' : relation X) (dom : X -> Prop)
         (IRR: irreflexive r) 
         (T: transitive r)
         (TOT: is_total dom r)
         (DL: forall x y (R: r' x y), dom x /\ ~ dom y),
    acyclic (pref_union r r').
Proof.
  ins; unfold pref_union.
  assert (EQ: restr_rel (fun x => ~ dom x)
                    (fun x y => r x y \/ r' x y /\ ~ r y x)
          <--> restr_rel (fun x => ~ dom x) r).
    unfold restr_rel; split; red; ins; desf; eauto.
    by exploit DL; eauto; ins; desf.

  apply min_cycle with (dom := dom) (rel' := r); 
    repeat split; repeat red; ins; desf; eauto using t_step;
    try rewrite EQ in *; 
    repeat match goal with 
          | H : clos_trans _ _ _ |- _ =>
            rewrite (ct_of_transitive (restr_rel_trans T)) in H
          | H : clos_refl_trans _ _ _ |- _ =>
            rewrite (crt_of_transitive (restr_rel_trans T)) in H
          | H : r' _ _ |- _ => apply DL in H; desf
        end;
    unfold restr_rel, clos_refl in *; desf; eauto.
Qed.

Lemma in_pref_union : 
  forall X (r r' : relation X) (dom : X -> Prop)
         (IRR: irreflexive r) 
         (T: transitive r)
         (TOT: is_total dom r)
         (DL: forall x y (R: r' x y), dom x /\ ~ dom y) x y
         (R: clos_trans (pref_union r r') x y) 
         (D: dom y),
    r x y.
Proof.
  unfold pref_union; ins; apply clos_trans_t1n in R; induction R; desf; eauto.
    by eapply DL in H; desf.
  apply clos_t1n_trans in R.
  assert (K:=DL _ _ H); desc.
  destruct (classic (x = z)) as [|N]; [|apply TOT in N]; desf; ins.
    by exfalso; eauto.
  exfalso; eapply acyclic_pref_union with (r:=r), t_trans, t_trans; vauto. 
Qed.


(** Remove duplicate list elements (classical) *)
(******************************************************************************)

Fixpoint undup A dec (l: list A) :=
  match l with nil => nil
    | x :: l =>
      if In_dec dec x l then undup dec l else x :: undup dec l
  end.

Lemma In_undup X dec (x: X) l : In x (undup dec l) <-> In x l.
Proof.
  induction l; ins; des_if; ins; rewrite IHl; split; ins; desf; vauto.
Qed.

Lemma NoDup_undup X dec (l : list X) : NoDup (undup dec l).
Proof.
  induction l; ins; desf; constructor; eauto; rewrite In_undup; eauto. 
Qed.


Lemma clos_trans_imm2 :
  forall X (dec : forall x y : X, {x = y} + {x <> y}) 
         (R : relation X) (I: irreflexive R) 
         (T: transitive R) L a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans (immediate R) a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup dec L); ins;
  try rewrite In_undup; eauto using NoDup_undup.
Qed.


Lemma total_immediate_unique:
  forall X (eq_X_dec: forall (x y: X), {x=y} + {x<>y}) (rel: X -> X -> Prop) (P: X -> Prop)
         (Tot: is_total P rel)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate rel a c)
         (ibc: immediate rel b c),
    a = b.
Proof.
  ins; destruct (eq_X_dec a b); eauto.
  exfalso; unfold immediate in *; desf.
  eapply Tot in n; eauto; desf; eauto.
Qed.


Lemma path_ut :
  forall X (r r' : relation X) (T: transitive r') x y
    (P: clos_refl_trans (fun x y => r x y \/ r' x y) x y),
    exists z w,
      clos_refl_trans r x z /\
      clos_refl_trans (fun x y => exists z, r' x z /\ clos_trans r z y) z w /\
      (w = y \/ r' w y).
Proof.
  ins; induction P; eauto 8 using rt_refl.
    by desf; eauto 8 using rt_refl, rt_step.
  clear P1 P2; desf.

  rewrite clos_refl_transE in IHP2; desf;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|
   rewrite clos_refl_transE, t_rt_step in IHP4; desf;
   eauto 8 using rt_trans, clos_trans_in_rt];
  (repeat eexists; [eauto|eapply rt_trans, rt_trans|vauto]); eauto;
  apply rt_step; eauto using t_trans.

  rewrite clos_refl_transE in IHP2; desf;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|];
  (repeat eexists; [eauto|eapply rt_trans, rt_trans|vauto]); eauto;
  apply rt_step; eauto.

  rewrite clos_refl_transE in IHP2; desf; eauto 8 using rt_trans;
  rewrite clos_refl_transE, t_rt_step in IHP4; desf;
  eauto 8 using rt_trans, clos_trans_in_rt;
  (repeat eexists; [eauto|eapply rt_trans,rt_trans|right; eauto]); eauto;
  apply rt_step; eauto using t_trans.

  rewrite clos_refl_transE in IHP2; desf; eauto 8 using rt_trans;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|];
  (repeat eexists; [eauto|eapply rt_trans,rt_trans|right; eauto]); eauto;
  apply rt_step; eauto using t_trans.
Qed.


Lemma path_ut2 :
  forall X (r r' : relation X) (T: transitive r') x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    clos_trans r x y \/
    exists z w w',
      clos_refl_trans r x z /\
      clos_refl_trans (fun x y => exists z, r' x z /\ clos_trans r z y) z w /\
      r' w w' /\
      clos_refl_trans r w' y.
Proof.
  ins.
  rewrite t_rt_step in P; desc;
  eapply path_ut in P; ins; desf;
  try (by right; repeat eexists; eauto using clos_refl_trans, clos_trans_in_rt).

  rewrite clos_refl_transE in P1; desf.
    by rewrite t_rt_step; eauto.
  right; rewrite t_rt_step in P1; desf.
  by repeat eexists; eauto using clos_refl_trans, clos_trans_in_rt.

  by right; eexists _, _, y; repeat eexists;
     eauto using clos_refl_trans, clos_trans_in_rt.
Qed.


Lemma path_utd :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b) x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    clos_trans r x y \/
    (exists z w, clos_refl_trans r x z /\ r' z w /\ clos_refl_trans r w y) \/
    (exists z w, r' z w /\ clos_refl_trans r w z).
Proof.
  ins; induction P; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  right; destruct (classic (z1 = w)) as [|NEQ]; desf; eauto 8 using clos_refl_trans.
  eapply F in NEQ; desf; eauto 8 using clos_refl_trans.
  eapply R in IHP4; desf.
  eapply R in IHP0; desf.
Qed.

Lemma cycle_utd :
  forall X (r: relation X) (A: acyclic r) 
         r' (T: transitive r') (IRR: irreflexive r') dom
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b) x
    (P: clos_trans (fun x y => r x y \/ r' x y) x x),
  exists z w, r' z w /\ clos_trans r w z.
Proof.
  ins; eapply path_utd in P; eauto; desf;
  try rewrite clos_refl_transE in *; desf;
  eauto using clos_trans; exfalso; eauto.
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




Lemma path_unc X (r r' : relation X)
  (A: seq r r <--> (fun x y => False))
  (B: seq r' r' <--> (fun x y => False)) :
  clos_refl_trans (union r r') <-->
  clos_refl_trans (seq r r') +++
  (clos_refl_trans (seq r' r) +++
   (seq r (clos_refl_trans (seq r' r)) +++
    seq r' (clos_refl_trans (seq r r')))).
Proof.
  split.
    eapply inclusion_rt_l; [by vauto|].
    rewrite seq_union_l, !seq_union_r, <- !seqA, <- !t_step_rt2.
    rewrite (rtE_left r (seq r r')), (rtE_left r' (seq r' r)), <- !seqA.
    rewrite A, B, ?seqFr, ?unionrF, ?unionFr.
    by unfold union, seq; red; ins; desf; 
       eauto 6 using clos_trans_in_rt, rt_refl.
  repeat first [apply inclusion_union_l|apply inclusion_seq_rt|
                eapply inclusion_rt_rt2]; vauto. 
Qed.

Lemma pathp_unc X (r r' : relation X)
  (A: seq r r <--> (fun x y => False))
  (B: seq r' r' <--> (fun x y => False)) :
  clos_trans (union r r') <-->
  clos_trans (seq r r') +++
  (clos_trans (seq r' r) +++
   (seq r (clos_refl_trans (seq r' r)) +++
    seq r' (clos_refl_trans (seq r r')))).
Proof.
  rewrite t_step_rt2, path_unc; ins.
  rewrite seq_union_l, !seq_union_r, <- !seqA, <- !t_step_rt2.
  rewrite (rtE_left r (seq r r')), (rtE_left r' (seq r' r)), <- !seqA.
  rewrite A, B, ?seqFr, ?unionrF, ?unionFr.
  by unfold union, seq; split; red; ins; desf; eauto 8 using rt_refl.   
Qed.

Lemma acyclic_unc X (r r' : relation X)
  (A: seq r r <--> (fun x y => False))
  (B: seq r' r' <--> (fun x y => False)) :
  acyclic (union r r') <-> acyclic (seq r r').
Proof.
  unfold acyclic.
  rewrite pathp_unc, !irreflexive_union; ins. 
  rewrite (irreflexive_seqC r), (irreflexive_seqC r'). 
  rewrite rtE_right, seqA, A, !seqrF, unionrF.
  rewrite rtE_right, seqA, B, !seqrF, unionrF.
  unfold seq, irreflexive; repeat split; ins; desf; 
  eauto using t_step.

  apply t_rt_step in H0; desf; apply (H z0).
  exploit (proj2 (crt_seq_swap r r') z0 z); [by eexists x; vauto|].
  by intros [? ?]; desf; eapply rt_t_trans, t_step; eauto.

  eapply A; vauto. 
  eapply B; vauto. 
Qed.



Lemma in_split_perm A (x : A) l (IN: In x l) :
  exists l', Permutation l (x :: l').
Proof.
  induction l; ins; intuition; desf; eauto.
  exists (a :: l'); rewrite H0; vauto.
Qed.

Lemma in_concat_iff A (a: A) ll :
  In a (concat ll) <-> exists l, In a l /\ In l ll.
Proof.
  induction ll; ins; [by split; ins; desf|].
  rewrite in_app_iff, IHll; split; ins; desf; eauto. 
Qed.

Lemma in_concat A (a: A) l ll :
  In a l ->
  In l ll ->
  In a (concat ll).
Proof.
  rewrite in_concat_iff; eauto.
Qed.

Add Parametric Morphism X : (@concat X) with 
  signature (@Permutation (list X)) ==> (@Permutation X)
      as concat_more.
Proof.
  induction 1; rewrite ?concat_cons,  ?app_assoc; 
  eauto using Permutation, Permutation_app, Permutation_app_comm. 
Qed.

Lemma NoDup_concat_simpl A (a : A) l1 l2 ll  
      (ND: NoDup (concat ll))
      (K: In l1 ll) (K' : In a l1)
      (L: In l2 ll) (L' : In a l2) :
      l1 = l2.
Proof.
  apply in_split_perm in K; desc; rewrite K, concat_cons, nodup_app in *; ins; desf.
  edestruct ND1; eauto using in_concat.
Qed.

Lemma NoDup_concatD A (l: list A) ll :
  NoDup (concat ll) -> In l ll -> NoDup l.
Proof.
  ins; apply in_split_perm in H0; desf.
  rewrite H0, concat_cons, nodup_app in H; desf.
Qed.

Lemma NoDup_eq_simpl A l1 (a : A) l1' l2 l2'  
      (ND : NoDup (l1 ++ a :: l1'))
      (L : l1 ++ a :: l1' = l2 ++ a :: l2') :
      l1 = l2 /\ l1' = l2'.
Proof.
  revert l2 L; induction l1; ins; destruct l2; ins; desf. 
    by exfalso; inv ND; eauto using in_or_app, in_eq, in_cons.
    by exfalso; inv ND; eauto using in_or_app, in_eq, in_cons.
  inv ND; eapply IHl1 in H0; desf. 
Qed. 

(** Construct a total order from a list of elements *)
(******************************************************************************)

Definition total_order_from_list A (l: list A) x y :=
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3.

Lemma total_order_from_list_cons :
  forall A (a : A) l x y,
    total_order_from_list (a :: l) x y <->
    a = x /\ In y l \/ total_order_from_list l x y.
Proof.
  unfold total_order_from_list; split; ins; desf.
    by destruct l1; ins; desf; eauto using in_or_app, in_eq, in_cons.
    apply in_split in H0; desf; exists nil; ins; eauto.
  exists (a :: l1); ins; eauto.
Qed.

Lemma total_order_from_list_app :
  forall A (l1 l2: list A) x y,
    total_order_from_list (l1 ++ l2) x y <->
    In x l1 /\ In y l2 \/
    total_order_from_list l1 x y \/
    total_order_from_list l2 x y.
Proof.
  induction l1; ins.
    intuition; eauto.
    by unfold total_order_from_list in *; desf; destruct l1; ins.
  rewrite !total_order_from_list_cons, IHl1, in_app_iff; clear;
  intuition.
Qed.

Lemma total_order_from_list_insert :
  forall A (l1: list A) a l2 x y,
    total_order_from_list (l1 ++ l2) x y ->
    total_order_from_list (l1 ++ a :: l2) x y.
Proof.
  ins; rewrite total_order_from_list_app, total_order_from_list_cons in *; 
  ins; desf; eauto.
Qed.

Lemma total_order_from_list_remove :
  forall A (l1: list A) a l2 x y,
    total_order_from_list (l1 ++ a :: l2) x y ->
    x <> a -> y <> a ->
    total_order_from_list (l1 ++ l2) x y.
Proof.
  ins; rewrite total_order_from_list_app, total_order_from_list_cons in *; 
  ins; desf; eauto.
Qed.

Lemma total_order_from_list_swap :
  forall A (l1: list A) a b l2 x y, 
    total_order_from_list (l1 ++ a :: b :: l2) x y ->
    (x = a -> b = y -> False) ->
    total_order_from_list (l1 ++ b :: a :: l2) x y.
Proof.
  ins; rewrite total_order_from_list_app, !total_order_from_list_cons in *;
  ins; intuition; desf; exfalso; eauto.
Qed.

Lemma total_order_from_list_in A (l: list A) x y :
  total_order_from_list l x y -> In x l /\ In y l.
Proof.
  unfold total_order_from_list; ins; desf.
  eauto 10 using in_or_app, in_eq, in_cons.
Qed.

Lemma total_order_from_list_in1 A (l: list A) x y :
  total_order_from_list l x y -> In x l.
Proof.
  unfold total_order_from_list; ins; desf.
  eauto 10 using in_or_app, in_eq, in_cons.
Qed.

Lemma total_order_from_list_in2 A (l: list A) x y :
  total_order_from_list l x y -> In y l.
Proof.
  unfold total_order_from_list; ins; desf.
  eauto 10 using in_or_app, in_eq, in_cons.
Qed.

Lemma total_order_from_list_trans A (l : list A) (ND: NoDup l) x y z :
  total_order_from_list l x y ->
  total_order_from_list l y z ->
  total_order_from_list l x z.
Proof.
  unfold total_order_from_list; ins; desf.
  replace (l0 ++ x :: l4 ++ y :: l5)
          with ((l0 ++ x :: l4) ++ y :: l5) in H0
    by (rewrite <- app_assoc; ins).
  apply NoDup_eq_simpl in H0; try rewrite <- app_assoc; ins; desf.
  eexists l0, (_ ++ y :: _), _; rewrite <- app_assoc; ins.
Qed.

Lemma total_order_from_list_irreflexive A (l : list A) (ND: NoDup l) :
  irreflexive (total_order_from_list l).
Proof.
  red; unfold total_order_from_list; ins; desf.
  induction l1; inv ND; ins; desf; eauto using in_or_app, in_eq.
Qed.

Lemma total_order_from_list_helper A (l : list A) (ND: NoDup l) :
  forall a b (IMM: immediate (total_order_from_list l) a b),
    (forall x, total_order_from_list l a x <-> x = b \/ total_order_from_list l b x) /\
    (forall x, total_order_from_list l x b <-> x = a \/ total_order_from_list l x a).
Proof.
  unfold immediate; ins; desf. 
  red in IMM; desf.
  assert (l2 = nil); desf; ins.
  { destruct l2 as [|c ?]; ins; destruct (IMM0 c).
    eexists l1, nil, _; ins; eauto.
    eexists (l1 ++ a :: nil), _, _; rewrite <- app_assoc; ins; eauto. 
  }
  rewrite nodup_app, !nodup_cons in *; desc.
  intuition;
  repeat first [rewrite total_order_from_list_app in * |
                rewrite total_order_from_list_cons in *]; ins; desf; eauto 8;
  try solve [exfalso; eauto using in_eq, in_cons, total_order_from_list_in1,
                      total_order_from_list_in2].
Qed.

(** Construct a union of total orders from a list of element lists *)
(******************************************************************************)

Definition mk_tou A (ll: list (list A)) x y :=
  exists l, In l ll /\ total_order_from_list l x y.

Lemma mk_tou_trans A (ll : list (list A)) (ND: NoDup (concat ll)) x y z :
  mk_tou ll x y ->
  mk_tou ll y z ->
  mk_tou ll x z.
Proof.
  unfold mk_tou; ins; desf. 
  assert (l0 = l); subst.
    by eapply NoDup_concat_simpl; 
       eauto using total_order_from_list_in1, total_order_from_list_in2.
  apply in_split_perm in H0; desc.
  rewrite H0, concat_cons, nodup_app in ND; desc.
  eauto using total_order_from_list_trans. 
Qed.

Lemma mk_tou_irreflexive A (ll : list (list A)) (ND: NoDup (concat ll)) :
  irreflexive (mk_tou ll).
Proof.
  red; unfold mk_tou; ins; desf.
  eapply total_order_from_list_irreflexive in H0; eauto using NoDup_concatD.
Qed.

Lemma mk_tou_in1 A ll (x y : A) :
  mk_tou ll x y -> In x (concat ll).
Proof.
  unfold mk_tou; ins; desf.
  eauto using in_concat, total_order_from_list_in1.
Qed.

Lemma mk_tou_in2 A ll (x y : A) :
  mk_tou ll x y -> In y (concat ll).
Proof.
  unfold mk_tou; ins; desf.
  eauto using in_concat, total_order_from_list_in2.
Qed.

Lemma mk_tou_trivial A ll1 l1 l2 ll2 (a b : A) :
  mk_tou (ll1 ++ (l1 ++ a :: b :: l2) :: ll2) a b.
Proof.
  by eexists; split; eauto using in_or_app, in_eq; eexists _, nil, _.
Qed.

Lemma mk_tou_immediateD A ll (a b : A) :
  immediate (mk_tou ll) a b ->
  exists ll1 l1 l2 ll2, ll = ll1 ++ (l1 ++ a :: b :: l2) :: ll2.
Proof.
  unfold mk_tou, immediate; ins; desf.
  apply in_split in H; desf; red in H1; desf.
  destruct l3 as [|c ?]; ins; eauto.
  edestruct (H0 c); eexists; split; eauto using in_or_app, in_eq.
    by eexists _, nil, _; ins. 
  by eexists (_ ++ _ :: nil), _, _; rewrite <- app_assoc; ins.
Qed. 

Lemma mk_tou_immediate A ll1 l1 l2 ll2 (a b : A) :
  NoDup (concat (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)) ->
  immediate (mk_tou (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)) a b.
Proof.
  unfold mk_tou; red; ins; split; ins; desf.
  by eexists; split; eauto using in_or_app, in_eq; eexists _, nil, _.
  assert (l0 = l); subst.
    by eapply NoDup_concat_simpl; 
       eauto using total_order_from_list_in1, total_order_from_list_in2.
  assert (l = l1 ++ a :: b :: l2); subst.
    by eapply NoDup_concat_simpl; 
       eauto using in_or_app, in_eq, total_order_from_list_in1.
  rewrite concat_app, concat_cons in H.
  apply nodup_append_right, nodup_append_left in H. 
  unfold total_order_from_list in *; desf.
  apply NoDup_eq_simpl in R3; desf.
  destruct l3; ins; desf.
    by rewrite R0, nodup_app, nodup_cons in *; desf; eauto using in_or_app, in_eq.
  replace (l0 ++ a :: a0 :: l3 ++ c :: l4) 
    with ((l0 ++ a :: a0 :: l3) ++ c :: l4) in R0
    by (rewrite <- app_assoc; done).
  eapply NoDup_eq_simpl in R0; desf. 
    by rewrite !nodup_app, !nodup_cons in *; desf; 
       eauto 8 using in_or_app, in_eq, in_cons.
  rewrite <- app_assoc; ins.
Qed.

Lemma mk_tou_helper A (ll : list (list A)) (ND: NoDup (concat ll)) :
  forall a b (IMM: immediate (mk_tou ll) a b),
    (forall x, mk_tou ll a x <-> x = b \/ mk_tou ll b x) /\
    (forall x, mk_tou ll x b <-> x = a \/ mk_tou ll x a).
Proof.
  unfold mk_tou, immediate; ins; desf.
  edestruct total_order_from_list_helper with (l:=l); eauto using NoDup_concatD.
  split; ins; eauto 8.
  clear IMM0; assert (X:=IMM1); apply total_order_from_list_in in X; desc.
  intuition; desf; eauto.
    assert (l0 = l); [|by subst; rewrite H in *; desf; eauto].
    by eauto using NoDup_concat_simpl, total_order_from_list_in1. 

    eexists; split; eauto.
    assert (l0 = l); [|by subst; rewrite H in *; desf; eauto].
    by eauto using NoDup_concat_simpl, total_order_from_list_in1.

    destruct (classic (x = a)); eauto.
    right; eexists; split; eauto.
    assert (l0 = l); [|by subst; rewrite H0 in *; desf; eauto].
    by eauto using NoDup_concat_simpl, total_order_from_list_in2.

    eexists; split; eauto.
    assert (l0 = l); [|by subst; rewrite H0 in *; desf; eauto].
    by eauto using NoDup_concat_simpl, total_order_from_list_in2. 
Qed.

Lemma mk_tou_insert :
  forall A ll1 (l1: list A) a l2 ll2 x y,
    mk_tou (ll1 ++ (l1 ++ l2) :: ll2) x y ->
    mk_tou (ll1 ++ (l1 ++ a :: l2) :: ll2) x y.
Proof.
  unfold mk_tou; ins; desf; rewrite in_app_iff in *; ins; desf;
  eauto 8 using in_or_app, in_eq, in_cons, total_order_from_list_insert.
Qed.

Lemma mk_tou_remove :
  forall A ll1 (l1: list A) a l2 ll2 x y,
    mk_tou (ll1 ++ (l1 ++ a :: l2) :: ll2) x y ->
    x <> a -> y <> a ->
    mk_tou (ll1 ++ (l1 ++ l2) :: ll2) x y.
Proof.
  unfold mk_tou; ins; desf; rewrite in_app_iff in *; ins; desf;
  eauto 8 using in_or_app, in_eq, in_cons, total_order_from_list_remove.
Qed.

Lemma mk_tou_swap :
  forall A ll1 (l1: list A) a b l2 ll2 x y, 
    mk_tou (ll1 ++ (l1 ++ a :: b :: l2) :: ll2) x y ->
    (x = a -> b = y -> False) ->
    mk_tou (ll1 ++ (l1 ++ b :: a :: l2) :: ll2) x y.
Proof.
  unfold mk_tou; ins; desf; rewrite in_app_iff in *; ins; desf;
  eauto 8 using in_or_app, in_eq, in_cons, total_order_from_list_swap.
Qed.


(** Construct a program order for [init ; (l1 || .. || ln)] *)
(******************************************************************************)

Definition mk_po A init ll (x y: A) :=
  In x init /\ In y (concat ll) \/ mk_tou ll x y.

Lemma mk_po_trans A init ll (D: NoDup (init ++ concat ll)) (x y z : A) :
  mk_po init ll x y ->
  mk_po init ll y z ->
  mk_po init ll x z.
Proof.
  unfold mk_po; ins; rewrite nodup_app in *; desf;
    eauto using mk_tou_trans, mk_tou_in2.
  exfalso; eauto using mk_tou_in1, mk_tou_in2.
Qed.

Lemma transitive_mk_po A (i: list A) ll :
  NoDup (i ++ concat ll) ->
  transitive (mk_po i ll).
Proof. red; ins; eauto using mk_po_trans. Qed.

Lemma mk_po_irreflexive A (init : list A) ll
  (ND: NoDup (init ++ concat ll)) x :
  mk_po init ll x x -> 
  False.
Proof.
  unfold mk_po; ins; rewrite nodup_app in *; desf; eauto. 
  eapply mk_tou_irreflexive; eauto. 
Qed.

Lemma mk_po_helper A init (ll : list (list A)) (ND: NoDup (init ++ concat ll)) :
  forall a (NI: ~ In a init) b (IMM: immediate (mk_po init ll) a b),
    (forall x, mk_po init ll a x <-> x = b \/ mk_po init ll b x) /\
    (forall x, mk_po init ll x b <-> x = a \/ mk_po init ll x a).
Proof.
  unfold mk_po, immediate; ins; desf.
  rewrite nodup_app in ND; desc.
  apply mk_tou_helper with (a:=a) (b:=b) in ND0; desc.
  2: by split; ins; eauto.
  clear IMM0; split; ins.
    by rewrite ND0; intuition; exfalso; eauto using mk_tou_in2.
  by rewrite ND2; intuition; eauto using mk_tou_in1, mk_tou_in2.
Qed.

Lemma mk_po_in1 A init ll (x y : A) :
  mk_po init ll x y -> In x (init ++ concat ll).
Proof.
  unfold mk_po; ins; desf; eauto using in_or_app, mk_tou_in1.
Qed.

Lemma mk_po_in2 A init ll (x y : A) :
  mk_po init ll x y -> In y (concat ll).
Proof.
  unfold mk_po; ins; desf; eauto using in_or_app, mk_tou_in2.
Qed.

Lemma mk_po_in2_weak A init ll (x y : A) :
  mk_po init ll x y -> In y (init ++ concat ll).
Proof.
  unfold mk_po; ins; desf; eauto using in_or_app, mk_tou_in2.
Qed.

Lemma mk_po_trivial A init ll1 l1 l2 ll2 (a b : A) :
  mk_po init (ll1 ++ (l1 ++ a :: b :: l2) :: ll2) a b.
Proof.
  right; apply mk_tou_trivial.
Qed.

Lemma mk_po_immediateD A init ll (a b : A) :
  immediate (mk_po init ll) a b ->
  ~ In a init ->
  exists ll1 l1 l2 ll2, ll = ll1 ++ (l1 ++ a :: b :: l2) :: ll2.
Proof.
  ins; eapply mk_tou_immediateD; unfold immediate, mk_po in *; desf; eauto.
Qed.

Lemma mk_po_immediate A init ll1 l1 l2 ll2 (a b : A) :
  NoDup (init ++ concat (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)) ->
  immediate (mk_po init (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)) a b.
Proof.
  rewrite nodup_app; unfold mk_po; ins; desc. 
  unfold mk_po; split; ins; desf;
    eauto 7 using in_concat, in_or_app, in_eq, in_cons, mk_tou_in1, mk_tou_in2.
    right; apply mk_tou_immediate; eauto.
  eapply mk_tou_immediate; eauto.
Qed.

Lemma mk_po_insert :
  forall A init ll1 (l1: list A) a l2 ll2 x y,
    mk_po init (ll1 ++ (l1 ++ l2) :: ll2) x y ->
    mk_po init (ll1 ++ (l1 ++ a :: l2) :: ll2) x y.
Proof.
  unfold mk_po; ins; desf; eauto using mk_tou_insert.
  rewrite concat_app, concat_cons, <- app_assoc, !in_app_iff in *.
  ins; desf; eauto 8.
Qed.

Lemma mk_po_remove :
  forall A init ll1 (l1: list A) a l2 ll2 x y,
    mk_po init (ll1 ++ (l1 ++ a :: l2) :: ll2) x y ->
    x <> a -> y <> a ->
    mk_po init (ll1 ++ (l1 ++ l2) :: ll2) x y.
Proof.
  unfold mk_po; ins; desf; eauto using mk_tou_remove.
  rewrite concat_app, concat_cons, <- app_assoc, !in_app_iff in *.
  ins; desf; eauto 8.
Qed.

Lemma mk_po_swap :
  forall A init ll1 (l1: list A) a b l2 ll2 x y, 
    mk_po init (ll1 ++ (l1 ++ a :: b :: l2) :: ll2) x y ->
    (x = a -> b = y -> False) ->
    mk_po init (ll1 ++ (l1 ++ b :: a :: l2) :: ll2) x y.
Proof.
  unfold mk_po; ins; desf; eauto using mk_tou_swap.
  rewrite concat_app, concat_cons, <- app_assoc, !in_app_iff in *.
  ins; desf; eauto 8.
Qed.


(** Reordering of adjacent actions in a partial order *)
(******************************************************************************)

Section ReorderSection.

Variable A : Type.
Implicit Types po : relation A. 
Implicit Types a b : A.

Definition reorder po a b x y := 
  po x y /\ ~ (x = a /\ y = b) \/ x = b /\ y = a.

Lemma reorderK po a b (NIN: ~ po b a) (IN: po a b) :
  reorder (reorder po a b) b a <--> po. 
Proof.
  unfold reorder; split; red; ins; desf; intuition. 
  destruct (classic (x = a)); desf; destruct (classic (y = b)); desf; intuition;
  left; intuition; desf.
Qed. 

Lemma Permutation_reord i ll1 l1 a b l2 ll2 : 
  Permutation (i ++ concat (ll1 ++ (l1 ++ b :: a :: l2) :: ll2))
              (i ++ concat (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)).
Proof.
  rewrite !concat_app, !concat_cons; ins; 
  eauto using Permutation_app, perm_swap.
Qed.

Lemma mk_po_reorder init ll1 l1 a b l2 ll2 :
  NoDup (init ++ concat (ll1 ++ (l1 ++ b :: a :: l2) :: ll2)) ->
  reorder (mk_po init (ll1 ++ (l1 ++ a :: b :: l2) :: ll2)) a b <-->
  mk_po init (ll1 ++ (l1 ++ b :: a :: l2) :: ll2).
Proof.
  unfold reorder; split; red; ins; desf; eauto using mk_po_swap, mk_po_trivial.
  destruct (classic (x = b /\ y = a)); eauto 8 using mk_po_swap, mk_po_trivial.
  left; split; ins; desf; eauto using mk_po_swap, mk_po_trivial.
  intro; desf; eauto 8 using mk_po_trans, mk_po_trivial, mk_po_irreflexive. 
Qed.

End ReorderSection.
