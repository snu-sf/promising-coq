Require Import HahnBase HahnRelationsBasic.
Require Import Classical Setoid.
Set Implicit Arguments.

Section Domains.

Variable A : Type.

Section Definitions.
  Variable r : relation A.
  Variable d : A -> Prop.

  Definition doma := forall x y (REL: r x y), d x.
  Definition domb := forall x y (REL: r x y), d y.
End Definitions.

Section Lemmas.

  Variables r r' : relation A.
  Variable B : Type.
  Variables f : A -> B.
  Variables d d' : A -> Prop.

  Lemma eqv_doma : doma <| d |> d.
  Proof. unfold doma, eqv_rel; ins; desf. Qed.

  Lemma eqv_domb : domb <| d |> d.
  Proof. unfold domb, eqv_rel; ins; desf. Qed.

  Lemma seq_eqv_doma : doma r d -> doma (<| d' |> ;; r) d.
  Proof. unfold doma, eqv_rel, seq; ins; desf; eauto. Qed.

  Lemma seq_eqv_domb : domb r d -> domb (r ;; <| d' |>) d.
  Proof. unfold domb, eqv_rel, seq; ins; desf; eauto. Qed.

  Lemma restr_eq_rel_doma : doma r d -> doma (restr_eq_rel f r) d.
  Proof. unfold doma, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma restr_eq_rel_domb : domb r d -> domb (restr_eq_rel f r) d.
  Proof. unfold domb, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma seq_doma : doma r d -> doma (r;;r') d. 
  Proof. unfold doma, seq; ins; desf; eauto. Qed.

  Lemma seq_domb : domb r' d -> domb (r;;r') d. 
  Proof. unfold domb, seq; ins; desf; eauto. Qed.

  Lemma union_doma : doma r d -> doma r' d -> doma (r +++ r') d.
  Proof. unfold doma, union; ins; desf; eauto. Qed.

  Lemma union_domb : domb r d -> domb r' d -> domb (r +++ r') d.
  Proof. unfold domb, union; ins; desf; eauto. Qed.

  Lemma ct_doma : doma r d -> doma (clos_trans r) d.
  Proof. induction 2; eauto. Qed.

  Lemma ct_domb : domb r d -> domb (clos_trans r) d.
  Proof. induction 2; eauto. Qed.

  Lemma seq_r_doma : doma r d -> doma r' d -> doma (clos_refl r ;; r') d. 
  Proof. unfold clos_refl, seq; red; ins; desf; eauto. Qed.

  Lemma seq_r_domb : domb r d -> domb r' d -> domb (r ;; clos_refl r') d. 
  Proof. unfold clos_refl, seq; red; ins; desf; eauto. Qed.

  Lemma dom_union x : dom_rel (r +++ r') x <-> dom_rel r x \/ dom_rel r' x.
  Proof. unfold dom_rel, union; split; ins; desf; eauto. Qed.

  Lemma codom_union x : codom_rel (r +++ r') x <-> codom_rel r x \/ codom_rel r' x.
  Proof. unfold codom_rel, union; split; ins; desf; eauto. Qed.

  Lemma dom_eqv x : dom_rel <| d |> x <-> d x.
  Proof. unfold dom_rel, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma codom_eqv x : codom_rel <| d |> x <-> d x.
  Proof. unfold codom_rel, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma dom_eqv1 x : dom_rel (<| d |> ;; r) x <-> d x /\ dom_rel r x.
  Proof. unfold dom_rel, seq, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma codom_eqv1 x : codom_rel (r ;; <| d |>) x <-> codom_rel r x /\ d x.
  Proof. unfold codom_rel, seq, eqv_rel; split; ins; desf; eauto. Qed.

End Lemmas.

End Domains.

Hint Resolve
  eqv_doma seq_eqv_doma restr_eq_rel_doma seq_doma union_doma ct_doma seq_r_doma
  eqv_domb seq_eqv_domb restr_eq_rel_domb seq_domb union_domb ct_domb seq_r_domb
: rel.

Add Parametric Morphism X : (@doma X) with signature 
  inclusion --> eq ==> Basics.impl as doma_mori.
Proof.
  unfold inclusion, doma, Basics.impl; eauto. 
Qed.

Add Parametric Morphism X : (@domb X) with signature 
  inclusion --> eq ==> Basics.impl as domb_mori.
Proof.
  unfold inclusion, domb, Basics.impl; eauto. 
Qed.

Add Parametric Morphism X : (@doma X) with signature 
  same_relation ==> eq ==> iff as doma_more.
Proof.
  by unfold same_relation; split; desc; [rewrite H0|rewrite H]. 
Qed.

Add Parametric Morphism X : (@domb X) with signature 
  same_relation ==> eq ==> iff as domb_more.
Proof.
  by unfold same_relation; split; desc; [rewrite H0|rewrite H]. 
Qed.

Add Parametric Morphism X : (@dom_rel X) with signature 
  same_relation  ==> eq ==> iff as dom_rel_more.
Proof.
  unfold same_relation; intros; unfold dom_rel; split; ins; desc; eauto.
Qed. 

Add Parametric Morphism X : (@codom_rel X) with signature 
  same_relation  ==> eq ==> iff as codom_rel_more.
Proof.
  unfold same_relation; intros; unfold codom_rel; split; ins; desc; eauto.
Qed. 

Hint Rewrite dom_union codom_union dom_eqv codom_eqv dom_eqv1 codom_eqv1 : rel_dom.
