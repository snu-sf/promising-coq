(******************************************************************************)
(** * Extension of a partial order to a total order *)
(******************************************************************************)

Require Import NPeano Omega Setoid Classical.
Require Import HahnBase HahnList HahnRelationsBasic.

Set Implicit Arguments.

(******************************************************************************)
(** Extend an order to make it total on one element. *)

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

(******************************************************************************)
(** Extend an order to make it total on a list of elements. *)

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

(******************************************************************************)
(** Extend an order on [nat] to make it total. *)

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

(******************************************************************************)
(** Add support for rewriting *)

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
  eapply tot_ext_more; try eassumption; symmetry; eauto.
Qed.



