(******************************************************************************)
(** * Maximal elements of relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnRelationsBasic.
Require Import Classical NPeano Omega Setoid.

Set Implicit Arguments.


Definition max_elt A (rel: relation A) (a : A) :=
  forall b (REL: rel a b), False.

Definition wmax_elt A (rel: relation A) (a : A) :=
  forall b (REL: rel a b), a = b.


Section BasicProperties.

Variables A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma max_elt_weaken : max_elt r a -> wmax_elt r a.
Proof.
  red; ins; exfalso; eauto.
Qed.

Lemma max_elt_union : max_elt r a -> max_elt r' a -> max_elt (r +++ r') a.
Proof.
  unfold union; red; ins; desf; eauto.
Qed.  

Lemma wmax_elt_union : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r +++ r') a.
Proof.
  unfold union; red; ins; desf; eauto.
Qed.  

Lemma max_elt_t : max_elt r a -> max_elt (clos_trans r) a.
Proof.
  red; ins; apply clos_trans_t1n in REL; induction REL; eauto.
Qed.

Lemma wmax_elt_rt : wmax_elt r a -> wmax_elt (clos_refl_trans r) a.
Proof.
  red; ins; apply clos_rt_rtn1 in REL; induction REL; desf; eauto.
Qed.

Lemma wmax_elt_t : wmax_elt r a -> wmax_elt (clos_trans r) a.
Proof.
  by red; ins; eapply wmax_elt_rt, inclusion_t_rt.
Qed.

Lemma wmax_elt_eqv (f: A -> Prop) : wmax_elt (eqv_rel f) a.
Proof. 
  unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmax_elt_restr_eq B (f: A -> B) :
  wmax_elt r a -> wmax_elt (restr_eq_rel f r) a. 
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto. 
Qed.

Lemma max_elt_restr_eq B (f: A -> B) :
  max_elt r a -> max_elt (restr_eq_rel f r) a. 
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto. 
Qed.

Lemma wmax_elt_r :
  wmax_elt r a -> wmax_elt (clos_refl r) a.
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma max_elt_seq1 : max_elt r a -> max_elt (r ;; r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq2 : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r ;; r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq1 : max_elt r a -> wmax_elt (r ;; r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma max_elt_seq2 : wmax_elt r a -> max_elt r' a -> max_elt (r ;; r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

End BasicProperties.

Hint Immediate max_elt_weaken : rel.
Hint Resolve wmax_elt_union max_elt_union : rel.
Hint Resolve wmax_elt_t wmax_elt_r wmax_elt_rt max_elt_t : rel.
Hint Resolve max_elt_restr_eq wmax_elt_restr_eq : rel.
Hint Resolve max_elt_seq1 max_elt_seq2 wmax_elt_seq1 wmax_elt_seq2 : rel.

Lemma seq_max X (rel rel' : relation X) b 
      (MAX: max_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; rel' <--> (fun _ _ => False).
Proof.
  unfold seq; split; red; ins; desf. 
  apply COD in H; desf; eauto. 
Qed.

Lemma seq_max_t X (rel rel' : relation X) b 
      (MAX: max_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; clos_trans rel' <--> (fun _ _ => False).
Proof.
  eauto using seq_max with rel.
Qed.

Lemma seq_max_rt X (rel rel' : relation X) b
      (MAX: max_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; clos_refl_trans rel' <--> rel. 
Proof.
  rewrite crtE; rel_simpl; rewrite seq_max_t; rel_simpl. 
Qed.

Lemma seq_max_r X (rel rel' : relation X) b
      (MAX: max_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; clos_refl rel' <--> rel. 
Proof.
  rewrite crE; rel_simpl; rewrite seq_max; rel_simpl. 
Qed.

Lemma seq_eq_max X (rel : relation X) b (MAX: max_elt rel b) : 
  <| eq b |> ;; rel <--> (fun _ _ => False).
Proof.
  eapply seq_max; unfold eqv_rel; ins; desf; eauto.
Qed.

Lemma seq_eq_max_t X (rel : relation X) b (MAX: max_elt rel b) :
  <| eq b |> ;; clos_trans rel <--> (fun _ _ => False).
Proof.
  eauto using seq_eq_max with rel. 
Qed.

Lemma seq_eq_max_rt X (rel : relation X) b (MAX: max_elt rel b) :
  <| eq b |> ;; clos_refl_trans rel <--> <| eq b |>.
Proof.
  rewrite crtE; rel_simpl; rewrite seq_eq_max_t; rel_simpl. 
Qed.

Lemma seq_eq_max_r X (rel : relation X) b (MAX: max_elt rel b) :
  <| eq b |> ;; clos_refl rel <--> <| eq b |>.
Proof.
  rewrite crE; rel_simpl; rewrite seq_eq_max; rel_simpl.
Qed.

Lemma seq_singl_max X (rel : relation X) a b (MAX: max_elt rel b) :
  singl_rel a b ;; rel <--> (fun _ _ => False).
Proof.
  unfold singl_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_singl_max_t X (rel : relation X) a b (MAX: max_elt rel b) :
  singl_rel a b ;; clos_trans rel <--> (fun _ _ => False).
Proof.
  eauto using seq_singl_max with rel. 
Qed.

Lemma seq_singl_max_rt X (rel : relation X) a b (MAX: max_elt rel b) :
  singl_rel a b ;; clos_refl_trans rel <--> singl_rel a b.
Proof.
  rewrite crtE; rel_simpl; rewrite seq_singl_max_t; rel_simpl. 
Qed.

Lemma seq_singl_max_r X (rel : relation X) a b (MAX: max_elt rel b) :
  singl_rel a b ;; clos_refl rel <--> singl_rel a b.
Proof.
  rewrite crE; rel_simpl; rewrite seq_singl_max; rel_simpl. 
Qed.

Lemma seq_wmax X (rel rel' : relation X) b 
      (MAX: wmax_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  inclusion (rel ;; rel') rel.
Proof.
  unfold seq; red; ins; desf; eauto.
  specialize (COD _ _ H); desf; apply MAX in H0; desf.
Qed.

Lemma seq_wmax_t X (rel rel' : relation X) b
      (MAX: wmax_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  inclusion (rel ;; clos_trans rel') rel.
Proof.
  eauto using seq_wmax with rel. 
Qed.

Lemma seq_wmax_rt X (rel rel' : relation X) b 
      (MAX: wmax_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; clos_refl_trans rel' <--> rel.
Proof.
  rewrite crtE; split; rel_simpl; rewrite seq_wmax_t; rel_simpl. 
Qed.

Lemma seq_wmax_r X (rel rel' : relation X) b 
      (MAX: wmax_elt rel' b) (COD: forall x y, rel x y -> y = b) :
  rel ;; clos_refl rel' <--> rel.
Proof.
  rewrite crE; split; rel_simpl; rewrite seq_wmax; rel_simpl. 
Qed.

Lemma seq_eq_wmax X (rel : relation X) b (MAX: wmax_elt rel b) :
  inclusion (<| eq b |> ;; rel) <| eq b |>.
Proof.
  eapply seq_wmax; unfold eqv_rel; ins; desf. 
Qed.

Lemma seq_eq_wmax_t X (rel : relation X) b (MAX: wmax_elt rel b) :
  inclusion (<| eq b |> ;; clos_trans rel) <| eq b |>.
Proof.
  eauto using seq_eq_wmax with rel. 
Qed.

Lemma seq_eq_wmax_rt X (rel : relation X) b (MAX: wmax_elt rel b) :
  <| eq b |> ;; clos_refl_trans rel <--> <| eq b |>.
Proof.
  rewrite crtE; split; rel_simpl; rewrite seq_eq_wmax_t; rel_simpl. 
Qed.

Lemma seq_eq_wmax_r X (rel : relation X) b (MAX: wmax_elt rel b) :
  <| eq b |> ;; clos_refl rel <--> <| eq b |>.
Proof.
  rewrite crE; split; rel_simpl; rewrite seq_eq_wmax; rel_simpl. 
Qed.

Lemma seq_singl_wmax X (rel : relation X) a b (MAX: wmax_elt rel b) :
  inclusion (singl_rel a b ;; rel) (singl_rel a b).
Proof.
  unfold singl_rel, seq; red; ins; desf; eauto.
  apply MAX in H0; desf.
Qed.

Lemma seq_singl_wmax_t X (rel : relation X) a b (MAX: wmax_elt rel b) :
  inclusion (singl_rel a b ;; clos_trans rel)
            (singl_rel a b).
Proof.
  eauto using seq_singl_wmax with rel. 
Qed.

Lemma seq_singl_wmax_rt X (rel : relation X) a b (MAX: wmax_elt rel b) :
  singl_rel a b ;; clos_refl_trans rel <--> singl_rel a b.
Proof.
  rewrite crtE; split; rel_simpl; rewrite seq_singl_wmax_t; rel_simpl. 
Qed.

Lemma seq_singl_wmax_r X (rel : relation X) a b (MAX: wmax_elt rel b) :
  singl_rel a b ;; clos_refl rel <--> singl_rel a b.
Proof.
  rewrite crE; split; rel_simpl; rewrite seq_singl_wmax; rel_simpl. 
Qed.

