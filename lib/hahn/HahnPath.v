(******************************************************************************)
(** * Lemmas about paths and cycles *)
(******************************************************************************)

Require Import Classical HahnBase HahnList HahnRelationsBasic HahnMaxElt.

Set Implicit Arguments.

(** Minimum cycle lemma *)

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


(******************************************************************************)

Lemma path_decomp_u1 X (rel : relation X) a b : 
  clos_trans (rel +++ singl_rel a b) <-->
  clos_trans rel +++ clos_refl_trans rel ;; singl_rel a b ;; clos_refl_trans rel.
Proof.
  split. 
  { unfold inclusion, union, singl_rel, seq. 
    induction 1; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  }
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct, ct_begin; eauto with rel.
Qed.

Lemma cycle_decomp_u1 X (rel : relation X) a b c : 
  clos_trans (rel +++ singl_rel a b) c c ->
  clos_trans rel c c \/ clos_refl_trans rel b a.
Proof.
  ins; apply path_decomp_u1 in H.
  unfold seq, union, singl_rel in *; desf; eauto using clos_refl_trans.
Qed.

Lemma acyclic_decomp_u1 X (rel : relation X) a b : 
  acyclic rel ->
  ~ clos_refl_trans rel b a ->
  acyclic (rel +++ singl_rel a b).
Proof.
  unfold acyclic, irreflexive; ins. 
  exploit cycle_decomp_u1; ins; desf; eauto.
Qed.

Lemma path_decomp_u1_max X (rel : relation X) a b (MAX: max_elt rel b) :
  clos_trans (rel +++ singl_rel a b) <-->
  clos_trans rel +++ clos_refl_trans rel ;; singl_rel a b.
Proof.
  rewrite path_decomp_u1, seq_singl_max_rt; vauto.
Qed.

Lemma acyclic_u1_max X (rel : relation X) a b (MAX: max_elt rel b) :
  acyclic (rel +++ singl_rel a b) <->
  acyclic rel /\ a <> b.
Proof.
  unfold acyclic; 
  rewrite path_decomp_u1_max, irreflexive_union, irreflexive_seqC, seq_singl_max_rt;
  intuition; unfold irreflexive, singl_rel in *; ins; desf; eauto.
Qed.

(******************************************************************************)

Lemma path_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b)
    (IRR: irreflexive (clos_refl_trans rel1 ;; clos_trans rel2)),
  clos_trans (rel1 +++ rel2) <-->
  clos_trans rel1 +++
  clos_refl_trans rel1 ;; clos_trans rel2 ;; clos_refl_trans rel1. 
Proof.
  split; ins.
  { intros ? ? C; unfold seq, union in *.
    induction C; desf; eauto 8 using rt_refl, clos_trans;
      eauto 8 using clos_trans_in_rt, rt_trans.

    destruct (classic (z1 = z3)) as [|NEQ]; desf;
      eauto 6 using t_trans, rt_trans.
    eapply T in NEQ; desf.
    by exfalso; eauto 10 using clos_trans, rt_trans.
    by eauto 8 using clos_trans, rt_trans.
    by eapply t_rt_step in IHC0; desf; exploit D; eauto; tauto.
    by eapply t_rt_step in IHC4; desf; exploit D; eauto; tauto.
  }
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct with (rel := rel1 +++ rel2),
          <- ct_rt with (rel := rel1 +++ rel2); eauto 8 with rel.
Qed.

Lemma acyclic_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b)
    (A: acyclic rel1)
    (IRR: irreflexive (clos_refl_trans rel1 ;; clos_trans rel2)),
    acyclic (rel1 +++ rel2).
Proof.
  red; ins.
  rewrite path_decomp_u_total; eauto. 
  eapply irreflexive_union; split; ins.
  by rewrite irreflexive_seqC, seqA, rt_rt, irreflexive_seqC.
Qed.

(*
Lemma cycle_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b) x
    (C: clos_trans (fun a b => rel1 a b \/ rel2 a b) x x),
    clos_trans rel1 x x \/
    (exists m n, clos_refl_trans rel1 m n /\ clos_trans rel2 n m).
Proof.
  ins; exploit path_decomp_u_total; eauto; ins; desf; eauto 8 using rt_trans.
Qed. *)

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
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False),
    clos_trans (rel +++ rel') <-->
    clos_trans rel +++ clos_trans rel' +++
    clos_trans rel' ;; clos_trans rel.
Proof.
  split; cycle 1.
    repeat apply inclusion_union_l; eauto with rel.
    by repeat apply inclusion_seq_trans; eauto with rel; vauto.
  intros ? ? T; unfold union, seq in *.
  induction T; desf; eauto 6 using clos_trans;
    try by exfalso; eauto using clos_trans_disj_rel.
Qed.

Lemma acyclic_decomp_u_1 :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False)
    (A1: acyclic rel)
    (A2: acyclic rel'),
    acyclic (rel +++ rel').
Proof.
  unfold acyclic; ins; rewrite path_decomp_u_1; eauto.
  unfold union, seq, irreflexive; ins; desf; 
  eauto using clos_trans_disj_rel.
Qed.

Lemma path_decomp_u_2 :
  forall (X : Type) (rel rel' : relation X)
         (F: inclusion (rel' ;; rel) (fun _ _ => False)),
    clos_trans (rel +++ rel') <--> 
    clos_trans rel +++ clos_refl_trans rel ;; clos_trans rel'.
Proof.
  ins; rewrite unionC, path_decomp_u_1.
    by rewrite crtE; rel_simpl; rewrite unionAC, unionA; vauto.
  unfold seq in *; eauto.
Qed.

Lemma path_decomp_u_3 :
  forall (X : Type) (rel rel' : relation X)
         (F: inclusion (rel' ;; rel) (fun _ _ => False))
         (F': transitive rel'),
    clos_trans (rel +++ rel') <--> 
    clos_trans rel +++ clos_refl_trans rel ;; rel'.
Proof.
  ins; rewrite path_decomp_u_2; ins.
  split; repeat apply inclusion_union_l; eauto with rel.
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
         (B: forall x y (R: r' x y), bdom y),
    clos_trans (r +++ r') <-->
    r +++
      clos_trans (r ;; eqv_rel adom +++ r') ;;
      clos_refl (eqv_rel bdom ;; r).
Proof.
  split.
    rewrite seq_eqv_r, seq_eqv_l.
    unfold seq, union, clos_refl; intros ? ? P.
    apply clos_trans_tn1 in P; induction P; desf; eauto 14 using clos_trans; clear P.
    apply clos_trans_t1n in IHP; induction IHP; 
    intuition; desf; eauto 14 using clos_trans.
  rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
  eauto using inclusion_t_r_t with rel.
Qed.

Lemma path_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r' x y), adom x)
         (B: forall x y (R: r' x y), bdom y),
    clos_trans (r +++ r') <-->
    clos_trans r +++
      clos_trans (clos_trans r ;; eqv_rel adom +++ r') ;;
      clos_refl (eqv_rel bdom ;; clos_trans r).
Proof.
  by ins; rewrite <- path_tur, clos_trans_union_ct; eauto; vauto. 
Qed. 

Lemma path_tur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (T: transitive r')  
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    clos_trans (r +++ r') <-->
    r' +++
      clos_refl (r' ;; eqv_rel adom) ;;
      clos_trans (r +++ eqv_rel bdom ;; r').
Proof.
  split.
    rewrite seq_eqv_r, seq_eqv_l.
    unfold seq, union, clos_refl; intros ? ? P.
    apply clos_trans_t1n in P; induction P; desf; eauto 14 using clos_trans; clear P.
    apply clos_trans_tn1 in IHP0; induction IHP0; 
    intuition; desf; eauto 14 using clos_trans.
  rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
  eauto using inclusion_r_t_t with rel.
Qed. 

Lemma path_ur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    clos_trans (r +++ r') <-->
    clos_trans r' +++
      clos_refl (clos_trans r' ;; eqv_rel adom) ;;
      clos_trans (r +++ eqv_rel bdom ;; clos_trans r').
Proof.
  ins; rewrite <- path_tur2; eauto; vauto. 
  rewrite unionC, <- clos_trans_union_ct, unionC; eauto; vauto. 
Qed. 


(*
Lemma seq_cr_cr A (rel rel' : relation A) :
  clos_refl rel ;; clos_refl rel' <-->
  clos_refl (rel ;; rel').
Proof.
  rewrite !crE, seq_union_l, seq_id_l, seq_union_r, seq_id_r.
*)

Lemma acyclic_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    acyclic r' ->
    acyclic (r +++ eqv_rel bdom ;; clos_trans r' ;; eqv_rel adom) ->
    acyclic (r +++ r').
Proof.
  unfold acyclic; ins.
  rewrite path_ur2; eauto.
  rewrite (unionC r), path_ur, <- (unionC r); eauto.
  rewrite seq_union_r, !irreflexive_union; repeat split; ins.
  eapply irreflexive_inclusion, H.
  rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r, ct_of_ct, cr_of_t, rt_ct; 
    auto with rel.
  rewrite irreflexive_seqC, seqA, inclusion_ct_seq_eqv_l, !seqA.
  rewrite (seq2 (seq_eqvK _)); do 2 rewrite ct_of_ct at 1.
  rewrite !crE, !seq_union_l, !seq_id_l, !seq_union_r, !seq_id_r.
  rewrite !irreflexive_union; repeat split; ins.

  rewrite ct_end, seqA, !seq_union_l, !seqA.
  rewrite <- rt_ct in H0; eapply irreflexive_inclusion, H0.
  eapply inclusion_seq_mon, inclusion_union_l; ins. 
    assert (EQ: r <--> r ;; eqv_rel bdom).
      by split; rewrite seq_eqv_r; red; ins; desf; eauto. 
    by rewrite EQ at 1; rewrite seqA;
       eauto using inclusion_step2_ct with rel.
  rewrite (inclusion_seq_eqv_l (dom:=adom)).
  rewrite <- inclusion_union_r2. 
  by rewrite <- seqA with (r1 := clos_trans _), ct_ct; eauto with rel.

  rewrite ct_begin, irreflexive_seqC, <- !seqA, !seq_union_r, !seqA.
  rewrite <- ct_rt in H0; eapply irreflexive_inclusion, H0.
  apply inclusion_seq_mon; ins.
  apply inclusion_union_l; ins. 
    assert (EQ: r <--> eqv_rel adom ;; r).
      by split; rewrite seq_eqv_l; red; ins; desf; eauto. 
    by rewrite EQ at 1; rewrite <- !seqA;
       eauto using inclusion_step2_ct with rel.
  rewrite <- inclusion_union_r2. 
  apply inclusion_step_t, inclusion_seq_mon; ins.
  by rewrite (inclusion_seq_eqv_l (dom:=bdom)), <- seqA, ct_ct.

  rewrite seqA, <- seqA with (r1 := clos_trans r') (r2 := clos_trans r'), ct_ct.
  eapply irreflexive_inclusion, H0; eauto using inclusion_t_r_t with rel.
Qed.

(*
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
*)


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



Lemma path_ut_helper :
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

Lemma path_ut :
  forall X (r r' : relation X) (T: transitive r'),
    clos_refl_trans (r +++ r') <-->
    clos_refl_trans r ;;
    clos_refl_trans (r' ;; clos_trans r) ;;
    clos_refl r'.
Proof.
  split.
  - unfold seq, union, clos_refl; red; ins; eapply path_ut_helper in H;
    desf; eauto 10.
  - rewrite inclusion_t_rt.
    eauto 10 using inclusion_seq_rt, inclusion_rt_rt2 with rel.
Qed.



Lemma rewrite_trans A (r: relation A) :
  transitive r -> inclusion (r ;; r) r.
Proof.
  unfold inclusion, seq; ins; desf; eauto. 
Qed.

Lemma transitiveI A (r: relation A) :
  inclusion (r ;; r) r -> transitive r.
Proof.
  unfold transitive, inclusion, seq; ins; desf; eauto. 
Qed.


Lemma path_ut2 :
  forall X (r r' : relation X) (T: transitive r'),
    clos_trans (r +++ r') <-->
    clos_trans r +++
      clos_refl_trans r ;; 
      clos_refl_trans (r' ;; clos_trans r) ;;
      r' ;; clos_refl_trans r.
Proof.
  split.
    rewrite crtE at 2; rewrite !seq_union_r, seq_id_r, <- ct_end.
    rewrite ct_begin, path_ut, !seq_union_l, <- !seqA, <- ct_begin; ins.
    
    rewrite (crtE r) at 1; 
      rewrite !seq_union_r, seq_id_r, !seq_union_l, <- ct_begin. 
    rewrite crt_begin at 2; rel_simpl. 
    rewrite !seqA, <- (seqA r'), rewrite_trans, <- !seqA, <- ct_begin; ins.

    rewrite crE, !seq_union_r, !seq_id_r, rewrite_trans; ins; rel_simpl.
    repeat apply inclusion_union_l; eauto 8 with rel;
    rewrite !crtE; rel_simpl.

  apply inclusion_union_l; eauto with rel.
  rewrite inclusion_t_rt.
  rewrite <- 2!(rt_ct (r +++ r')), (ct_begin (r +++ r'));
  eauto 10 using inclusion_rt_rt2, inclusion_seq_rt with rel.
Qed.



Lemma path_utd_helper :
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

Lemma path_utd :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b)
         (I': irreflexive (r' ;; clos_refl_trans r)),
    clos_trans (r +++ r') <-->
    clos_trans r +++
    (clos_refl_trans r ;; r' ;; clos_refl_trans r).
Proof.
  split.
    unfold inclusion, seq, union in *; ins; desf.
    eapply path_utd_helper with (2:=F) in H; desf; eauto 8; exfalso; eauto 8.
  apply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct, ct_begin; eauto with rel.
Qed.

Lemma acyclic_utd :
  forall X (r: relation X) (A: acyclic r) 
         r' (T: transitive r') (IRR: irreflexive r') dom
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b)
         (I': irreflexive (r' ;; clos_trans r)),
  acyclic (r +++ r').
Proof.
  unfold acyclic; ins.
  assert (irreflexive (r';; clos_refl_trans r)).
    by rewrite crtE; rel_simpl; rewrite irreflexive_union.
  unfold acyclic; ins; rewrite path_utd, irreflexive_union; eauto.
  by split; ins; rewrite irreflexive_seqC, seqA, rt_rt.
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
  clos_refl_trans (r +++ r') <-->
  clos_refl_trans (r ;; r') +++
  (clos_refl_trans (r' ;; r) +++
   (r ;; clos_refl_trans (r' ;; r) +++
    r' ;; clos_refl_trans (r ;; r'))).
Proof.
  split.
    eapply inclusion_rt_ind_left; [by vauto|].
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
  clos_trans (r +++ r') <-->
  clos_trans (r ;; r') +++
  (clos_trans (r' ;; r) +++
   (r ;; clos_refl_trans (r' ;; r) +++
    r' ;; clos_refl_trans (r ;; r'))).
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
  acyclic (r +++ r') <-> acyclic (r ;; r').
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


