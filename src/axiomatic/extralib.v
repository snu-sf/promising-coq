Require Import Omega.
Require Import Vbase Relations List Permutation Sorting.
Require Import ClassicalDescription Setoid.

Set Implicit Arguments.

(** This file contains a number of basic definitions and lemmas about lists 
    that are missing from the standard library, and a few properties of 
    classical logic. *)

(** Very basic lemmas *)
(******************************************************************************)

Definition appA := app_ass.  

Lemma in_cons_iff A (a b : A) l : In b (a :: l) <-> a = b \/ In b l.
Proof. done. Qed. 

Lemma In_split2 :
  forall A (x: A) l (IN: In x l),
  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1.
Proof.
  induction l; ins; desf; [by eexists nil; ins; eauto|].
  destruct (classic (a = x)); desf; [by eexists nil; ins; eauto|].
  apply IHl in IN; desf; eexists (_ :: _); repeat eexists; ins; intro; desf.
Qed.

Lemma map_eq_app_inv A B (f : A -> B) l l1 l2 :
  map f l = l1 ++ l2 ->
  exists l1' l2', l = l1' ++ l2' /\ map f l1' = l1 /\ map f l2' = l2.
Proof.
  induction[l1] l; ins.
    by destruct l1, l2; ins; eexists nil, nil.
  destruct l1; ins; desf.
    by eexists nil,_; ins.
  eapply IHl in H; desf; eexists (_ :: _), _; split; ins.
Qed.


(** List filtering *)
(******************************************************************************)

Lemma in_filter_iff A l f (x : A) : In x (filter f l) <-> In x l /\ f x.
Proof.
  induction l; ins; try tauto.
  des_if; ins; rewrite IHl; split; ins; desf; eauto.
Qed.

Lemma filter_app A f (l l' : list A) :
  filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
  induction l; ins; desf; ins; congruence.
Qed.

Lemma Permutation_filter A (l l' : list A) (P: Permutation l l') f :
  Permutation (filter f l) (filter f l').
Proof.
  induction P; ins; desf; vauto.
Qed.

Add Parametric Morphism A : (@filter A) with 
  signature eq ==> (@Permutation A) ==> (@Permutation A)
      as filter_mor.
Proof.
  by ins; apply Permutation_filter.
Qed.

(** List flattening *)
(******************************************************************************)

Fixpoint flatten A (l: list (list A)) :=
  match l with 
    | nil => nil 
    | x :: l' => x ++ flatten l' 
  end.

Lemma in_flatten_iff A (x: A) ll :
  In x (flatten ll) <-> exists l, In l ll /\ In x l.
Proof.
  induction ll; ins. 
    by split; ins; desf.
  rewrite in_app_iff, IHll; clear; split; ins; desf; eauto.
Qed.

(** List disjointness *)
(******************************************************************************)

Definition disjoint A (l1 l2 : list A) := 
  forall a (IN1: In a l1) (IN2: In a l2), False. 


(** Remove duplicate list elements (classical) *)
(******************************************************************************)

Fixpoint undup A (l: list A) :=
  match l with nil => nil
    | x :: l =>
      if excluded_middle_informative (In x l) then undup l else x :: undup l
  end.

(** Lemmas about [NoDup] and [undup] *)
(******************************************************************************)

Lemma nodup_one A (x: A) : NoDup (x :: nil).
Proof. vauto. Qed.

Hint Resolve NoDup_nil nodup_one.

Lemma nodup_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (map f l).
Proof.
  induction 1; ins; vauto. 
  constructor; eauto.
  intro; rewrite in_map_iff in *; desf.
  edestruct H1; try eapply H2; eauto.
  intro; desf.
Qed.

Lemma nodup_append_commut:
  forall (A: Type) (a b: list A),
  NoDup (a ++ b) -> NoDup (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A), 
           NoDup (a ++ b) -> ~(In x a) -> ~(In x b) -> 
           NoDup (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto. 
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto. 
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma nodup_cons A (x: A) l:
  NoDup (x :: l) <-> ~ In x l /\ NoDup l.
Proof. split; inversion 1; vauto. Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
  induction l1; ins. 
    by split; ins; desf; vauto.
  rewrite !nodup_cons, IHl1, in_app_iff; unfold disjoint.
  ins; intuition (subst; eauto). 
Qed.

Lemma nodup_append:
  forall (A: Type) (l1 l2: list A),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_right:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_left:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_filter A (l: list A) (ND: NoDup l) f : NoDup (filter f l). 
Proof. 
  induction l; ins; inv ND; desf; eauto using NoDup.
  econstructor; eauto; rewrite in_filter_iff; tauto.
Qed.

Hint Resolve nodup_filter.

Lemma Permutation_nodup A ( l l' : list A) : 
  Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; eauto; rewrite !nodup_cons in *; ins; desf; intuition. 
  eby symmetry in H; eapply H0; eapply Permutation_in.
Qed.

Lemma nodup_eq_one A (x : A) l : 
   NoDup l -> In x l -> (forall y (IN: In y l), y = x) -> l = x :: nil.
Proof.
  destruct l; ins; f_equal; eauto.
  inv H; desf; clear H H5; induction l; ins; desf; case H4; eauto using eq_sym.
  rewrite IHl in H0; ins; desf; eauto.
Qed.

Lemma nodup_consD A (x : A) l : NoDup (x :: l) -> NoDup l.
Proof. inversion 1; desf. Qed.

Lemma nodup_mapD A B (f : A-> B) l : NoDup (map f l) -> NoDup l.
Proof.
  induction l; ins; rewrite !nodup_cons, in_map_iff in *; desf; eauto 8.
Qed.

Lemma In_NoDup_Permutation A (a : A) l (IN: In a l) (ND : NoDup l) : 
  exists l', Permutation l (a :: l') /\ ~ In a l'.
Proof.
  induction l; ins; desf; inv ND; eauto.
  destruct IHl as (l' & ? & ?); eauto.
  destruct (classic (a0 = a)); desf.
  eexists (a0 :: l'); split; try red; ins; desf. 
  eapply Permutation_trans, perm_swap; eauto.
Qed.

Lemma in_undup_iff A (x : A) (l : list A) : In x (undup l) <-> In x l.
Proof. induction l; split; ins; desf; ins; desf; eauto. Qed.

Lemma nodup_undup A (l : list A) : NoDup (undup l).
Proof. induction l; ins; desf; constructor; rewrite ?in_undup_iff in *; eauto. Qed.

Hint Resolve nodup_undup.

Lemma undup_nodup A (l : list A) : NoDup l -> undup l = l.
Proof. induction 1; ins; desf; congruence. Qed.

Lemma Sorted_undup A p (l : list A) :
  StronglySorted p l -> StronglySorted p (undup l).
Proof. 
  induction 1; ins; desf; constructor; eauto.
  rewrite Forall_forall in *; ins; rewrite in_undup_iff in *; eauto.
Qed.

Lemma undup_nonnil A (l : list A) : l <> nil -> undup l <> nil.
Proof.
  induction l; ins; desf.
  by eapply in_undup_iff in i; intro X; rewrite X in *.
Qed.

Lemma Permutation_undup A (l l' : list A) :
  Permutation l l' -> Permutation (undup l) (undup l').
Proof.
  ins; eapply NoDup_Permutation; ins; rewrite !in_undup_iff.
  split; eauto using Permutation_in, Permutation_sym.
Qed. 


(** Function update *)
(******************************************************************************)

Definition upd A B (f : A -> B) a b x :=
  if excluded_middle_informative (x = a) then b else f x.

Lemma upds A B (f: A -> B) a b : upd f a b a = b.
Proof. unfold upd; desf. Qed.

Lemma updo A B (f: A -> B) a b c (NEQ: c <> a) : upd f a b c = f c.
Proof. unfold upd; desf. Qed.

Ltac rupd := repeat first [rewrite upds | rewrite updo ; try done].

Lemma updss A B (f : A -> B) l x y : upd (upd f l x) l y = upd f l y.
Proof.
  extensionality z; unfold upd; desf.
Qed.

Lemma updC A l l' (NEQ: l <> l') B (f : A -> B) x y :
  upd (upd f l x) l' y = upd (upd f l' y) l x.
Proof.
  extensionality z; unfold upd; desf.
Qed.

Lemma updI A B (f : A -> B) a : upd f a (f a) = f. 
Proof.
  extensionality a'; unfold upd; desf.
Qed.

Lemma map_upd_irr A (a: A) l (NIN: ~ In a l) B f (b : B) :
  map (upd f a b) l = map f l.
Proof.
  unfold upd; induction l; ins.
  apply not_or_and in NIN; desf; f_equal; eauto.
Qed.

(** Decidable function update *)
(******************************************************************************)

Definition mupd (A: eqType) B (h : A -> B) y z := 
  fun x => if x == y then z else h x.
Arguments mupd [A B] h y z x.

Lemma mupds (A: eqType) B (f: A -> B) x y : mupd f x y x = y. 
Proof. by unfold mupd; desf; desf. Qed.

Lemma mupdo (A: eqType) B (f: A -> B) x y z : x <> z -> mupd f x y z = f z. 
Proof. by unfold mupd; desf; desf. Qed.

(** Lemmas about sorting *)
(******************************************************************************)

Lemma sorted_perm_eq : forall A (cmp: A -> A -> Prop) 
  (TRANS: transitive _ cmp) 
  (ANTIS: antisymmetric _ cmp)
  l l' (P: Permutation l l')
  (S : StronglySorted cmp l) (S' : StronglySorted cmp l'), l = l'.
Proof.
  induction l; ins.
    by apply Permutation_nil in P; desf.
  assert (X: In a l') by eauto using Permutation_in, Permutation_sym, in_eq.
  apply In_split2 in X; desf; apply Permutation_cons_app_inv in P.
  destruct l1; ins; [by inv S; inv S'; eauto using f_equal|].
  assert (X: In a0 l) by eauto using Permutation_in, Permutation_sym, in_eq.
  inv S; inv S'; rewrite Forall_forall in *; ins.
  destruct X0; left; apply ANTIS; eauto using in_eq, in_or_app.
Qed.

(*
Lemma perm_sort_eq A (l l': list A) (P: Permutation l l') cmp 
    (TOTAL: forall x y, In x l -> In y l -> cmp x y = true \/ cmp y x = true)
    (TRANS: transitive _ cmp) 
    (ANTIS: antisymmetric _ cmp) :
  sort cmp l = sort cmp l'. 
Proof.
  exploit (@sort_sorted A cmp l); eauto.
  exploit (@sort_sorted A cmp l'); 
    eauto 6 using Permutation_in, Permutation_sym.
  ins; eauto using sorted_perm_eq, sort_perm, Permutation_trans, 
                   Permutation_sym.
Qed.


Lemma In_sort A (x: A) cmp l : In x (sort cmp l) <-> In x l.
Proof.
  split; eauto using Permutation_in, sort_perm, Permutation_sym.
Qed.

Lemma NoDup_sort A cmp (l : list A) : NoDup (sort cmp l) <-> NoDup l.
Proof.
  split; eauto using Permutation_nodup, Permutation_sym, sort_perm.
Qed.

Lemma NoDup_sort1 A cmp (l : list A) : NoDup l -> NoDup (sort cmp l).
Proof.
  apply NoDup_sort. 
Qed.

Hint Resolve NoDup_sort1.

Lemma Sorted_total : 
  forall A cmp (R: reflexive _ cmp) (l: list A), StronglySorted cmp l -> 
    forall x y, In x l -> In y l -> 
      cmp x y \/ cmp y x.
Proof.
  induction 2; ins; rewrite Forall_forall in *; desf; desf; eauto.
Qed.

Lemma Sorted_app_end_inv A (cmp : A -> A -> Prop) l x :
  StronglySorted cmp (l ++ x :: nil) ->
  forall y, In y l -> cmp y x.
Proof.
  ins; induction l; ins; inv H; rewrite Forall_forall in *.
  desf; eauto using in_or_app, in_eq.
Qed.
*)

(** [dprod] *)
(******************************************************************************)

Fixpoint dprod A B al (f : A -> list B) :=
  match al with 
    | nil => nil
    | a :: al => map (fun b => (a, b)) (f a) ++ dprod al f
  end.

Lemma in_dprod_iff A B x al (f : A -> list B) :
  In x (dprod al f) <-> In (fst x) al /\ In (snd x) (f (fst x)).
Proof.
  induction al; ins; rewrite ?in_app_iff, ?in_map_iff, ?IHal; try clear IHal;
  split; ins; desf; ins; eauto; destruct x; ins; eauto.
Qed.


(** Miscellaneous *)
(******************************************************************************)

Lemma perm_from_subset : 
  forall A (l : list A) l',
    NoDup l' ->
    (forall x, In x l' -> In x l) ->
    exists l'', Permutation l (l' ++ l''). 
Proof.
  induction l; ins; vauto.
    by destruct l'; ins; vauto; exfalso; eauto.
  destruct (classic (In a l')).

    eapply In_split in H1; desf; rewrite ?nodup_app, ?nodup_cons in *; desf.
    destruct (IHl (l1 ++ l2)); ins. 
      by rewrite ?nodup_app, ?nodup_cons in *; desf; repeat split; ins; red; 
         eauto using in_cons.
      by specialize (H0 x); rewrite in_app_iff in *; ins; desf;
         destruct (classic (a = x)); subst; try tauto; exfalso; eauto using in_eq.
    eexists; rewrite app_ass in *; ins.
    by eapply Permutation_trans, Permutation_middle; eauto.

  destruct (IHl l'); eauto; ins.
    by destruct (H0 x); auto; ins; subst.
  by eexists (a :: _); eapply Permutation_trans, Permutation_middle; eauto.
Qed.


Lemma seq_split_gen : 
  forall l n a,
  n <= a < n + l ->
  seq n l = seq n (a - n) ++ a :: seq (S a) (l + n - a - 1).
Proof.
  induction l; ins; desf; ins; try omega.
    repeat f_equal; omega.
  destruct (eqP n (S n0)); subst.
    replace (n0 - n0) with 0 by omega; ins; repeat f_equal; omega.
  rewrite IHl with (a := S n0); try omega.
  desf; ins; try replace (n0 - n2) with (S (n0 - S n2)) by omega;
  ins; repeat (f_equal; try omega).
Qed.

Lemma seq_split0 : 
  forall l a,
  a < l ->
  seq 0 l = seq 0 a ++ a :: seq (S a) (l - a - 1).
Proof.
  ins; rewrite seq_split_gen with (a := a); repeat f_equal; omega.
Qed.

Lemma list_prod_app A (l l' : list A) B (m : list B) : 
  list_prod (l ++ l') m = list_prod l m ++ list_prod l' m.
Proof.
  by induction l; ins; rewrite IHl, app_assoc.
Qed.

Lemma list_prod_nil_r A (l : list A) B :
  list_prod l (@nil B) = nil.
Proof.
  induction l; ins.
Qed.

Lemma list_prod_cons_r A (l : list A) B a (m : list B) : 
  Permutation (list_prod l (a :: m)) (map (fun x => (x,a)) l ++ list_prod l m).
Proof.
  induction l; ins.
  eapply Permutation_cons; ins.
  eapply Permutation_trans; [by apply Permutation_app; eauto|].
  rewrite !app_assoc; eauto using Permutation_app, Permutation_app_comm. 
Qed.

Lemma list_prod_app_r A (l : list A) B (m m' : list B) : 
  Permutation (list_prod l (m ++ m')) (list_prod l m ++ list_prod l m').
Proof.
  induction m; ins; ins.
    by rewrite list_prod_nil_r.
  rewrite list_prod_cons_r. 
  eapply Permutation_trans; [by eapply Permutation_app, IHm|].
  rewrite app_assoc; apply Permutation_app; ins. 
  symmetry; apply list_prod_cons_r.
Qed.

Lemma in_seq_iff a n l : In a (seq n l) <-> n <= a < n + l.
Proof.
  induction[n] l; ins; rewrite ?IHl; omega.
Qed.

Lemma in_seq0_iff x a : In x (seq 0 a) <-> x < a.
Proof.
  rewrite in_seq_iff; omega.
Qed.


Lemma nodup_seq n l : NoDup (seq n l).
Proof.
  induction[n] l; ins; constructor; ins; eauto.
  rewrite in_seq_iff; omega.
Qed.

Lemma seq_split : 
  forall l a,
  a < l ->
  exists l', Permutation (seq 0 l) (a :: l') /\ ~ In a l'.
Proof.
  ins; eapply In_NoDup_Permutation; eauto using nodup_seq; apply in_seq_iff; omega.
Qed.

Lemma Permutation_listprod_r A (l : list A) B (m m' : list B) : 
  Permutation m m' -> 
  Permutation (list_prod l m) (list_prod l m').
Proof.
  ins; revert l; induction H; ins; eauto using Permutation.
    by rewrite ?list_prod_cons_r; eauto using Permutation_app.
  rewrite list_prod_cons_r.
  eapply Permutation_trans; [by apply Permutation_app, list_prod_cons_r|].
  symmetry.
  rewrite list_prod_cons_r.
  eapply Permutation_trans; [by apply Permutation_app, list_prod_cons_r|].
  rewrite !app_assoc; eauto using Permutation_app, Permutation_app_comm. 
Qed.


Ltac in_simp :=
  try match goal with |- ~ _ => intro end;
  repeat first [
    rewrite in_flatten_iff in *; desc; clarify |
    rewrite in_map_iff in *; desc; clarify |
    rewrite in_seq0_iff in *; desc; clarify ].

Global Opaque seq.
