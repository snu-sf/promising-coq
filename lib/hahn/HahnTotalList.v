(******************************************************************************)
(** * Total order from a list of elements *)
(******************************************************************************)

Require Import HahnBase HahnList HahnRelationsBasic.

Set Implicit Arguments.

(** We define three constructions: 
- [total_order_from_list] constructs a total order from a list of elements. 
- [mk_tou] constructs a union of total orders from a list of element lists.
- [mk_po] constructs a program order for [init ; (l1 || .. || ln)].
*)

Definition total_order_from_list A (l: list A) x y :=
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3.

Definition mk_tou A (ll: list (list A)) x y :=
  exists l, In l ll /\ total_order_from_list l x y.

Definition mk_po A init ll (x y: A) :=
  In x init /\ In y (concat ll) \/ mk_tou ll x y.

(******************************************************************************)
(** We now prove several properties of these definitions. 
We start with [total_order_from_list]. *)


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

(******************************************************************************)
(** Next, we prove some basic properties of [mk_tou]. *)
(******************************************************************************)

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


(******************************************************************************)
(** Finally, we prove some basic properties of [mk_po]. *)
(******************************************************************************)

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


(** Reordering of adjacent actions in a partial order. *)
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
