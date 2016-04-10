Require Import Bool OrderedType ZArith OrderedType OrderedTypeEx FMapInterface FMapPositive FMapFacts ProofIrrelevance EqdepFacts.

Require Import sflib.

Set Implicit Arguments.
Local Open Scope positive_scope.
Local Unset Elimination Schemes.

Module UsualPositiveMap' <: S with Module E:=PositiveOrderedTypeBits.

  Module E:=PositiveOrderedTypeBits.
  Module ME:=KeyOrderedType E.

  Definition key := positive : Type.

  Module Raw := PositiveMap.

  Inductive inhabited A: forall (m : Raw.t A), Prop :=
  | inhabited_Some
      l o r
      (L: wf l)
      (R: wf r):
      inhabited (Raw.Node l (Some o) r)
  | inhabited_l
      l r
      (L: inhabited l)
      (R: wf r):
      inhabited (Raw.Node l None r)
  | inhabited_r
      l r
      (L: wf l)
      (R: inhabited r):
      inhabited (Raw.Node l None r)

  with wf A: forall (m : Raw.t A), Prop :=
  | wf_Leaf:
      wf (Raw.Leaf _)
  | wf_inhabited
      m (INHABITED: inhabited m):
      wf m
  .

  Lemma wf_l A l o r (WF: @wf A (Raw.Node l o r)):
    wf l.
  Proof.
    inversion WF. subst. clear WF.
    inversion INHABITED; subst; auto.
    constructor. auto.
  Qed.

  Lemma wf_r A l o r (WF: @wf A (Raw.Node l o r)):
    wf r.
  Proof.
    inversion WF. subst. clear WF.
    inversion INHABITED; subst; auto.
    constructor. auto.
  Qed.

  Lemma inhabited_inv A m (INH: @inhabited A m):
    exists i a, Raw.find i m = Some a.
  Proof.
    revert INH.
    induction m; intros;
      inversion INH; subst; clear INH.
    - exists xH, o0. auto.
    - destruct (IHm1 L) as [i' [a' IH]].
      exists (xO i'), a'. auto.
    - destruct (IHm2 R) as [i' [a' IH]].
      exists (xI i'), a'. auto.
  Qed.

  Definition t A := {tr:Raw.t A | wf tr}.

  Section A.
  Variable A:Type.

  Ltac tac :=
    repeat
      (try match goal with
           | [|- wf (Raw.Leaf _)] => constructor
           | [|- wf (Raw.Node _ _ _)] => constructor
           | [|- inhabited (Raw.Node _ (Some _) _)] => constructor 1
           | [|- inhabited (Raw.Node ?x None (Raw.Leaf _))] => constructor 2
           | [|- inhabited (Raw.Node (Raw.Leaf _) None ?x)] => constructor 3
           | [H: inhabited ?x |- inhabited (Raw.Node ?x None _)] => constructor 2
           | [H: inhabited ?x |- inhabited (Raw.Node _ None ?x)] => constructor 3

           | [x: t A |- _] =>
             let m := fresh "m" in
             let WF := fresh "WF" in
             destruct x as [m WF]; clear x
           | [WF: wf (Raw.Node _ _ _) |- _] =>
             inversion WF; clear WF
           | [INHABITED: inhabited (Raw.Node _ _ _) |- _] =>
             inversion INHABITED; clear INHABITED
           | [INHABITED: inhabited ?m |- wf ?m] =>
             constructor; auto
           | [H: inhabited (Raw.Leaf _) |- _] => inversion H
           | [H: (Raw.Leaf _) <> ?x |- _] =>
             destruct x; [congruence|clear H]
           | [H: ?x <> (Raw.Leaf _) |- _] =>
             destruct x; [congruence|clear H]
           end;
       ss; subst; auto).

  Program Definition empty : t A := Raw.empty A.
  Next Obligation. constructor. Qed.

  Definition is_empty (m : t A) : bool := Raw.is_empty (proj1_sig m).

  Definition find (i : key) (m : t A) := Raw.find i (proj1_sig m).

  Definition mem (i : key) (m : t A) := Raw.mem i (proj1_sig m).

  Lemma add_proper i v (m:Raw.t A) (WF: wf m):
    inhabited (Raw.add i v m).
  Proof.
    revert v m WF.
    induction i; destruct m; intros; tac;
      try (constructor; tac; fail).
    - constructor 3; tac. apply IHi. tac.
    - constructor 2; tac. apply IHi. tac.
  Qed.
  Definition add (i : key) (v : A) (m : t A) : t A :=
    exist
      _
      (Raw.add i v (proj1_sig m))
      (wf_inhabited (add_proper i v (proj2_sig m))).

  Lemma remove_proper i (m:Raw.t A) (WF: wf m):
    wf (Raw.remove i m).
  Proof.
    revert m WF.
    induction i; destruct m; intros; tac.
    - destruct m1; tac.
    - destruct m1; tac.
    - destruct m1; tac; try (apply IHi; tac; fail).
      specialize (IHi m2 (wf_inhabited R)).
      destruct (Raw.remove i m2); tac.
    - destruct m2; tac; try (apply IHi; tac; fail).
      specialize (IHi m1 (wf_inhabited L)).
      destruct (Raw.remove i m1); tac.
    - destruct m2; tac.
    - destruct m1, m2; tac.
    - destruct m1, m2; tac.
    - destruct m1, m2; tac.
  Qed.
  Definition remove (i : key) (m : t A) : t A :=
    exist
      _
      (Raw.remove i (proj1_sig m))
      (remove_proper i (proj2_sig m)).

  (** [elements] *)

  Definition elements (m : t A) := Raw.elements (proj1_sig m).

  (** [cardinal] *)

  Definition cardinal (m : t A) := Raw.cardinal (proj1_sig m).

  Section CompcertSpec.

  Theorem gempty:
    forall (i: key), find i empty = None.
  Proof.
    apply Raw.gempty.
  Qed.

  Theorem gss:
    forall (i: key) (x: A) (m: t A), find i (add i x m) = Some x.
  Proof.
    intros. apply Raw.gss.
  Qed.

  Theorem gso:
    forall (i j: key) (x: A) (m: t A),
    i <> j -> find i (add j x m) = find i m.
  Proof.
    intros. apply Raw.gso. tac.
  Qed.

  Theorem grs:
    forall (i: key) (m: t A), find i (remove i m) = None.
  Proof.
    intros. apply Raw.grs.
  Qed.

  Theorem gro:
    forall (i j: key) (m: t A),
    i <> j -> find i (remove j m) = find i m.
  Proof.
    intros. apply Raw.gro. tac.
  Qed.

  Theorem elements_correct:
    forall (m: t A) (i: key) (v: A),
    find i m = Some v -> List.In (i, v) (elements m).
  Proof.
    intros. apply Raw.elements_correct. tac.
  Qed.

  Theorem elements_complete:
    forall (m: t A) (i: key) (v: A),
    List.In (i, v) (elements m) -> find i m = Some v.
  Proof.
    intros. apply Raw.elements_complete. tac.
  Qed.

  Lemma cardinal_1 :
   forall (m: t A), cardinal m = length (elements m).
  Proof.
    intros. apply Raw.cardinal_1.
  Qed.

  End CompcertSpec.

  Definition MapsTo (i:key)(v:A)(m:t A) := find i m = Some v.

  Definition In (i:key)(m:t A) := exists e:A, MapsTo i e m.

  Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').

  Definition eq_key_elt (p p':key*A) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

  Global Instance eqk_equiv : Equivalence eq_key := _.
  Global Instance eqke_equiv : Equivalence eq_key_elt := _.
  Global Instance ltk_strorder : StrictOrder lt_key := _.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
    intros. apply Raw.mem_find.
  Qed.

  Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
  Proof.
    intros. apply Raw.Empty_alt.
  Qed.

  Section FMapSpec.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  destruct (find x m).
  exists a; auto.
  intros; discriminate.
  Qed.

  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  rewrite Empty_alt; apply gempty.
  Qed.

  Lemma is_empty_1 : Empty m -> is_empty m = true.
  Proof.
    intros. apply Raw.is_empty_1. auto.
  Qed.

  Lemma is_empty_2 : is_empty m = true -> Empty m.
  Proof.
    intros. apply Raw.is_empty_2. auto.
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
    intros. apply Raw.add_1. auto.
  Qed.

  Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros. apply Raw.add_2; auto.
  Qed.

  Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    unfold add. intros. eapply Raw.add_3; eauto.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof.
    unfold remove. intros. eapply Raw.remove_1; eauto.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    unfold remove. intros. eapply Raw.remove_2; eauto.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    unfold remove. intros. eapply Raw.remove_3; eauto.
  Qed.

  Lemma elements_1 :
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
    unfold elements. intros. eapply Raw.elements_1; eauto.
  Qed.

  Lemma elements_2 :
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
    unfold elements. intros. eapply Raw.elements_2; eauto.
  Qed.

  Lemma elements_3 : sort lt_key (elements m).
  Proof.
    unfold elements. intros. eapply Raw.elements_3; eauto.
  Qed.

  Lemma elements_3w : NoDupA eq_key (elements m).
  Proof.
    unfold elements. intros. eapply Raw.elements_3w; eauto.
  Qed.

  End FMapSpec.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> A -> B.

    Lemma xmapi_proper (m:Raw.t A) i:
      (wf m -> wf (Raw.xmapi f m i)) /\
      (inhabited m -> inhabited (Raw.xmapi f m i)).
    Proof.
      revert i.
      induction m; constructor; intros; tac;
        try (apply IHm1; tac; fail);
        try (apply IHm2; tac; fail).
      - constructor 2; try apply IHm1; try apply IHm2; tac.
      - constructor 3; try apply IHm1; try apply IHm2; tac.
      - constructor 2; try apply IHm1; try apply IHm2; tac.
      - constructor 3; try apply IHm1; try apply IHm2; tac.
    Qed.
    Program Definition xmapi (m : t A) (i : key) : t B :=
      exist
        _
        (Raw.xmapi f (proj1_sig m) i)
        (proj1 (xmapi_proper (proj1_sig m) i) (proj2_sig m)).

    Definition mapi m := xmapi m xH.

  End Mapi.

  Definition map (f : A -> B) m := mapi (fun _ => f) m.

  End A.

  Lemma xgmapi:
      forall (A B: Type) (f: key -> A -> B) (i j : key) (m: t A),
      find i (xmapi f m j) = option_map (f (append j i)) (find i m).
  Proof.
    unfold find, xmapi. s. intros. apply Raw.xgmapi.
  Qed.

  Theorem gmapi:
    forall (A B: Type) (f: key -> A -> B) (i: key) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof.
  intros.
  unfold mapi.
  replace (f i) with (f (append xH i)).
  apply xgmapi.
  rewrite append_neutral_l; auto.
  Qed.

  Lemma mapi_1 :
    forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
    MapsTo x e m ->
    exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
  intros.
  exists x.
  split; [red; auto|].
  apply find_2.
  generalize (find_1 H); clear H; intros.
  rewrite gmapi.
  rewrite H.
  s; auto.
  Qed.

  Lemma mapi_2 :
    forall (elt elt':Type)(m: t elt)(x:key)(f:key->elt->elt'),
    In x (mapi f m) -> In x m.
  Proof.
  intros.
  apply mem_2.
  rewrite mem_find.
  destruct H as (v,H).
  generalize (find_1 H); clear H; intros.
  rewrite gmapi in H.
  destruct (find x m); auto.
  ss; discriminate.
  Qed.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
  intros; unfold map.
  destruct (mapi_1 (fun _ => f) H); intuition.
  Qed.

  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
    In x (map f m) -> In x m.
  Proof.
  intros; unfold map in *; eapply mapi_2; eauto.
  Qed.

  Fixpoint normalize A (m:Raw.t A): Raw.t A :=
    match m with
    | Raw.Leaf _ => Raw.Leaf _
    | Raw.Node l o r =>
      match normalize l, o, normalize r with
      | Raw.Leaf _, None, Raw.Leaf _ => Raw.Leaf _
      | l, _, r => Raw.Node l o r
      end
    end.

  Lemma normalize_wf A (m:Raw.t A):
    wf (normalize m).
  Proof.
    induction m; s.
    { constructor. }
    destruct (normalize m1), o, (normalize m2);
      try (repeat (constructor; auto); fail).
    - constructor. constructor 3; auto.
      inversion IHm2. auto.
    - constructor. constructor 2; auto.
      inversion IHm1. auto.
    - constructor. constructor 2; auto.
      inversion IHm1. auto.
  Qed.

  Lemma normalize_correct A (m:Raw.t A) i:
    Raw.find i (normalize m) = Raw.find i m.
  Proof.
    revert m.
    induction i; destruct m; intros; s; auto;
      destruct
        (normalize m1) eqn:M1,
        o,
        (normalize m2) eqn:M2;
      try (rewrite <- M1, IHi; auto; fail);
      try (rewrite <- M2, IHi; auto; fail);
      auto.
    - rewrite <- IHi, M2. rewrite Raw.gleaf. auto.
    - rewrite <- IHi, M1. rewrite Raw.gleaf. auto.
  Qed.

  Definition map2 (elt elt' elt'':Type)(f:option elt->option elt'->option elt'')
             (m:t elt) (m':t elt'): t elt'' :=
    exist
      _
      (normalize (Raw.map2 f (proj1_sig m) (proj1_sig m')))
      (normalize_wf _).

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m').
  Proof.
    unfold find, map2. s. intros.
    rewrite normalize_correct.
    apply Raw.map2_1. auto.
  Qed.

  Lemma  map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
    unfold map2. intros.
    apply mem_1 in H. unfold mem in *. ss.
    rewrite Raw.mem_find, normalize_correct, <- Raw.mem_find in *.
    apply Raw.mem_2 in H.
    eapply Raw.map2_2; eauto.
  Qed.


  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    Definition fold (m:t A) i := Raw.fold f (proj1_sig m) i.

  End Fold.

  Lemma fold_1 :
    forall (A:Type)(m:t A)(B:Type)(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    unfold fold, elements. intros.
    apply Raw.fold_1.
  Qed.

  Definition equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    Raw.equal cmp (proj1_sig m1) (proj1_sig m2).

  Definition Equal (A:Type)(m m':t A) :=
    forall y, find y m = find y m'.
  Definition Equiv (A:Type)(eq_elt:A->A->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    intros. apply Raw.equal_1. auto.
  Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    intros. apply Raw.equal_2. auto.
  Qed.

  Lemma eq_leibniz
        A (m m':t A)
        (EQUAL: Equal m m'):
    m = m'.
  Proof.
    destruct m as [m WF], m' as [m' WF'].
    revert WF m' WF' EQUAL.
    induction m; destruct m'; intros;
      apply subset_eq_compat; auto.
    - inversion WF'. subst.
      apply inhabited_inv in INHABITED.
      destruct INHABITED as [i [a INHABITED]].
      specialize (EQUAL i). unfold find in *. ss.
      rewrite Raw.gleaf, INHABITED in EQUAL. congruence.
    - inversion WF. subst.
      apply inhabited_inv in INHABITED.
      destruct INHABITED as [i [a INHABITED]].
      specialize (EQUAL i). unfold find in *. ss.
      rewrite Raw.gleaf, INHABITED in EQUAL. congruence.
    - f_equal.
      + eapply eq_sig_fst. apply IHm1.
        intro i. specialize (EQUAL (xO i)). auto.
      + specialize (EQUAL xH). auto.
      + eapply eq_sig_fst. apply IHm2.
        intro i. specialize (EQUAL (xI i)). auto.
  Grab Existential Variables.
  { s. eapply wf_r. eauto. }
  { s. eapply wf_r. eauto. }
  { s. eapply wf_l. eauto. }
  { s. eapply wf_l. eauto. }
  Qed.
End UsualPositiveMap'.

(** Here come some additional facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)

Module UsualPositiveMap <: S with Module E:=PositiveOrderedTypeBits.
  Include UsualPositiveMap'.

  Module Facts := FMapFacts.Facts (UsualPositiveMap').
  Module Properties := FMapFacts.Properties (UsualPositiveMap').

  Lemma map_add A B (f:A -> B) i v m:
    map f (add i v m) = add i (f v) (map f m).
  Proof.
    apply eq_leibniz. intro.
    rewrite ? Facts.map_o, ? Properties.F.add_o.
    destruct (Properties.F.eq_dec i y); auto.
    rewrite Facts.map_o. auto.
  Qed.

  (* Derivable from the Map interface *)
  Theorem gsspec:
    forall (A:Type)(i j: key) (x: A) (m: t A),
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    intros.
    destruct (E.eq_dec i j) as [ ->|]; [ apply gss | apply gso; auto ].
  Qed.

   (* Not derivable from the Map interface *)
  Theorem gsident:
    forall (A:Type)(i: key) (m: t A) (v: A),
    find i m = Some v -> add i v m = m.
  Proof.
    intros. destruct m as [m WF].
    apply subset_eq_compat.
    apply PositiveMapAdditionalFacts.gsident.
    auto.
  Qed.

  Lemma add_add V k1 k2 (v1 v2:V) m
        (KEY: k1 <> k2):
    add k1 v1 (add k2 v2 m) = add k2 v2 (add k1 v1 m).
  Proof.
    apply eq_leibniz. ii.
    rewrite ? Facts.add_o.
    destruct (E.eq_dec k1 y), (E.eq_dec k2 y); auto.
    congruence.
  Qed.
End UsualPositiveMap.
