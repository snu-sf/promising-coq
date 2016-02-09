Require String.
Require Import List.
Require Import PArith.
Require Import Omega.
Require Import MSetPositive.
Require Import FMapPositive.
Require Import FMapFacts.
Require Import Relations.

Set Implicit Arguments.

Module PositiveMapFacts := FMapFacts.Facts (PositiveMap).
Module PositiveMapProperties := FMapFacts.Properties (PositiveMap).

Module PositiveFun.
  Section PositiveFun.
    Variable (V:Type).

    Structure t := mk {
      map: PositiveMap.t V;
      default: V;
    }.

    Definition init (v:V) := mk (PositiveMap.empty _) v.

    Definition find (p:positive) (f:t): V :=
      match PositiveMap.find p f.(map) with
      | Some v => v
      | None => f.(default)
      end.

    Definition add (p:positive) (v:V) (f:t): t :=
      mk
        (PositiveMap.add p v f.(map))
        f.(default).

    Definition get_max (pred: V -> nat) (f:t): nat :=
      PositiveMap.fold
        (fun _ v res => max (pred v) res)
        f.(map)
        (pred f.(default)).

    Lemma init_spec p v:
      find p (init v) = v.
    Proof.
      unfold find, init. simpl.
      rewrite PositiveMap.gempty. auto.
    Qed.

    Lemma add_spec p' p v f:
      find p' (add p v f) =
      if Pos.eq_dec p' p
      then v
      else find p' f.
    Proof.
      unfold find, add. simpl.
      rewrite PositiveMapAdditionalFacts.gsspec.
      destruct (PositiveMap.E.eq_dec p' p), (Pos.eq_dec p' p); congruence.
    Qed.

    Lemma get_max_spec pred f:
      forall i, pred (find i f) <= get_max pred f.
    Proof.
      unfold find, get_max.
      rewrite PositiveMap.fold_1, <- fold_left_rev_right.
      intros. destruct (PositiveMap.find i (map f)) eqn:FIND.
      - apply PositiveMap.elements_correct in FIND.
        apply in_rev in FIND.
        revert FIND. generalize (rev (PositiveMap.elements (map f))).
        induction l; intros; inversion FIND; subst; simpl.
        + apply Max.le_max_l.
        + rewrite <- Max.le_max_r. apply IHl. auto.
      - induction (rev (PositiveMap.elements (map f))); auto.
        simpl. rewrite <- Max.le_max_r. apply IHl.
    Qed.
  End PositiveFun.
End PositiveFun.

Module Ident.
  Definition t := Pos.t.
  Definition eq_dec := Pos.eq_dec.

  Module Map := PositiveMap.
  Module Set_ := PositiveSet.
  Module Fun := PositiveFun.

  Parameter of_string: String.string -> t.
  Hypothesis of_string_inject:
    forall s1 s2 (H12: s1 <> s2), of_string s1 <> of_string s2.
End Ident.

Definition option_eq_dec
           A (eq_dec: forall (l r:A), {l = r} + {l <> r})
           (l r: option A): {l = r} + {l <> r}.
Proof.
  refine
    (match l, r with
     | Some l, Some r => _
     | None, None => _
     | _, _ => _
     end);
    try (left; auto; fail);
    try (right; congruence; fail).
  destruct (eq_dec l r).
  - subst. left. auto.
  - right. contradict n. inversion n. auto.
Defined.

Notation rtc := (clos_refl_trans _). (* reflexive transitive closure *)
Notation rc := (clos_refl _). (* reflexive transitive closure *)
Notation tc := (clos_trans _). (* transitive closure *)
Hint Immediate rt_step rt_refl t_step.
