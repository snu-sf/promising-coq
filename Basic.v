Require String.
Require Import PArith.
Require Import FMapPositive.
Require Import MSetPositive.

Set Implicit Arguments.

Module PositiveFun.
  Section PositiveFun.
    Variable (V:Type).

    Structure t := mk {
      map: PositiveMap.t V;
      default: V;
    }.

    Definition empty (v:V) := mk (PositiveMap.empty _) v.

    Definition find (p:positive) (f:t): V :=
      match PositiveMap.find p f.(map) with
      | Some v => v
      | None => f.(default)
      end.

    Definition add (p:positive) (v:V) (f:t): t :=
      mk
        (PositiveMap.add p v f.(map))
        f.(default).

    Lemma empty_spec p v:
      find p (empty v) = v.
    Proof.
      unfold find, empty. simpl.
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
