Require String.
Require Import PArith.
Require Import FMapPositive.
Require Import MSetPositive.

Module Ident.
  Definition t := Pos.t.
  Definition eq_dec := Pos.eq_dec.

  Module Map := PositiveMap.
  Module Set_ := PositiveSet.

  Parameter of_string: String.string -> t.
  Hypothesis of_string_inject:
    forall s1 s2 (H12: s1 <> s2), of_string s1 <> of_string s2.
End Ident.
