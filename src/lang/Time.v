Require Import Orders.

Require Import sflib.

Require Import DataStructure.
Require Import DenseOrder.

Module Time := DenseOrder.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Inductive time_mem (x:Time.t) (interval:t): Prop :=
  | time_mem_intro
      (FROM: Time.lt interval.(fst) x)
      (TO: ~ Time.lt interval.(snd) x)
  .
End Interval.


Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module IntervalSet.
  Include UsualSet Interval.

  Inductive time_mem (x:Time.t) (intervals:t): Prop :=
  | time_mem_intro
      itv
      (ITV: Interval.time_mem x itv)
      (ITVS: mem itv intervals)
  .

  Definition time_disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: time_mem x lhs)
      (RHS: time_mem x rhs),
      False.
End IntervalSet.
