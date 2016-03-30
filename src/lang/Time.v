Require Import Orders.

Require Import sflib.

Require Import DataStructure.
Require Import DenseOrder.
Require Import Basic.
Require Import Event.

Module Time := DenseOrder.

Module TimeSet := UsualSet Time.
Module TimeFun := UsualFun Time.

Module Interval <: UsualOrderedType.
  Include UsualProd Time Time.

  Inductive time_mem (x:Time.t) (interval:t): Prop :=
  | time_mem_intro
      (FROM: Time.lt interval.(fst) x)
      (TO: ~ Time.lt interval.(snd) x)
  .

  Definition time_disjoint (lhs rhs:t): Prop :=
    forall x
      (LHS: time_mem x lhs)
      (RHS: time_mem x rhs),
    False.
End Interval.

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

Module IntervalSets.
  Definition t := LocFun.t IntervalSet.t.
  Definition bot: t := LocFun.init IntervalSet.empty.

  Definition mem (loc:Loc.t) (ts:Time.t) (itvs:t): Prop :=
    IntervalSet.time_mem ts (LocFun.find loc itvs).

  Definition remove (loc:Loc.t) (ts0 ts:Time.t) (itvs:t): option t :=
    if IntervalSet.mem (ts0, ts) (LocFun.find loc itvs)
    then Some (LocFun.add loc (IntervalSet.remove (ts0, ts) (LocFun.find loc itvs)) itvs)
    else None.

  Definition disjoint (loc:Loc.t) (ts0 ts:Time.t) (perm:t): Prop :=
    forall x (ITV: Interval.time_mem x (ts0, ts)),
      ~ mem loc x perm.

  Definition add (loc:Loc.t) (ts0 ts:Time.t) (perm:t): t :=
    LocFun.add loc (IntervalSet.add (ts0, ts) (LocFun.find loc perm)) perm.

  Definition le (lhs rhs:t): Prop :=
    forall loc ts (LHS: IntervalSet.time_mem ts (LocFun.find loc lhs)),
      IntervalSet.time_mem ts (LocFun.find loc rhs).
End IntervalSets.
