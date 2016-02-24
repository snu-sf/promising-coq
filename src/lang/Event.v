Require Import List.
Require Import PeanoNat.
Require Import Orders.
Require Import MSetList.
Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import BoolOrderedType.

Set Implicit Arguments.
Import ListNotations.


Module Loc := Ident.
Module LocSet := IdentSet.
Module LocMap := IdentMap.
Module LocFun := IdentFun.


Module Const <: OrderedTypeWithLeibniz.
  Include Nat.

  Lemma eq_leibniz (x y: t): eq x y -> x = y.
  Proof. auto. Qed.
  
  Ltac ltb_tac :=
    match goal with
    | [H: compare ?x1 ?x2 = _ |- _] =>
      generalize (compare_spec x1 x2); rewrite H; clear H;
      intro H; inversion H; subst; clear H
    | [H: lt ?x ?x |- _] =>
      destruct lt_strorder; congruence
    | [H: lt ?x ?y |- _] =>
      rewrite H in *; clear H
    | [H: eq ?x ?y |- _] =>
      rewrite H in *; clear H
    end.
End Const.


Module Ordering <: OrderedTypeWithLeibniz.
  Module Raw <: BoolOrderedType.S.
    Inductive t_ :=
    | relaxed
    | acquire
    | release
    | relacq
    .
    Definition t := t_.

    Definition eq_dec (x y:t): {x = y} + {x <> y}.
    Proof. decide equality. Qed.

    Definition ltb (lhs rhs:t): bool :=
      match lhs, rhs with
      | relaxed, relaxed => false
      | relaxed, _ => true
      | acquire, relaxed => false
      | acquire, acquire => false
      | acquire, _ => true
      | release, relaxed => false
      | release, acquire => false
      | release, release => false
      | release, _ => true
      | relacq, _ => false
      end.

    Lemma ltb_trans (x y z:t) (XY: ltb x y) (YZ: ltb y z): ltb x z.
    Proof. repeat intro. destruct x, y, z; auto. Qed.

    Lemma ltb_irrefl x: ~ ltb x x.
    Proof. repeat intro. destruct x; auto. Qed.

    Lemma ltb_eq (lhs rhs:t) (LR: ~ ltb lhs rhs) (RL: ~ ltb rhs lhs): lhs = rhs.
    Proof. repeat intro. destruct lhs, rhs; simpl in *; congruence. Qed.
  End Raw.

  Include Raw <+ BoolOrderedType.Make (Raw).

  Definition ord (lhs rhs:t): bool :=
    match lhs, rhs with
    | acquire, relaxed => false
    | acquire, release => false
    | release, relaxed => false
    | release, acquire => false
    | _, _ => true
    end.
End Ordering.


Module RWEvent <: OrderedTypeWithLeibniz.
  Module Raw <: BoolOrderedType.S.
    Inductive t_ :=
    | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
    | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
    | update (loc:Loc.t) (rval wval:Const.t) (ord:Ordering.t)
    .
    Definition t := t_.

    Definition eq_dec (x y:t): {x = y} + {x <> y}.
    Proof.
      decide equality;
        (try apply Loc.eq_dec);
        (try apply Const.eq_dec);
        (try apply Ordering.eq_dec).
    Qed.

    Definition ltb (lhs rhs:t): bool :=
      match lhs, rhs with
      | read l1 v1 o1, read l2 v2 o2 =>
        compose_comparisons [Loc.compare l1 l2; Const.compare v1 v2; Ordering.compare o1 o2]
      | write l1 v1 o1, write l2 v2 o2 =>
        compose_comparisons [Loc.compare l1 l2; Const.compare v1 v2; Ordering.compare o1 o2]
      | update l1 r1 w1 o1, update l2 r2 w2 o2 =>
        compose_comparisons [Loc.compare l1 l2; Const.compare r1 r2; Const.compare w1 w2; Ordering.compare o1 o2]
      | read _ _ _, _ => true
      | write _ _ _, read _ _ _ => false
      | write _ _ _, _ => true
      | update _ _ _ _, _ => false
      end.

    Lemma ltb_trans (x y z:t) (XY: ltb x y) (YZ: ltb y z): ltb x z.
    Proof.
      destruct x, y, z; simpl in *; auto;
        repeat
          (try congruence;
           try omega;
           try Loc.ltb_tac;
           try Const.ltb_tac;
           try Ordering.ltb_tac;
           try ltb_des).
    Qed.

    Lemma ltb_irrefl x: ~ ltb x x.
    Proof.
      destruct x; simpl in *; auto;
        repeat
          (try congruence;
           try omega;
           try Loc.ltb_tac;
           try Const.ltb_tac;
           try Ordering.ltb_tac;
           try ltb_des).
    Qed.

    Lemma ltb_eq (lhs rhs:t) (LR: ~ ltb lhs rhs) (RL: ~ ltb rhs lhs): lhs = rhs.
    Proof.
      destruct lhs, rhs; simpl in *; auto;
        repeat
          (try congruence;
           try omega;
           try Loc.ltb_tac;
           try Const.ltb_tac;
           try Ordering.ltb_tac;
           try ltb_des).
    Qed.
  End Raw.

  Include Raw <+ BoolOrderedType.Make (Raw).

  Definition is_writing (e:t): option (Loc.t * Const.t) :=
    match e with
    | read _ _ _ => None
    | write loc val _ => Some (loc, val)
    | update loc _ val _ => Some (loc, val)
    end.

  Definition get_ordering (e:t): Ordering.t :=
    match e with
    | read _ _ ord => ord
    | write _ _ ord => ord
    | update _ _ _ ord => ord
    end.
End RWEvent.


Module Event.
  Structure t_ := mk {
    lhs: Const.t;
    rhses: list Const.t;
  }.
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply list_eq_dec);
      (try apply Const.eq_dec).
  Qed.
End Event.


Module ThreadEvent.
  Inductive mem_t :=
  | rw (e:RWEvent.t)
  | fence (ord:Ordering.t)
  .

  Inductive t :=
  | mem (e:mem_t)
  | syscall (e:Event.t)
  .
End ThreadEvent.
