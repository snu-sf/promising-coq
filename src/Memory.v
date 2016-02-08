Require Import List.
Require Import Equalities.
Require Import MSetWeakList.
Require Import PeanoNat.

Require Import Basic.
Require Import Event.
Require Import Thread.

Set Implicit Arguments.

Module Clock.
  Definition t := Loc.Fun.t nat.

  Definition init := Loc.Fun.init 0.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Loc.Fun.find loc lhs <= Loc.Fun.find loc rhs.
End Clock.

Module Clocks.
  Definition t := Ident.Fun.t Clock.t.

  Definition init := Ident.Fun.init Clock.init.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Clock.le (Ident.Fun.find loc lhs) (Ident.Fun.find loc rhs).
End Clocks.

Module Message <: DecidableType.
  Structure t_ := mk {
    event: Event.t;
    timestamp: nat;
  }.
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply Event.eq_dec);
      (try apply Nat.eq_dec).
  Qed.
End Message.

Module MessageSet := MSetWeakList.Make (Message).

Module Buffer.
  Structure t := mk {
    history: list Message.t;
    inception: MessageSet.t;
  }.

  Definition empty := mk nil MessageSet.empty.

  Module Position.
    Inductive t :=
    | history (n:nat)
    | inception
    .

    Inductive lt: forall (lhs rhs:t), Prop :=
    | lt_hh n m (LT: n < m):
        lt (history n) (history m)
    | lt_hi n:
        lt (history n) inception
    .
  End Position.

  Inductive In (msg:Message.t) (b:t): forall (p:Position.t), Prop :=
  | In_history
      n
      (HISTORY: List.nth_error b.(history) n = Some msg):
      In msg b (Position.history n)
  | In_inception
      (INCEPTION: MessageSet.In msg b.(inception)):
      In msg b Position.inception
  .

  Definition add_history (msg:Message.t) (b:t): t :=
    mk (msg::b.(history)) b.(inception).

  Definition add_inception (msg:Message.t) (b:t): t :=
    mk b.(history) (MessageSet.add msg b.(inception)).

  Definition confirm (msg:Message.t) (b:t): option t :=
    if MessageSet.mem msg b.(inception)
    then Some (mk (msg::b.(history)) (MessageSet.remove msg b.(inception)))
    else None.

  Definition timestamp_history (loc:Loc.t) (b:t): nat :=
    List.fold_left
      (fun res msg =>
         if option_eq_dec
              Loc.eq_dec
              (option_map fst (Event.is_writing msg.(Message.event)))
              (Some loc)
         then max msg.(Message.timestamp) res
         else res)
      b.(history)
      0.

  Definition timestamp_inception (loc:Loc.t) (b:t): nat :=
    MessageSet.fold
      (fun msg res =>
         if option_eq_dec
              Loc.eq_dec
              (option_map fst (Event.is_writing msg.(Message.event)))
              (Some loc)
         then max msg.(Message.timestamp) res
         else res)
      b.(inception)
      0.

  Definition timestamp (loc:Loc.t) (b:t): nat :=
    max (timestamp_history loc b) (timestamp_inception loc b).
End Buffer.

Module Memory.
  Definition t := Ident.Fun.t Buffer.t.

  Definition init := Ident.Fun.init Buffer.empty.

  Definition position := (Ident.t * Buffer.Position.t)%type.

  Inductive In (msg:Message.t) (m:t): forall (p:position), Prop :=
  | In_intro
      i p
      (IN: Buffer.In msg (Ident.Fun.find i m) p):
      In msg m (i, p)
  .

  Definition timestamp (loc:Loc.t) (m:t): nat :=
    Ident.Fun.get_max
      (Buffer.timestamp loc)
      m.

  Inductive step (c:Clocks.t): forall (m1:t) (i:Ident.t) (e:option Event.t) (m2:t), Prop :=
  | step_read
      m read_event ts position
      i loc val ord
      (MESSAGE: Memory.In (Message.mk read_event ts) m position)
      (READ: Event.is_writing read_event = Some (loc, val))
      (POSITION: position <> (i, Buffer.Position.inception))
      (TS1: Loc.Fun.find loc (Ident.Fun.find i c) <= ts)
      (TS2: Buffer.timestamp_history loc (Ident.Fun.find i m) <= ts):
      step
        c
        m
        i
        (Some (Event.read loc val ord))
        (Ident.Fun.add
           i
           (Buffer.add_history (Message.mk (Event.read loc val ord) ts) (Ident.Fun.find i m))
           m)
  | step_write
      m
      i loc val ord:
      step
        c
        m
        i
        (Some (Event.write loc val ord))
        (Ident.Fun.add
           i
           (Buffer.add_history
              (Message.mk
                 (Event.write loc val ord)
                 ((timestamp loc m) + 1))
              (Ident.Fun.find i m))
           m)
  | step_update
      m read_event position
      i loc valr valw ord
      (MESSAGE: Memory.In (Message.mk read_event (timestamp loc m)) m position)
      (READ: Event.is_writing read_event = Some (loc, valr))
      (POSITION: position <> (i, Buffer.Position.inception))
      (TS: Loc.Fun.find loc (Ident.Fun.find i c) <= (timestamp loc m)):
      step
        c
        m
        i
        (Some (Event.update loc valr valw ord))
        (Ident.Fun.add
           i
           (Buffer.add_history
              (Message.mk
                 (Event.update loc valr valw ord)
                 ((timestamp loc m) + 1))
              (Ident.Fun.find i m))
           m)
  | step_confirm
      m event ts i b'
      (MESSAGE: Buffer.confirm (Message.mk event ts) (Ident.Fun.find i m) = Some b'):
      step c m i (Some event) (Ident.Fun.add i b' m)
  .
End Memory.
