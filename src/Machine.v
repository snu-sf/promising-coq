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

  Inductive position :=
  | position_h (n:nat)
  | position_i
  .

  Inductive In (msg:Message.t) (b:t): forall (p:position), Prop :=
  | In_history
      n
      (HISTORY: List.nth_error b.(history) n = Some msg):
      In msg b (position_h n)
  | In_inception
      (INCEPTION: MessageSet.In msg b.(inception)):
      In msg b position_i
  .

  Definition add_history (msg:Message.t) (b:t): t :=
    mk (msg::b.(history)) b.(inception).

  Definition add_inception (msg:Message.t) (b:t): t :=
    mk b.(history) (MessageSet.add msg b.(inception)).

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

  Definition position := (Ident.t * Buffer.position)%type.

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
      (POSITION: position <> (i, Buffer.position_i))
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
      (POSITION: position <> (i, Buffer.position_i))
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
  .
End Memory.

Module Configuration.
  Structure t := mk {
    clocks: Clocks.t;
    threads: Threads.t;
    memory: Memory.t;
    stack: list (Threads.t * Memory.t);
  }.

  Inductive is_terminal (c:t): Prop :=
  | is_terminal_intro
      (STACK: c.(stack) = nil)
      (THREADS:
         forall i th (THREAD: Ident.Map.find i c.(threads) = Some th),
           Thread.is_terminal th)
  .

  Inductive step: forall (c1 c2:t), Prop :=
  | step_event
      i e
      c p1 p2 m1 m2 stack
      (THREADS: Threads.step p1 i e p2)
      (MEMORY: Memory.step c m1 i e m2):
      step (mk c p1 m1 stack) (mk c p2 m2 stack)
  | step_dream
      c p m stack:
      step (mk c p m stack) (mk c p m ((p, m)::stack))
  | step_inception
      c p m p' m' stack
      event ts ts' position i
      (MESSAGE: Memory.In (Message.mk event ts) m position)
      (POSITION: position.(snd) <> Buffer.position_i)
      (INCEPTION:
         forall i,
           MessageSet.Subset
             (Ident.Fun.find i m).(Buffer.inception)
             (Ident.Fun.find i m').(Buffer.inception)):
      step
        (mk c p m ((p', m')::stack))
        (mk c
            p'
            (Ident.Fun.add i (Buffer.add_inception (Message.mk event ts') (Ident.Fun.find i m')) m')
            stack)
  | step_commit
      c p m c'
      (MEMORY: forall i, MessageSet.Empty (Ident.Fun.find i m).(Buffer.inception))
      (CLOCKS: Clocks.le c c'):
      step
        (mk c p m nil)
        (mk c' p m nil)
  .
End Configuration.
