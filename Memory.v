Require Import Equalities.
Require Import MSetWeakList.
Require Import PeanoNat.

Require Import Basic.
Require Import Event.
Require Import Program.

Set Implicit Arguments.

Module LocalClock.
  Definition t := Loc.Fun.t nat.

  Definition empty := Loc.Fun.empty 0.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Loc.Fun.find loc lhs <= Loc.Fun.find loc rhs.
End LocalClock.

Module Clock.
  Definition t := Ident.Fun.t LocalClock.t.

  Definition empty := Ident.Fun.empty LocalClock.empty.

  Definition le (lhs rhs:t): Prop :=
    forall i, LocalClock.le (Ident.Fun.find i lhs) (Ident.Fun.find i rhs).
End Clock.

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
  | h (n:nat)
  | i
  .

  Inductive In (msg:Message.t) (b:t): forall (p:position), Prop :=
  | In_history
      n
      (HISTORY: List.nth_error b.(history) n = Some msg):
      In msg b (h n)
  | In_inception
      (INCEPTION: MessageSet.In msg b.(inception)):
      In msg b i
  .

  Definition add_inception (msg:Message.t) (b:t): t :=
    mk b.(history) (MessageSet.add msg b.(inception)).
End Buffer.

Module Memory.
  Definition t := Ident.Fun.t Buffer.t.

  Definition empty := Ident.Fun.empty Buffer.empty.

  Definition position := (Ident.t * Buffer.position)%type.

  Inductive In (msg:Message.t) (m:t): forall (p:position), Prop :=
  | In_intro
      i p
      (IN: Buffer.In msg (Ident.Fun.find i m) p):
      In msg m (i, p)
  .

  (* TODO *)
  Inductive step (c:Clock.t): forall (s1:t) (i:Ident.t) (e:option Event.t) (s2:t), Prop :=
  .
End Memory.

Module State.
  Structure t := mk {
    clock: Clock.t;
    program: Program.t;
    memory: Memory.t;
    stack: list (Program.t * Memory.t);
  }.

  Inductive step: forall (s1 s2:t), Prop :=
  | step_event
      i e
      c p1 p2 m1 m2 stack
      (PROGRAM: Program.step p1 i e p2)
      (MEMORY: Memory.step c m1 i e m2):
      step (mk c p1 m1 stack) (mk c p2 m2 stack)
  | step_dream
      c p m stack:
      step (mk c p m stack) (mk c p m ((p, m)::stack))
  | step_inception
      c p m p' m' stack
      event ts ts' position i
      (MESSAGE: Memory.In (Message.mk event ts) m position)
      (POSITION: position.(snd) <> Buffer.i)
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
      (CLOCK: Clock.le c c'):
      step
        (mk c p m nil)
        (mk c' p m nil)
  .
End State.
