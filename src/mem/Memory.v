Require Import List.
Require Import Equalities.
Require Import MSetWeakList.
Require Import PeanoNat.
Require Import Relations.

Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Thread.

Import ListNotations.

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
  Inductive t_ :=
  | rw (event:RWEvent.t) (timestamp:nat)
  | fence (ord:Ordering.t)
  .
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply RWEvent.eq_dec);
      (try apply Nat.eq_dec);
      (try apply Ordering.eq_dec).
  Qed.

  Definition get_ordering (e:t): Ordering.t :=
    match e with
    | rw e _ => RWEvent.get_ordering e
    | fence ord => ord
    end.
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
    | inception (msg:Message.t)
    .

    Inductive lt: forall (lhs rhs:t), Prop :=
    | lt_hh n m (LT: n < m):
        lt (history n) (history m)
    | lt_hi n msg:
        lt (history n) (inception msg)
    .
  End Position.

  Inductive In (msg:Message.t) (b:t): forall (p:Position.t), Prop :=
  | In_history
      n
      (HISTORY: List.nth_error b.(history) n = Some msg):
      In msg b (Position.history n)
  | In_inception
      (INCEPTION: MessageSet.In msg b.(inception)):
      In msg b (Position.inception msg)
  .

  Definition add_history (msg:Message.t) (b:t): t :=
    mk (b.(history) ++ [msg]) b.(inception).

  Definition add_inception (msg:Message.t) (b:t): t :=
    mk b.(history) (MessageSet.add msg b.(inception)).

  Definition confirm (msg:Message.t) (b:t): option t :=
    if MessageSet.mem msg b.(inception)
    then Some (mk (b.(history) ++ [msg]) (MessageSet.remove msg b.(inception)))
    else None.

  Definition timestamp_history (loc:Loc.t) (b:t): nat :=
    List.fold_left
      (fun res msg =>
         match msg with
         | Message.rw event timestamp =>
           if option_eq_dec
                Loc.eq_dec
                (option_map fst (RWEvent.is_writing event))
                (Some loc)
           then max timestamp res
           else res
         | _ => res
         end)
      b.(history)
      0.

  Definition timestamp_inception (loc:Loc.t) (b:t): nat :=
    MessageSet.fold
      (fun msg res =>
         match msg with
         | Message.rw event timestamp =>
           if option_eq_dec
                Loc.eq_dec
                (option_map fst (RWEvent.is_writing event))
                (Some loc)
           then max timestamp res
           else res
         | _ => res
         end)
      b.(inception)
      0.

  Definition timestamp (loc:Loc.t) (b:t): nat :=
    max (timestamp_history loc b) (timestamp_inception loc b).
End Buffer.

Module Memory.
  Definition t := Ident.Fun.t Buffer.t.

  Definition init := Ident.Fun.init Buffer.empty.

  Module Position.
    Inductive t :=
    | init
    | buffer (i:Ident.t) (pos:Buffer.Position.t)
    .

    Definition is_inception (p:t): bool :=
      match p with
      | buffer _ pos =>
        match pos with
        | Buffer.Position.inception _ => true
        | _ => false
        end
      | _ => false
      end.
  End Position.

  Inductive In (m:t): forall (msg:Message.t) (p:Position.t), Prop :=
  | In_init
      loc:
      In m (Message.rw (RWEvent.write loc Const.zero Ordering.release) 0) Position.init
  | In_buffer
      msg i p
      (IN: Buffer.In msg (Ident.Fun.find i m) p):
      In m msg (Position.buffer i p)
  .

  Definition timestamp (loc:Loc.t) (m:t): nat :=
    Ident.Fun.get_max
      (Buffer.timestamp loc)
      m.

  Inductive step (c:Clocks.t): forall (m1:t) (i:Ident.t) (e:option ThreadEvent.t) (m2:t), Prop :=
  | step_read
      m read_event ts position
      i loc val ord
      (MESSAGE: In m (Message.rw read_event ts) position)
      (READ: RWEvent.is_writing read_event = Some (loc, val))
      (POSITION: position <> Position.buffer i (Buffer.Position.inception (Message.rw read_event ts)))
      (TS1: Loc.Fun.find loc (Ident.Fun.find i c) <= ts)
      (TS2: Buffer.timestamp_history loc (Ident.Fun.find i m) <= ts):
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.read loc val ord)))
        (Ident.Fun.add
           i
           (Buffer.add_history (Message.rw (RWEvent.read loc val ord) ts) (Ident.Fun.find i m))
           m)
  | step_write
      m
      i loc val ord:
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.write loc val ord)))
        (Ident.Fun.add
           i
           (Buffer.add_history
              (Message.rw
                 (RWEvent.write loc val ord)
                 ((timestamp loc m) + 1))
              (Ident.Fun.find i m))
           m)
  | step_update
      m read_event position
      i loc valr valw ord
      (MESSAGE: In m (Message.rw read_event (timestamp loc m)) position)
      (READ: RWEvent.is_writing read_event = Some (loc, valr))
      (POSITION: position <> Position.buffer i (Buffer.Position.inception (Message.rw read_event (timestamp loc m))))
      (TS: Loc.Fun.find loc (Ident.Fun.find i c) <= (timestamp loc m)):
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.update loc valr valw ord)))
        (Ident.Fun.add
           i
           (Buffer.add_history
              (Message.rw
                 (RWEvent.update loc valr valw ord)
                 ((timestamp loc m) + 1))
              (Ident.Fun.find i m))
           m)
  | step_fence
      m i ord:
      step
        c
        m
        i
        (Some (ThreadEvent.fence ord))
        (Ident.Fun.add i (Buffer.add_history (Message.fence ord) (Ident.Fun.find i m)) m)
  | step_confirm
      m event ts i b
      (MESSAGE: Buffer.confirm (Message.rw event ts) (Ident.Fun.find i m) = Some b):
      step c m i (Some (ThreadEvent.rw event)) (Ident.Fun.add i b m)
  .

  Section Consistency.
    Variable (m:t).

    Inductive prod (pred1 pred2: Message.t -> Prop): relation Position.t :=
    | prod_intro
        pos1 pos2 msg1 msg2
        (POS1: In m msg1 pos1)
        (POS2: In m msg2 pos2)
        (MSG1: pred1 msg1)
        (MSG2: pred2 msg2):
        prod pred1 pred2 pos1 pos2
    .

    Inductive compose (rel1 rel2:relation Position.t): relation Position.t :=
    | compose_intro
        x y z
        (REL1: rel1 x y)
        (REL2: rel2 y z):
        compose rel1 rel2 x z
    .

    Inductive acyclic (rel:relation Position.t): Prop :=
    | acyclic_intro
        (ACYCLIC: Irreflexive (tc rel))
    .

    Inductive sb: relation Position.t :=
    | sb_init
        i pos:
        sb Position.init (Position.buffer i pos)
    | sb_buffer
        i pos1 pos2
        (LT: Buffer.Position.lt pos1 pos2):
        sb (Position.buffer i pos1) (Position.buffer i pos2)
    .

    Inductive sbw: relation Position.t :=
    | sbw_writing
        pos1 pos2 e1 e2 ts1 ts2 loc val1 val2
        (SB: sb pos1 pos2)
        (POS1: In m (Message.rw e1 ts1) pos1)
        (POS2: In m (Message.rw e2 ts2) pos2)
        (WRITE1: RWEvent.is_writing e1 = Some (loc, val1))
        (WRITE2: RWEvent.is_writing e2 = Some (loc, val2)):
        sbw pos1 pos2
    | sbw_fence
        pos1 pos2 ord1 e2 ts2
        (SB: sb pos1 pos2)
        (POS1: In m (Message.fence ord1) pos1)
        (POS2: In m (Message.rw e2 ts2) pos2):
        sbw pos1 pos2
    .

    Inductive rfr: relation Position.t :=
    | rfr_intro
        write_pos read_pos
        write_event ts
        loc val ord
        (WRITEPOS: In m (Message.rw write_event ts) write_pos)
        (READPOS: In m (Message.rw (RWEvent.read loc val ord) ts) read_pos)
        (WRITE: RWEvent.is_writing write_event = Some (loc, val)):
        rfr write_pos read_pos
    .

    Inductive rfu: relation Position.t :=
    | rfu_intro
        write_pos update_pos
        write_event ts
        loc valr valw ord
        (WRITEPOS: In m (Message.rw write_event ts) write_pos)
        (UPDATEPOS: In m (Message.rw (RWEvent.update loc valr valw ord) (ts + 1)) update_pos)
        (WRITE: RWEvent.is_writing write_event = Some (loc, valr)):
        rfu write_pos update_pos
    .

    Definition rf: relation Position.t := rfr \2/ rfu.

    Definition rseq: relation Position.t :=
      compose
        (rc sbw)
        (rtc rfu).

    Inductive aseq: relation Position.t :=
    | aseq_refl
        pos:
        aseq pos pos
    | aseq_fence
        pos1 pos2 ord2
        (SB: sb pos1 pos2)
        (POS2: In m (Message.fence ord2) pos2):
        aseq pos1 pos2
    .

    Definition sw: relation Position.t :=
      (compose rseq (compose rf aseq))
        /2\
        (prod
           (fun msg => Ordering.le Ordering.release (Message.get_ordering msg))
           (fun msg => Ordering.le Ordering.acquire (Message.get_ordering msg)))
    .

    Definition hb: relation Position.t := tc (sb \2/ sw).

    Inductive consistent: Prop :=
    | consistent_intro
        (CoHB: acyclic hb)
        (CoRF: acyclic (compose hb rf))
    .
  End Consistency.
End Memory.
