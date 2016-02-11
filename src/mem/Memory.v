Require Import List.
Require Import Equalities.
Require Import PeanoNat.
Require Import Relations.
Require Import MSetList.
Require Import Omega.

Require Import sflib.
Require Import paco.

Require Import DataStructure.
Require Import Basic.
Require Import Event.
Require Import Thread.
Require Import BoolOrderedType.

Set Implicit Arguments.
Import ListNotations.

Module Clock.
  Definition t := LocFun.t nat.

  Definition init := LocFun.init 0.

  Definition le (lhs rhs:t): Prop :=
    forall loc, LocFun.find loc lhs <= LocFun.find loc rhs.
End Clock.

Module Clocks.
  Definition t := IdentFun.t Clock.t.

  Definition init := IdentFun.init Clock.init.

  Definition le (lhs rhs:t): Prop :=
    forall loc, Clock.le (IdentFun.find loc lhs) (IdentFun.find loc rhs).
End Clocks.


Module Message_ <: BoolOrderedType.S.
  Inductive t_ :=
  | rw (event:RWEvent.t) (timestamp:nat)
  | fence (ord:Ordering.t)
  .
  Definition t := t_.

  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality;
      (try apply RWEvent.eq_dec);
      (try apply Nat.eq_dec);
      (try apply Ordering.eq_dec).
  Qed.

  Definition ltb (lhs rhs:t): bool :=
    match lhs, rhs with
    | rw e1 t1, rw e2 t2 =>
      compose_comparisons [RWEvent.compare e1 e2; Const.compare t1 t2]
    | rw _ _, fence _ => true
    | fence _, rw _ _ => false
    | fence o1, fence o2 =>
      compose_comparisons [Ordering.compare o1 o2]
    end.

  Lemma ltb_trans (x y z:t) (XY: ltb x y) (YZ: ltb y z): ltb x z.
  Proof.
    destruct x, y, z; simpl in *; auto;
      repeat
        (try congruence;
         try omega;
         try RWEvent.ltb_tac;
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
         try RWEvent.ltb_tac;
         try Const.ltb_tac;
         try Ordering.ltb_tac;
         try ltb_des).
  Qed.

  Lemma ltb_eq (lhs rhs:t) (LR: ~ ltb lhs rhs) (RL: ~ ltb rhs lhs): lhs = rhs.
  Proof.
    destruct lhs, rhs; simpl in *; auto;
      repeat
      repeat
        (try congruence;
         try omega;
         try RWEvent.ltb_tac;
         try Const.ltb_tac;
         try Ordering.ltb_tac;
         try ltb_des).
  Qed.
End Message_.

Module Message <: OrderedTypeWithLeibniz.
  Include Message_ <+ BoolOrderedType.Make (Message_).

  Definition get_ordering (e:t): Ordering.t :=
    match e with
    | rw e _ => RWEvent.get_ordering e
    | fence ord => ord
    end.

  Definition observable (msg:t): bool :=
    match msg with
    | rw e _ => if RWEvent.is_writing e then true else false
    | fence _ => false
    end.

  Definition get_threadevent (msg:t): ThreadEvent.t :=
    match msg with
    | rw e _ => ThreadEvent.rw e
    | fence ord => ThreadEvent.fence ord
    end.
End Message.

Module MessageSet := UsualSet (Message).

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
  Definition t := IdentMap.t Buffer.t.

  Definition empty := IdentMap.empty Buffer.t.

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
      b msg i p
      (BUFFER: IdentMap.find i m = Some b)
      (IN: Buffer.In msg b p):
      In m msg (Position.buffer i p)
  .

  Definition timestamp (loc:Loc.t) (m:t): nat :=
    IdentMap.get_max
      (Buffer.timestamp loc)
      m.

  Inductive step (c:Clocks.t): forall (m1:t) (i:Ident.t) (e:option ThreadEvent.t) (m2:t), Prop :=
  | step_read
      m read_event ts position
      i b loc val ord
      (MESSAGE: In m (Message.rw read_event ts) position)
      (READ: RWEvent.is_writing read_event = Some (loc, val))
      (POSITION: position <> Position.buffer i (Buffer.Position.inception (Message.rw read_event ts)))
      (BUFFER: IdentMap.find i m = Some b)
      (TS1: LocFun.find loc (IdentFun.find i c) <= ts)
      (TS2: Buffer.timestamp_history loc b <= ts):
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.read loc val ord)))
        (IdentMap.add
           i
           (Buffer.add_history (Message.rw (RWEvent.read loc val ord) ts) b)
           m)
  | step_write
      m
      i b loc val ord
      (BUFFER: IdentMap.find i m = Some b):
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.write loc val ord)))
        (IdentMap.add
           i
           (Buffer.add_history
              (Message.rw
                 (RWEvent.write loc val ord)
                 ((timestamp loc m) + 1))
              b)
           m)
  | step_update
      m read_event position
      i b loc valr valw ord
      (MESSAGE: In m (Message.rw read_event (timestamp loc m)) position)
      (READ: RWEvent.is_writing read_event = Some (loc, valr))
      (POSITION: position <> Position.buffer i (Buffer.Position.inception (Message.rw read_event (timestamp loc m))))
      (BUFFER: IdentMap.find i m = Some b)
      (TS: LocFun.find loc (IdentFun.find i c) <= (timestamp loc m)):
      step
        c
        m
        i
        (Some (ThreadEvent.rw (RWEvent.update loc valr valw ord)))
        (IdentMap.add
           i
           (Buffer.add_history
              (Message.rw
                 (RWEvent.update loc valr valw ord)
                 ((timestamp loc m) + 1))
              b)
           m)
  | step_fence
      m i b ord
      (BUFFER: IdentMap.find i m = Some b):
      step
        c
        m
        i
        (Some (ThreadEvent.fence ord))
        (IdentMap.add i (Buffer.add_history (Message.fence ord) b) m)
  | step_confirm
      m event ts i b1 b2
      (BUFFER: IdentMap.find i m = Some b1)
      (MESSAGE: Buffer.confirm (Message.rw event ts) b1 = Some b2):
      step c m i (Some (ThreadEvent.rw event)) (IdentMap.add i b2 m)
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
           (fun msg => Ordering.ord Ordering.release (Message.get_ordering msg))
           (fun msg => Ordering.ord Ordering.acquire (Message.get_ordering msg)))
    .

    Definition hb: relation Position.t := tc (sb \2/ sw).

    Inductive consistent: Prop :=
    | consistent_intro
        (CoHB: acyclic hb)
        (CoRF: acyclic (compose hb rf))
    .
  End Consistency.
End Memory.
