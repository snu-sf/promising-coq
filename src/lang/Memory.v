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
Require Import Program.
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


Module Message <: OrderedTypeWithLeibniz.
  Module Raw <: BoolOrderedType.S.
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
  End Raw.

  Include Raw <+ BoolOrderedType.Make (Raw).

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

  Definition get_memevent (msg:t): ThreadEvent.mem_t :=
    match msg with
    | rw e _ => ThreadEvent.rw e
    | fence ord => ThreadEvent.fence ord
    end.
End Message.

Module Inception <: OrderedTypeWithLeibniz.
  Module Raw <: BoolOrderedType.S.
    Structure t_ := mk {
      msg: Message.t;
      threads: IdentSet.t;
    }.
    Definition t := t_.

    Definition eq_dec (x y:t): {x = y} + {x <> y}.
    Proof.
      decide equality.
      - destruct (IdentSet.eq_dec threads0 threads1).
        + left. apply IdentSet.eq_leibniz. auto.
        + right. contradict n. auto. subst. reflexivity.
      - apply Message.eq_dec.
    Qed.

    Definition ltb (lhs rhs:t): bool :=
      compose_comparisons [Message.compare lhs.(msg) rhs.(msg); IdentSet.compare lhs.(threads) rhs.(threads)].

    Lemma ltb_trans (x y z:t) (XY: ltb x y) (YZ: ltb y z): ltb x z.
    Proof.
    Admitted.

    Lemma ltb_irrefl x: ~ ltb x x.
    Proof.
    Admitted.

    Lemma ltb_eq (lhs rhs:t) (LR: ~ ltb lhs rhs) (RL: ~ ltb rhs lhs): lhs = rhs.
    Proof.
    Admitted.
  End Raw.

  Include Raw <+ BoolOrderedType.Make (Raw).
End Inception.

Module InceptionSet := UsualSet (Inception).

Module Buffer.
  Definition t := list Message.t.

  Definition empty: t := nil.

  Definition timestamp (loc:Loc.t) (b:t): nat :=
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
      b
      0.
End Buffer.

Module Memory.
  Structure t := mk {
    buffers: IdentMap.t Buffer.t;
    inceptions: InceptionSet.t;
  }.

  Definition init (syntax:Program.syntax) :=
    Memory.mk
      (IdentMap.map (fun _ => Buffer.empty) syntax)
      InceptionSet.empty.

  Definition update_buffer (i:Ident.t) (b:Buffer.t) (m:t): t :=
    mk (IdentMap.add i b m.(buffers)) m.(inceptions).

  Definition update_inceptions (inceptions:InceptionSet.t) (m:t): t :=
    mk m.(buffers) inceptions.

  Module Position.
    Inductive t :=
    | init
    | buffer (i:Ident.t) (pos:nat)
    | inception (i:Inception.t)
    .

    Definition is_inception_of (p:t) (i:Ident.t): bool :=
      match p with
      | inception (Inception.mk _ threads) => IdentSet.mem i threads
      | _ => false
      end.
  End Position.

  Inductive In (m:t): forall (msg:Message.t) (p:Position.t), Prop :=
  | In_init
      loc:
      In m (Message.rw (RWEvent.write loc Const.zero Ordering.release) 0) Position.init
  | In_buffer
      b msg i n
      (BUFFER: IdentMap.find i m.(buffers) = Some b)
      (IN: List.nth_error b n = Some msg):
      In m msg (Position.buffer i n)
  | In_inception
      msg threads
      (INCEPTION: InceptionSet.mem (Inception.mk msg threads) m.(inceptions)):
      In m msg (Position.inception (Inception.mk msg threads))
  .

  Definition timestamp_inceptions (loc:Loc.t) (inceptions:InceptionSet.t): nat :=
    InceptionSet.fold
      (fun inception res =>
         match inception with
         | Inception.mk (Message.rw event timestamp) _ =>
           if option_eq_dec
                Loc.eq_dec
                (option_map fst (RWEvent.is_writing event))
                (Some loc)
           then max timestamp res
           else res
         | _ => res
         end)
      inceptions
      0.

  Definition timestamp (loc:Loc.t) (m:t): nat :=
    max (IdentMap.get_max
           (Buffer.timestamp loc)
           m.(buffers))
        (timestamp_inceptions loc m.(inceptions)).

  Inductive step (c:Clocks.t): forall (m1:t) (i:Ident.t) (e:ThreadEvent.mem_t) (m2:t), Prop :=
  | step_read
      m read_event ts position
      i b loc val ord
      (MESSAGE: In m (Message.rw read_event ts) position)
      (READ: RWEvent.is_writing read_event = Some (loc, val))
      (POSITION: ~ Position.is_inception_of position i)
      (BUFFER: IdentMap.find i m.(buffers) = Some b)
      (TS1: LocFun.find loc (IdentFun.find i c) <= ts)
      (TS2: Buffer.timestamp loc b <= ts):
      step c m i (ThreadEvent.rw (RWEvent.read loc val ord))
           (mk (IdentMap.add i (b ++ [Message.rw (RWEvent.read loc val ord) ts]) m.(buffers)) m.(inceptions))
  | step_write
      m
      i b loc val ord
      (BUFFER: IdentMap.find i m.(buffers) = Some b):
      step c m i (ThreadEvent.rw (RWEvent.write loc val ord))
           (mk (IdentMap.add i (b ++ [Message.rw (RWEvent.write loc val ord) ((timestamp loc m) + 1)]) m.(buffers)) m.(inceptions))
  | step_update
      m read_event position
      i b loc valr valw ord
      (MESSAGE: In m (Message.rw read_event (timestamp loc m)) position)
      (READ: RWEvent.is_writing read_event = Some (loc, valr))
      (POSITION: ~ Position.is_inception_of position i)
      (BUFFER: IdentMap.find i m.(buffers) = Some b)
      (TS: LocFun.find loc (IdentFun.find i c) <= (timestamp loc m)):
      step c m i (ThreadEvent.rw (RWEvent.update loc valr valw ord))
           (mk (IdentMap.add i (b ++ [Message.rw (RWEvent.update loc valr valw ord) ((timestamp loc m) + 1)]) m.(buffers)) m.(inceptions))
  | step_fence
      m i b ord
      (BUFFER: IdentMap.find i m.(buffers) = Some b):
      step c m i (ThreadEvent.fence ord)
           (mk (IdentMap.add i (b ++ [Message.fence ord]) m.(buffers)) m.(inceptions))
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
        (LT: pos1 < pos2):
        sb (Position.buffer i pos1) (Position.buffer i pos2)
    | sb_inception
        i1 pos1 inception2
        (INCEPTION: IdentSet.mem i1 inception2.(Inception.threads)):
        sb (Position.buffer i1 pos1) (Position.inception inception2)
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
