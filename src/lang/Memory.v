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

  Definition is_writing (msg:t): bool :=
    match msg with
    | rw e _ => if RWEvent.is_writing e then true else false
    | fence _ => false
    end.

  Definition is_reading (msg:t): bool :=
    match msg with
    | rw e _ => if RWEvent.is_reading e then true else false
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

Module InceptionSet.
  Include UsualSet (Inception).

  Definition timestamp (loc:Loc.t) (inceptions:t): nat :=
    fold
      (fun inception res =>
         match inception with
         | Inception.mk (Message.rw event timestamp) _ =>
           if option_eq_dec
                Loc.eq_dec
                (option_map (fst <*> fst) (RWEvent.is_writing event))
                (Some loc)
           then max timestamp res
           else res
         | _ => res
         end)
      inceptions
      0.
End InceptionSet.


Module Clock.
  Definition t := IdentFun.t (LocFun.t nat).

  Definition init := IdentFun.init (LocFun.init 0).

  Definition le (lhs rhs:t): Prop :=
    forall i loc, LocFun.find loc (IdentFun.find i lhs) <= LocFun.find loc (IdentFun.find i rhs).

  Definition add i loc ts (c:t): t :=
    IdentFun.add
      i
      (LocFun.add loc ts (IdentFun.find i c))
      c.

  Definition timestamp i loc (c:t) :=
    LocFun.find loc (IdentFun.find i c).
End Clock.


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
                (option_map (fst <*> fst) (RWEvent.is_writing event))
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
    mk
      (IdentMap.map (fun _ => Buffer.empty) syntax)
      InceptionSet.empty.

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

    Inductive sb: relation t :=
    | sb_init
        i pos:
        sb init (buffer i pos)
    | sb_buffer
        i pos1 pos2
        (LT: pos1 < pos2):
        sb (buffer i pos1) (buffer i pos2)
    | sb_inception
        i1 pos1 inception2
        (INCEPTION: IdentSet.mem i1 inception2.(Inception.threads)):
        sb (buffer i1 pos1) (inception inception2)
    .
  End Position.

  Section Consistency.
    Variable (m:t).

    Inductive In: forall (msg:Message.t) (p:Position.t), Prop :=
    | In_init
        loc:
        In (Message.rw (RWEvent.write loc Const.zero Ordering.release) 0) Position.init
    | In_buffer
        b msg i n
        (BUFFER: IdentMap.find i m.(buffers) = Some b)
        (IN: List.nth_error b n = Some msg):
        In msg (Position.buffer i n)
    | In_inception
        msg threads
        (INCEPTION: InceptionSet.mem (Inception.mk msg threads) m.(inceptions)):
        In msg (Position.inception (Inception.mk msg threads))
    .

    Inductive prod (pred1 pred2: Message.t -> Prop): relation Position.t :=
    | prod_intro
        pos1 pos2 msg1 msg2
        (POS1: In msg1 pos1)
        (POS2: In msg2 pos2)
        (MSG1: pred1 msg1)
        (MSG2: pred2 msg2):
        prod pred1 pred2 pos1 pos2
    .

    Inductive acyclic (rel:relation Position.t): Prop :=
    | acyclic_intro
        (ACYCLIC: Irreflexive (tc rel))
    .

    Inductive sbw: relation Position.t :=
    | sbw_writing
        pos1 pos2 e1 e2 ts1 ts2 loc val1 val2
        (SB: Position.sb pos1 pos2)
        (POS1: In (Message.rw e1 ts1) pos1)
        (POS2: In (Message.rw e2 ts2) pos2)
        (WRITE1: RWEvent.is_writing e1 = Some (loc, val1))
        (WRITE2: RWEvent.is_writing e2 = Some (loc, val2)):
        sbw pos1 pos2
    | sbw_fence
        pos1 pos2 ord1 e2 ts2
        (SB: Position.sb pos1 pos2)
        (POS1: In (Message.fence ord1) pos1)
        (POS2: In (Message.rw e2 ts2) pos2):
        sbw pos1 pos2
    .

    Inductive rfr: relation Position.t :=
    | rfr_intro
        posw posr
        ew ts ordw
        loc val ordr
        (WRITEPOS: In (Message.rw ew ts) posw)
        (WRITE: RWEvent.is_writing ew = Some (loc, val, ordw))
        (READPOS: In (Message.rw (RWEvent.read loc val ordr) ts) posr):
        rfr posw posr
    .

    Inductive rfu: relation Position.t :=
    | rfu_intro
        posw posu
        ew ts ordw
        loc valr valw ordu
        (WRITEPOS: In (Message.rw ew ts) posw)
        (WRITE: RWEvent.is_writing ew = Some (loc, valr, ordw))
        (UPDATEPOS: In (Message.rw (RWEvent.update loc valr valw ordu) (ts + 1)) posu):
        rfu posw posu
    .

    Definition rf: relation Position.t := rfr \2/ rfu.

    Definition rseq: relation Position.t := compose (rc sbw) (rtc rfu).

    Inductive aseq: relation Position.t :=
    | aseq_refl
        pos:
        aseq pos pos
    | aseq_fence
        pos1 pos2 ord2
        (SB: Position.sb pos1 pos2)
        (POS2: In (Message.fence ord2) pos2):
        aseq pos1 pos2
    .

    Definition sw: relation Position.t :=
      (compose rseq (compose rf aseq))
        /2\
        (prod
           (fun msg => Ordering.ord Ordering.release (Message.get_ordering msg))
           (fun msg => Ordering.ord Ordering.acquire (Message.get_ordering msg)))
    .

    Definition hb: relation Position.t := tc (Position.sb \2/ sw).

    Inductive consistent: Prop :=
    | consistent_intro
        (CoHB: acyclic hb)
        (CoRF: acyclic (compose hb rf))
        (RF: forall msgr posr
               (IN: In msgr posr)
               (READING: Message.is_reading msgr),
            exists posw, rf posw posr)
    .
  End Consistency.

  Definition add_message i msg m: option (Position.t * t) :=
    match IdentMap.find i m.(buffers) with
    | None => None
    | Some b =>
      Some (Position.buffer i (List.length b),
            mk (IdentMap.add i (b ++ [msg]) m.(buffers))
               (InceptionSet.filter
                  (fun inception =>
                     if Message.eq_dec msg inception.(Inception.msg)
                     then negb (IdentSet.mem i inception.(Inception.threads))
                     else true)
                  m.(inceptions)))
    end.

  Definition timestamp (loc:Loc.t) (m:t): nat :=
    IdentMap.fold
      (fun _ b res => max (Buffer.timestamp loc b) res)
      m.(buffers)
      0%nat.

  Inductive message (c1:Clock.t) (m1:t) (i:Ident.t): forall (e:ThreadEvent.mem_t) (c2:Clock.t) (msg:Message.t), Prop :=
  | message_read
      ew ts posw loc val ordw
      ordr
      (MESSAGE: In m1 (Message.rw ew ts) posw)
      (READ: RWEvent.is_writing ew = Some (loc, val, ordw))
      (POSITION: ~ Position.is_inception_of posw i)
      (TIMESTAMP: Clock.timestamp i loc c1 <= ts):
      message c1 m1 i
           (ThreadEvent.rw (RWEvent.read loc val ordr))
           c1
           (Message.rw (RWEvent.read loc val ordr) ts)
  | message_write
      loc val ord ts
      (TIMESTAMP: timestamp loc m1 < ts):
      message c1 m1 i
           (ThreadEvent.rw (RWEvent.write loc val ord))
           (Clock.add i loc ts c1)
           (Message.rw (RWEvent.write loc val ord) ts)
  | message_update
      ew posw loc valr valw ordw
      ordu
      (MESSAGE: In m1 (Message.rw ew (timestamp loc m1)) posw)
      (READ: RWEvent.is_writing ew = Some (loc, valr, ordw))
      (POSITION: ~ Position.is_inception_of posw i):
      message c1 m1 i
           (ThreadEvent.rw (RWEvent.update loc valr valw ordu))
           (Clock.add i loc ((timestamp loc m1) + 1) c1)
           (Message.rw (RWEvent.update loc valr valw ordu) ((timestamp loc m1) + 1))
  | message_fence
      ordf:
      message c1 m1 i (ThreadEvent.fence ordf) c1 (Message.fence ordf)
  .

  Inductive step (c1:Clock.t) (m1:t) (i:Ident.t): forall (e:ThreadEvent.mem_t) (c2:Clock.t) (m2:t), Prop :=
  | step_intro
      e c2 msg pos m2
      (MESSAGE: message c1 m1 i e c2 msg)
      (ADD: Memory.add_message i msg m1 = Some (pos, m2))
      (NRSEQ: InceptionSet.For_all
                (fun inception => ~ Memory.rseq m2 pos (Memory.Position.inception inception))
                m2.(Memory.inceptions))
      (CONSISTENT: Memory.consistent m2):
      step c1 m1 i e c2 m2
  .

  Inductive inception (m:t): forall inception, Prop :=
  | inception_intro
      ew ts i n ths
      (INCEPTIONS: InceptionSet.Empty m.(inceptions))
      (MESSAGE: In m (Message.rw ew ts) (Position.buffer i n))
      (WRITING: if RWEvent.is_writing ew then true else false)
      (NRELEASE: ~ Ordering.ord Ordering.release (RWEvent.get_ordering ew))
      (PROGRAM: IdentSet.mem i ths):
      inception m (Inception.mk (Message.rw ew ts) ths)
  .
End Memory.
