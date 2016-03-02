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
  Definition t := IdentFun.t (LocFun.t nat).

  Definition init := IdentFun.init (LocFun.init 0).

  Definition le (lhs rhs:t): Prop :=
    forall tid loc, LocFun.find loc (IdentFun.find tid lhs) <= LocFun.find loc (IdentFun.find tid rhs).

  Definition add tid loc ts (c:t): t :=
    IdentFun.add
      tid
      (LocFun.add loc ts (IdentFun.find tid c))
      c.

  Definition timestamp tid loc (c:t) :=
    LocFun.find loc (IdentFun.find tid c).
End Clock.


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

  Inductive rseq: relation Message.t :=
  | rseq_writing
      e1 e2 ts1 ts2 loc val1 val2 ord1 ord2
      (WRITE1: RWEvent.is_writing e1 = Some (loc, val1, ord1))
      (WRITE2: RWEvent.is_writing e2 = Some (loc, val2, ord2))
      (ORDERING: Ordering.ord Ordering.release ord1):
      rseq (rw e1 ts1) (rw e1 ts2)
  | rseq_fence
      ord msg2
      (ORDERING: Ordering.ord Ordering.release ord):
      rseq (fence ord) msg2
  .

  Definition get_memevent (msg:t): ThreadEvent.mem_t :=
    match msg with
    | rw e _ => ThreadEvent.rw e
    | fence ord => ThreadEvent.fence ord
    end.

  Definition timestamp (loc:Loc.t) (msg:t): option nat :=
    match msg with
    | rw event ts =>
      if option_eq_dec
           Loc.eq_dec
           (option_map (fst <*> fst) (RWEvent.is_writing event))
           (Some loc)
      then Some ts
      else None
    | _ => None
    end.
End Message.

Module Inception <: OrderedTypeWithLeibniz.
  Module Raw <: BoolOrderedType.S.
    Structure t_ := mk {
      message: Message.t;
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
      compose_comparisons [Message.compare lhs.(message) rhs.(message); IdentSet.compare lhs.(threads) rhs.(threads)].

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

  Definition timestamp (loc:Loc.t) (inception:t): option nat :=
    Message.timestamp loc inception.(message).
End Inception.

Module InceptionSet.
  Include UsualSet (Inception).

  Definition has_timestamp (loc:Loc.t) (ts:nat) (inceptions:t): bool :=
    exists_
      (fun inception =>
         match Inception.timestamp loc inception with
         | None => false
         | Some ts' => Nat.eqb ts' ts
         end)
      inceptions.
End InceptionSet.


Module Buffer.
  Definition t := list Message.t.

  Definition empty: t := nil.

  Definition has_timestamp (loc:Loc.t) (ts:nat) (b:t): bool :=
    List.existsb
      (fun msg =>
         match Message.timestamp loc msg with
         | Some timestamp => Nat.eqb timestamp ts
         | None => false
         end)
      b.
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
    | buffer (tid:Ident.t) (pos:nat)
    | inception (inception:Inception.t)
    .

    Definition is_inception_of (p:t) (tid:Ident.t): bool :=
      match p with
      | inception (Inception.mk _ threads) => IdentSet.mem tid threads
      | _ => false
      end.

    Inductive sb: relation t :=
    | sb_init
        tid pos:
        sb init (buffer tid pos)
    | sb_buffer
        tid pos1 pos2
        (LT: pos1 < pos2):
        sb (buffer tid pos1) (buffer tid pos2)
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
        b msg tid n
        (BUFFER: IdentMap.find tid m.(buffers) = Some b)
        (IN: List.nth_error b n = Some msg):
        In msg (Position.buffer tid n)
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

    Inductive mo: relation Position.t :=
    | mo_intro
        pos1 pos2 e1 e2 ts1 ts2 loc val1 val2 ord1 ord2
        (TIMESTAMP: ts1 < ts2)
        (POS1: In (Message.rw e1 ts1) pos1)
        (POS2: In (Message.rw e2 ts2) pos2)
        (WRITE1: RWEvent.is_writing e1 = Some (loc, val1, ord1))
        (WRITE2: RWEvent.is_writing e2 = Some (loc, val2, ord2)):
        mo pos1 pos2
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

    Inductive rseq_base: relation Position.t :=
    | rseq_base_intro
        msg_rel msg_w
        pos_rel pos_w
        (REL: In msg_rel pos_rel)
        (W: In msg_w pos_w)
        (RSEQ: Message.rseq msg_rel msg_w)
        (SB: rc Position.sb pos_rel pos_w):
        rseq_base pos_rel pos_w
    .

    Definition rseq := compose rseq_base (rtc rfu).

    (* TODO: tight up? *)
    Inductive aseq: relation Position.t :=
    | aseq_refl
        msg pos
        (IN: In msg pos)
        (ORDERING: Ordering.ord Ordering.acquire (Message.get_ordering msg)):
        aseq pos pos
    | aseq_fence
        pos1 pos2 ord2
        (SB: Position.sb pos1 pos2)
        (IN: In (Message.fence ord2) pos2)
        (ORDERING: Ordering.ord Ordering.acquire ord2):
        aseq pos1 pos2
    .

    Definition sw: relation Position.t := compose rseq (compose rf aseq).

    Definition hb: relation Position.t := tc (Position.sb \2/ sw).

    Inductive consistent: Prop :=
    | consistent_intro
        (CoHB: Irreflexive hb)
        (CoRF: Irreflexive (compose hb rf))
        (CoMO: Irreflexive (compose hb mo))
        (RF: forall msgr posr
               (IN: In msgr posr)
               (READING: Message.is_reading msgr),
            exists posw, rf posw posr)
    .
  End Consistency.

  Definition add_message tid msg m: option (Position.t * t) :=
    match IdentMap.find tid m.(buffers) with
    | None => None
    | Some b =>
      Some (Position.buffer tid (List.length b),
            mk (IdentMap.add tid (b ++ [msg]) m.(buffers))
               (InceptionSet.filter
                  (fun inception =>
                     if Message.eq_dec msg inception.(Inception.message)
                     then negb (IdentSet.mem tid inception.(Inception.threads))
                     else true)
                  m.(inceptions)))
    end.

  Definition has_timestamp (loc:Loc.t) (ts:nat) (m:t): bool :=
    IdentMap.Properties.exists_ (fun _ => Buffer.has_timestamp loc ts) m.(buffers) ||
    InceptionSet.has_timestamp loc ts m.(inceptions).

  Definition acquirable (c:Clock.t) (tid:Ident.t) (m:t) (pos_w:Position.t): Prop :=
    forall e ts loc val ord pos pos_rel
      (MESSAGE: In m (Message.rw e ts) pos)
      (WRITING: RWEvent.is_writing e = Some (loc, val, ord))
      (SB: rc Position.sb pos pos_rel)
      (RSEQ: rseq m pos_rel pos_w),
      ts <= Clock.timestamp tid loc c.

  Definition releasable (c:Clock.t) (tid:Ident.t) (m:t) (loc:Loc.t): Prop :=
    forall e val ord ts threads
      (WRITING: RWEvent.is_writing e = Some (loc, val, ord))
      (THREADS: IdentSet.mem tid threads)
      (INCEPTION: InceptionSet.mem (Inception.mk (Message.rw e ts) threads) m.(inceptions)),
      False.

  Inductive readable (c:Clock.t) (tid:Ident.t) (m:t) (loc:Loc.t) (val:Const.t) (ts:nat) (ord:Ordering.t): Prop :=
  | readable_intro
      e ordw pos
      (WRITING: RWEvent.is_writing e = Some (loc, val, ordw))
      (POS: In m (Message.rw e ts) pos)
      (NINCEPTION: ~ Position.is_inception_of pos tid)
      (TIMESTAMP: Clock.timestamp tid loc c <= ts)
      (ACQUIRE: forall (ORDERING: Ordering.ord Ordering.acquire ord), acquirable c tid m pos)
  .

  Inductive writable (c:Clock.t) (tid:Ident.t) (m:t) (loc:Loc.t) (ts:nat) (ord:Ordering.t): Prop :=
  | writable_intro
      (CLOCK: forall i, Clock.timestamp i loc c < ts)
      (UNIQUE: ~ has_timestamp loc ts m)
      (TIMESTAMP1: forall msg n timestamp
                     (IN: In m msg (Position.buffer tid n))
                     (TIMESTAMP: Message.timestamp loc msg = Some timestamp),
          timestamp < ts)
      (TIMESTAMP2: forall msg threads timestamp
                     (IN: InceptionSet.mem (Inception.mk msg threads) m.(inceptions))
                     (THREADS: IdentSet.mem tid threads)
                     (TIMESTAMP: Message.timestamp loc msg = Some timestamp),
          ts < timestamp)
      (RELEASE: forall (ORDERING: Ordering.ord Ordering.release ord), releasable c tid m loc)
  .

  Inductive fencable (c:Clock.t) (tid:Ident.t) (m:t) (ord:Ordering.t): Prop :=
  | fencable_intro
      (ACQUIRE: forall pos_w n (RF: rf m pos_w (Position.buffer tid n)), acquirable c tid m pos_w)
      (RELEASE: forall loc, releasable c tid m loc)
  .

  Inductive message (c:Clock.t) (m1:t) (tid:Ident.t): forall (e:ThreadEvent.mem_t) (msg:Message.t), Prop :=
  | message_read
      loc val ts ord
      (READABLE: readable c tid m1 loc val ts ord):
      message c m1 tid
           (ThreadEvent.rw (RWEvent.read loc val ord))
           (Message.rw (RWEvent.read loc val ord) ts)
  | message_write
      loc val ord ts
      (WRITABLE: writable c tid m1 loc ts ord):
      message c m1 tid
           (ThreadEvent.rw (RWEvent.write loc val ord))
           (Message.rw (RWEvent.write loc val ord) ts)
  | message_update
      loc val ts valu ord
      (READABLE: readable c tid m1 loc val ts ord)
      (WRITABLE: writable c tid m1 loc (ts + 1) ord):
      message c m1 tid
           (ThreadEvent.rw (RWEvent.update loc val valu ord))
           (Message.rw (RWEvent.update loc val valu ord) (ts + 1))
  | message_fence
      ord
      (FENCABLE: fencable c tid m1 ord):
      message c m1 tid (ThreadEvent.fence ord) (Message.fence ord)
  .

  Inductive step (c:Clock.t) (m1:t) (tid:Ident.t): forall (e:option ThreadEvent.mem_t) (m2:t), Prop :=
  | step_None:
      step c m1 tid None m1
  | step_Some
      e msg pos m2
      (MESSAGE: message c m1 tid e msg)
      (ADD: add_message tid msg m1 = Some (pos, m2))
      (NRSEQ: InceptionSet.For_all
                (fun inception => ~ rseq m2 pos (Position.inception inception))
                m2.(inceptions))
      (CONSISTENT: consistent m2):
      step c m1 tid (Some e) m2
  .

  Inductive inception (m1 m2:t): forall inception, Prop :=
  | inception_intro
      b1 tid n ew ts ths
      (INCEPTIONS: InceptionSet.Empty m2.(inceptions))
      (BUFFER: IdentMap.find tid m1.(buffers) = Some b1)
      (LENGTH: length b1 <= n)
      (MESSAGE: In m2 (Message.rw ew ts) (Position.buffer tid n))
      (WRITING: if RWEvent.is_writing ew then true else false)
      (READING: forall pos (RF: rf m2 pos (Position.buffer tid n)), exists msg, In m1 msg pos)
      (NRELEASE: ~ Ordering.ord Ordering.release (RWEvent.get_ordering ew))
      (PROGRAM: IdentSet.mem tid ths):
      inception m1 m2 (Inception.mk (Message.rw ew ts) ths)
  .

  Inductive inceptionless tid (m:t): Prop :=
  | inceptionness_intro
      (INCEPTIONLESS: InceptionSet.For_all
                        (fun inception => negb (IdentSet.mem tid inception.(Inception.threads)))
                        m.(inceptions))
  .
End Memory.
