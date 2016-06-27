
(******************************************************************************)
(** * Definition of graph events *)
(******************************************************************************)

Require Import Hahn.

Require Import Basic Event.

Set Implicit Arguments.

Definition act_id := nat.
Definition thread_id := IdentMap.key.

Inductive label := 
  | Aload (l:Loc.t) (v:Const.t) (o:Ordering.t)
  | Astore (l:Loc.t) (v:Const.t) (o:Ordering.t)
  | Arfence (o:Ordering.t)
  | Awfence (o:Ordering.t).

Inductive event := 
  | Event (id: act_id) (tid: thread_id) (lb:label).

Definition id a :=
  match a with
  | Event  id _ _ => id
  end.

Definition thread a :=
  match a with
  | Event  _ i _ => i
  end.

Definition lab a :=
  match a with
  | Event  _ _ lb => lb
  end.

Definition loc a :=
  match (lab a) with
  | Aload l _ _
  | Astore l _ _ => Some l
  | _ => None
  end.

Definition val a :=
  match (lab a) with
  | Aload  _ v _
  | Astore _ v _ => Some v
  | _ => None
  end.

Definition ord a :=
  match (lab a) with
  | Aload  _ _ o
  | Astore _ _ o
  | Arfence o 
  | Awfence o => o
  end.

Definition is_read a := 
  match (lab a) with
  | Aload  _ _ _ => True
  | _ => False
  end.

Definition is_write a := 
  match (lab a) with
  | Astore _ _ _ => True
  | _ => False
  end.

Definition is_rfence a := 
  match (lab a) with
  | Arfence _ => True
  | _ => False
  end.

Definition is_wfence a := 
  match (lab a) with
  | Awfence  _ => True
  | _ => False
  end.

Definition is_rlx a :Prop := Ordering.le Ordering.relaxed (ord a).
Definition is_ra  a :Prop := Ordering.le Ordering.acqrel  (ord a).
Definition is_sc  a :Prop := Ordering.le Ordering.seqcst  (ord a).

(** * Basic Lemmas *)

Lemma read_non_write a (A: is_read a) : ~ is_write a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_non_read a (A: is_write a) : ~ is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma wfence_non_read a (A: is_wfence a) : ~ is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_non_rfence a (A: is_write a) : ~ is_rfence a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_non_wfence a (A: is_write a) : ~ is_wfence a.
Proof. destruct a; destruct lb; ins. Qed.


Lemma write_has_location a (WRITE: is_write a) : exists l, loc a = Some l.
Proof. unfold loc; destruct a; destruct lb; ins; eauto. Qed.
Lemma ra_is_rlx a (RA: is_ra a) : is_rlx a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.
Lemma sc_is_rlx a (SC: is_sc a) : is_rlx a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.
Lemma sc_is_ra a (SC: is_sc a) : is_ra a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.

Lemma read_is_read a l v o (A: lab a = Aload l v o) : is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_is_write a l v o (A: lab a = Astore l v o) : is_write a.
Proof. destruct a; destruct lb; ins. Qed.

Lemma read_rlx a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.relaxed o -> is_rlx a.
Proof. unfold is_rlx; unfold ord; rewrite A; done. Qed.
Lemma read_ra a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.acqrel o -> is_ra a.
Proof. unfold is_ra; unfold ord; rewrite A; done. Qed.
Lemma read_sc a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.seqcst o -> is_sc a.
Proof. unfold is_sc; unfold ord; rewrite A; done. Qed.

Lemma write_rlx a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.relaxed o -> is_rlx a.
Proof. unfold is_rlx; unfold ord; rewrite A; done. Qed.
Lemma write_ra a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.acqrel o -> is_ra a.
Proof. unfold is_ra; unfold ord; rewrite A; done. Qed.
Lemma write_sc a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.seqcst o -> is_sc a.
Proof. unfold is_sc; unfold ord; rewrite A; done. Qed.


Hint Resolve  read_non_write write_non_read wfence_non_read ra_is_rlx 
sc_is_rlx sc_is_ra read_is_read read_rlx read_ra read_sc
write_is_write write_rlx write_ra write_sc 
write_non_rfence write_non_wfence : acts.

