
(******************************************************************************)
(** * Definition of graph events *)
(******************************************************************************)

Require Import Hahn.

Require Import Basic Event.

Set Implicit Arguments.

Definition act_id := nat.
Definition thread_id := option IdentMap.key.

Inductive label := 
  | Aload (l:Loc.t) (v:Const.t) (o:Ordering.t)
  | Astore (l:Loc.t) (v:Const.t) (o:Ordering.t)
  | Afence (or ow:Ordering.t).

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
  match lab a with
  | Aload l _ _
  | Astore l _ _ => Some l
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload  _ v _
  | Astore _ v _ => Some v
  | _ => None
  end.

Definition is_read a := 
  match lab a with
  | Aload  _ _ _ => True
  | _ => False
  end.

Definition is_write a := 
  match lab a with
  | Astore _ _ _ => True
  | _ => False
  end.

Definition is_fence a := 
  match lab a with
  | Afence _ _ => True
  | _ => False
  end.

Definition is_rlx_rw a : Prop :=
  match lab a with
    | Aload  _ _ o
    | Astore  _ _ o => Ordering.le Ordering.relaxed o
    | _ => False
  end.

Definition is_acq a : Prop :=
  match lab a with
    | Aload  _ _ o
    | Afence o _ => Ordering.le Ordering.acqrel o
    | _ => False
  end.

Definition is_rel a : Prop :=
  match lab a with
    | Astore  _ _ o
    | Afence _ o => Ordering.le Ordering.acqrel o
    | _ => False
  end.

Definition is_sc a : Prop :=
  match lab a with
    | Astore  _ _ o
    | Aload  _ _ o
    | Afence _ o => Ordering.le Ordering.seqcst o
  end.

Definition is_sc_fence a : Prop :=
  match lab a with
    | Afence _ o => Ordering.le Ordering.seqcst o
    | _ => False
  end.

Definition is_sc_write a : Prop :=
  match lab a with
    | Astore _ _ o => Ordering.le Ordering.seqcst o
    | _ => False
  end.

Definition is_sc_wf a : Prop := is_sc_fence a \/ is_sc_write a.

(** * Basic Lemmas *)

Lemma read_non_write a (A: is_read a) : ~ is_write a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma read_non_fence a (A: is_read a) : ~ is_fence a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_non_read a (A: is_write a) : ~ is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_non_fence a (A: is_write a) : ~ is_fence a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma fence_non_read a (A: is_fence a) : ~ is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma fence_non_write a (A: is_fence a) : ~ is_write a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma sc_fence_is_sc_wf a (A: is_sc_fence a) : is_sc_wf a.
Proof. vauto. Qed.
Lemma sc_write_is_sc_wf a (A: is_sc_write a) : is_sc_wf a.
Proof. vauto. Qed.
Lemma sc_wf_is_sc a (A: is_sc_wf a) : is_sc a.
Proof. unfold is_sc, is_sc_wf in *.
       destruct a; destruct lb; ins; desf. Qed.
Lemma sc_write_is_sc_write a (A: is_sc a) (B: is_write a) : is_sc_write a.
Proof. unfold is_sc, is_sc_wf in *.
       destruct a; destruct lb; ins; desf. Qed.
Lemma sc_fence_is_sc_fence a (A: is_sc a) (B: is_fence a) : is_sc_fence a.
Proof. unfold is_sc, is_sc_wf in *.
       destruct a; destruct lb; ins; desf. Qed.

Lemma sc_is_rel a (A: is_sc_wf a) : is_rel a.
Proof. unfold is_sc_wf, is_rel, is_sc_fence, is_sc_write in *.
       destruct a; destruct lb; ins; desf.
       destruct o; ins. destruct ow; ins. 
Qed.

Lemma sc_fence_is_fence a (A: is_sc_fence a) : is_fence a.
Proof. destruct a; destruct lb; ins. Qed.

Lemma write_has_location a (WRITE: is_write a) : exists l, loc a = Some l.
Proof. unfold loc; destruct a; destruct lb; ins; eauto. Qed.
(*
Lemma ra_is_rlx a (RA: is_ra a) : is_rlx a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.
Lemma sc_is_rlx a (SC: is_sc a) : is_rlx a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.
Lemma sc_is_ra a (SC: is_sc a) : is_ra a.
Proof. destruct a; destruct lb; destruct o; ins. Qed.
*)

Lemma read_is_read a l v o (A: lab a = Aload l v o) : is_read a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma write_is_write a l v o (A: lab a = Astore l v o) : is_write a.
Proof. destruct a; destruct lb; ins. Qed.
Lemma fence_is_fence a or ow (A: lab a = Afence or ow) : is_fence a.
Proof. destruct a; destruct lb; ins. Qed.

Lemma read_rlx a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.relaxed o -> is_rlx_rw a.
Proof. destruct a; ins; rewrite A; done. Qed.
Lemma read_acq a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.acqrel o -> is_acq a.
Proof. destruct a; ins; rewrite A; done. Qed.
Lemma read_sc a l v o (A: lab a = Aload l v o) : Ordering.le Ordering.seqcst o -> is_sc a.
Proof. destruct a; ins; rewrite A; done. Qed.

Lemma write_rlx a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.relaxed o -> is_rlx_rw a.
Proof. destruct a; ins; rewrite A; done. Qed.
Lemma write_rel a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.acqrel o -> is_rel a.
Proof. destruct a; ins; rewrite A; done. Qed.
Lemma write_sc a l v o (A: lab a = Astore l v o) : Ordering.le Ordering.seqcst o -> is_sc a.
Proof. destruct a; ins; rewrite A; done. Qed.

Hint Resolve  read_non_write read_non_fence write_non_read fence_non_read 
     read_is_read read_rlx read_acq read_sc
     write_is_write write_rlx write_rel write_sc 
     write_non_fence write_non_fence 
     fence_is_fence fence_non_write
     sc_fence_is_sc_wf sc_write_is_sc_wf sc_wf_is_sc
     sc_write_is_sc_write sc_fence_is_sc_fence
     sc_is_rel sc_fence_is_fence : acts.

(******************************************************************************)
(** ** Initialization *)
(******************************************************************************)

  Definition init_event l := Event 0 None (Astore l 0 Ordering.relaxed).
  Definition is_init a := exists l, a = init_event l.
  Definition is_proper a := exists i_a, thread a = Some i_a.
  Definition init_pair a b := is_init a /\ is_proper b.

Lemma init_not_proper a (INIT: is_init a): ~ is_proper a.
Proof. ins; intro H; unfold is_init, is_proper in *; desc; desf. Qed.

Lemma proper_non_init a (NON_INIT: is_proper a): ~ is_init a.
Proof. ins; intro H; unfold is_init, is_proper in *; desc; desf. Qed.

Lemma init_proper_thread a b (INIT: is_init a) (NON_INIT: is_proper b): ~ thread a = thread b.
Proof. ins; intro H; unfold is_init, is_proper, thread in *; desc; desf. Qed.

Lemma thread_proper a b (T: thread a = thread b): is_proper a <-> is_proper b.
Proof. split; intro H; unfold is_proper in *; desc; subst; ins; exists i_a; congruence. Qed.

Lemma init_is_write a (A: is_init a) : is_write a.
Proof. unfold is_init in *; desc; destruct a; destruct lb; ins. Qed.

Lemma init_is_rlx a (A: is_init a) : is_rlx_rw a.
Proof. unfold is_init, init_event, is_rlx_rw in *; desc. 
destruct a; destruct lb; ins; desf. Qed.

Lemma init_not_acq a (A: is_init a) : ~ is_acq a.
Proof. unfold is_init, init_event, is_rlx_rw in *; desc. 
destruct a; destruct lb; ins; desf. Qed.

Lemma init_not_rel a (A: is_init a) : ~ is_rel a.
Proof. unfold is_init, init_event, is_rlx_rw in *; desc. 
destruct a; destruct lb; ins; desf. Qed.

Lemma init_not_sc a (A: is_init a) : ~ is_sc a.
Proof. unfold is_init, init_event, is_rlx_rw in *; desc. 
destruct a; destruct lb; ins; desf. Qed.

Lemma same_init a b (A: is_init a) (B: is_init b) (LOC: loc a = loc b) :  a=b.
Proof. unfold is_init,init_event,loc,lab in *; desf. Qed.

Hint Resolve  init_not_proper proper_non_init init_proper_thread thread_proper 
  init_is_write init_is_rlx init_not_acq init_not_rel init_not_sc : acts.

(******************************************************************************)
(** ** Decidable equality *)
(******************************************************************************)

Require Import Omega.

Lemma eq_dec_labels :
  forall x y : label, {x = y} + {x <> y}.
Proof.
decide equality; eauto using Ident.eq_dec, eq_nat_dec; decide equality.
Qed.

Lemma eq_dec_events :
  forall x y : event, {x = y} + {x <> y}.
Proof.
do 2 (decide equality; eauto using eq_dec_labels, eq_nat_dec, Ident.eq_dec).
Qed. 
