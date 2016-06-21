
(******************************************************************************)
(** * Definition of graph events *)
(******************************************************************************)

Require Import Vbase.

Require Import Basic Event.

Set Implicit Arguments.

(** * Labels *)

Inductive label := 
(*  | Askip*)
  | Aload   (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | Astore  (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | Arfence (ord:Ordering.t)
  | Awfence (ord:Ordering.t).

Definition loc_lab a :=
  match a with
(*  | Askip  => None*)
  | Aload  l _ _
  | Astore l _ _ => Some l
  | Arfence _ 
  | Awfence _ => None
  end.

Definition val_lab a :=
  match a with
(*  | Askip  => None*)
  | Aload  _ v _
  | Astore _ v _ => Some v
  | Arfence _ 
  | Awfence _ => None
  end.

Definition ord_lab a :=
  match a with
(*  | Askip  => None*)
  | Aload  _ _ o
  | Astore _ _ o
  | Arfence o 
  | Awfence o => o
  end.

Definition is_read_lab a :=
  match a with
    | Aload _ _ _ => True
    | _ => False
  end.

Definition is_write_lab a :=
  match a with
    | Astore  _ _ _ => True
    | _ => False
  end.

Definition is_wfence_lab a :=
  match a with
    | Awfence _ => True
    | _ => False
  end.

Definition is_rfence_lab a :=
  match a with
    | Arfence _ => True
    | _ => False
  end.

Definition is_rlx_lab a :Prop := Ordering.le Ordering.relaxed (ord_lab a).
Definition is_ra_lab a :Prop := Ordering.le Ordering.acqrel (ord_lab a).
Definition is_sc_lab a :Prop := Ordering.le Ordering.seqcst (ord_lab a).

(** * Events *)
Definition act_id := nat.
Definition thread_id := IdentMap.key.

Inductive event := 
  | Event (id: act_id) (tid: thread_id) (lab:label).

Definition thread a :=
  match a with
  | Event _ tid _ => tid
  end.

Definition lab a :=
  match a with
  | Event _ _ lab => lab
  end.

Definition loc a := loc_lab (lab a).
Definition val a := val_lab (lab a).
Definition ord a := ord_lab (lab a).
Definition is_read a := is_read_lab (lab a).
Definition is_write a := is_write_lab (lab a).
Definition is_wfence a := is_wfence_lab (lab a).
Definition is_rfence a := is_rfence_lab (lab a).
Definition is_rlx a :Prop := is_rlx_lab (lab a).
Definition is_ra a :Prop := is_ra_lab (lab a).
Definition is_sc a :Prop := is_sc_lab (lab a).

(** * Basic Lemmas *)

Lemma write_non_read a (A: is_write a) : ~ is_read a.
Proof.
unfold is_write, is_read in *.
destruct a; destruct lab0; ins; eexists; desf; eauto.
Qed.

Lemma wfence_non_read a (A: is_wfence a) : ~ is_read a.
Proof.
unfold is_wfence, is_read in *.
destruct a; destruct lab0; ins; eexists; desf; eauto.
Qed.

Lemma write_has_location a (WRITE: is_write a) : exists x, loc a = Some x.
Proof.
destruct a; destruct lab0; ins; eexists; desf; eauto.
Qed.

Lemma ra_is_rlx a (RA: is_ra a) : is_rlx a.
Proof.
destruct a; destruct lab0; ins; desf;  destruct ord0; ins; desf.
Qed.

Lemma sc_is_rlx a (SC: is_sc a) : is_rlx a.
Proof.
destruct a; destruct lab0; ins; desf;  destruct ord0; ins; desf.
Qed.

Lemma sc_is_ra a (SC: is_sc a) : is_ra a.
Proof.
destruct a; destruct lab0; ins; desf;  destruct ord0; ins; desf.
Qed.

Hint Resolve  write_non_read wfence_non_read ra_is_rlx sc_is_rlx sc_is_ra : acts.

(*
Definition is_access a :=
  match a with
    | Aload _ _ _ _ | Astore _ _ _ _ | Armw _ _ _ _ _  => true
    | Askip _ => false
  end.

(** A read is either a load or a read-modify-write action. *)

Definition is_read a :=
  match a with
    | Aload _ _ _ _ | Armw _ _ _ _ _  => true
    | _ => false
  end.

Definition is_readL a l :=
  match a with
    | Aload _ _ l' _
    | Armw _ _ l' _ _ => l' = l
    | _ => False
  end.

Definition is_readLV a l v :=
  match a with
    | Aload _ _ l' v' 
    | Armw _ _ l' v' _ => l' = l /\ v' = v
    | _ => False
  end.

Definition is_read_only a :=
  match a with
    | Askip _ => false
    | Aload _ _ _ _ => true
    | Armw _ _ _ _ _ => false
    | Astore _ _ _ _ => false
  end.

(** A write is either a store or a read-modify-write action. *)

Definition is_write a :=
  match a with
    | Astore _ _ _ _ | Armw _ _ _ _ _ => true
    | _ => false
  end.

Definition is_writeL a l :=
  match a with
    | Astore _ _ l' _ 
    | Armw _ _ l' _ _ => l' = l
    | _ => False
  end.

Definition is_writeLV a l v :=
  match a with
    | Astore _ _ l' v' 
    | Armw _ _ l' _ v' => l' = l /\ v' = v
    | _ => False
  end.

Definition is_write_only a :=
    match a with
    | Askip _       => false
    | Aload _ _ _ _ => false
    | Armw _ _ _ _ _ => false
    | Astore _ _ _ _ => true
  end.

Definition is_rmw a :=
  match a with
    | Armw _ _ _ _ _ => true
    | _ => false
  end.

Lemma is_rmwE a : is_rmw a <-> is_read a /\ is_write a.
Proof. destruct a; ins; intuition. Qed.

  
(** Acquire actions have memory order [acq] or stronger. *)
 
Definition is_acquire_rtyp t :=
   match t with RATacq => true end.

Definition is_acquire_utyp t :=
   match t with UATrel_acq => true end.

Definition is_acquire a :=
  match a with
    | Aload _ typ _ _ => is_acquire_rtyp typ
    | Armw  _ typ _ _ _ => is_acquire_utyp typ
    | _ => false
  end.

(** Release actions have memory order [rel] or stronger. *)

Definition is_release_wtyp t :=
   match t with WATrel => true end.

Definition is_release_utyp t :=
   match t with | UATrel_acq => true end.

Definition is_release_write a :=
  match a with
    | Astore _ typ _ _ => is_release_wtyp typ 
    | Armw   _ typ _ _ _ => is_release_utyp typ
    | _ => false
  end.


(******************************************************************************)
(** ** Lemmas about access types *)
(******************************************************************************)

Lemma is_readLV_rmw_writeL a l v : is_readLV a l v -> is_rmw a -> is_writeL a l.
Proof. by destruct a; ins; desf. Qed.

Lemma is_readL_rmw_writeL a l : is_readL a l -> is_rmw a -> is_writeL a l.
Proof. by destruct a; ins; desf. Qed.

Lemma is_writeLV_writeL a l v : is_writeLV a l v -> is_writeL a l.
Proof. by destruct a; ins; desf. Qed.

(** Lemmas deriving [is_readL]. *)

Lemma is_writeLV_rmw_readL a l v : is_writeLV a l v -> is_rmw a -> is_readL a l.
Proof. by destruct a; ins; desf. Qed.

Lemma is_writeL_rmw_readL a l : is_writeL a l -> is_rmw a -> is_readL a l.
Proof. by destruct a; ins; desf. Qed.

Lemma is_readLV_readL a l v : is_readLV a l v -> is_readL a l.
Proof. by destruct a; ins; desf. Qed.

(** Lemmas deriving [is_write]. *)

Lemma is_rmw_write : 
  forall a, is_rmw a -> is_write a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_writeLV_write : 
  forall a l v, is_writeLV a l v -> is_write a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_writeL_write : 
  forall a l, is_writeL a l -> is_write a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_release_write_write : 
  forall a, is_release_write a -> is_write a.
Proof. by destruct a; ins; desf. Qed.

(** Lemmas deriving [is_read]. *)

Lemma is_rmw_read : 
  forall a, is_rmw a -> is_read a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_readLV_read : 
  forall a l v, is_readLV a l v -> is_read a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_readL_read : 
  forall a l, is_readL a l -> is_read a.
Proof. by destruct a; ins; desf. Qed.

Lemma is_readL_loc : forall x l, is_readL x l ->
                                 loc x = l.
Proof. by destruct x; ins; desf. Qed.

Lemma is_writeL_loc : forall x l, is_writeL x l ->
                                  loc x = l.
Proof. by destruct x; ins; desf. Qed.

Lemma is_readLV_loc : forall x l v, is_readLV x l v ->
                                    loc x = l.
Proof. by destruct x; ins; desf. Qed.
      
Lemma is_writeLV_loc : forall x l v, is_writeLV x l v ->
                                     loc x = l.
Proof. by destruct x; ins; desf. Qed.


Lemma is_write_write_only : forall x, is_write_only x = true ->
                                      is_write x = true.
Proof.
  ins; destruct x; simpl in *; auto.
Qed.

Lemma is_read_read_only : forall x, is_read_only x = true ->
                                      is_read x = true.
Proof.
  ins; destruct x; simpl in *; auto.
Qed.
  
Hint Resolve
  is_writeLV_writeL    is_readLV_readL
  is_writeL_write      is_writeLV_write    is_rmw_write
  is_readL_read        is_readLV_read      is_rmw_read
  is_readL_loc is_writeL_loc
  is_readLV_loc is_writeLV_loc : caccess.


Lemma is_write_access a : is_write a -> is_access a.
Proof. by destruct a. Qed.

Lemma is_read_access a : is_read a -> is_access a.
Proof. by destruct a. Qed.

Lemma is_writeL_access a l : is_writeL a l -> is_access a.
Proof. by destruct a. Qed.

Lemma is_readL_access a l : is_readL a l -> is_access a.
Proof. by destruct a. Qed.

Lemma is_readLV_access a l v : is_readLV a l v -> is_access a.
Proof. by destruct a. Qed.

Hint Resolve is_read_access is_readL_access is_readLV_access
             is_write_access is_writeL_access : caccess.

Lemma is_read_only_access a : is_read_only a -> is_access a.
Proof. by destruct a. Qed.

Lemma is_write_only_access a : is_write_only a -> is_access a.
Proof. by destruct a. Qed.

Lemma is_read_only_read a : is_read_only a -> is_read a.
Proof. by destruct a. Qed.

Lemma is_write_only_write a : is_write_only a -> is_write a.
Proof. by destruct a. Qed.

Hint Resolve is_read_only_read is_read_only_access
     is_write_only_write is_write_only_access : caccess.


*)