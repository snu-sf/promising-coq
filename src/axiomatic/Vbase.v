
(* *********************************************************************)
(*                                                                     *)
(*                      Basic lemmas & tactics                         *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics for better
    proof automation, structuring large proofs, or rewriting.  Most of 
    the rewriting support is ported from ss-reflect. *)

(** Symbols starting with [vlib__] are internal. *)

Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.

Open Scope bool_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ************************************************************************** *)
(** * Axioms *)
(* ************************************************************************** *)

Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Ltac exten := apply functional_extensionality.

(* ************************************************************************** *)
(** * Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma vlib__true_is_true : true.
Proof. reflexivity. Qed.

Lemma vlib__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Hint Resolve vlib__true_is_true vlib__not_false_is_true.

(* ************************************************************************** *)
(** * Very basic automation *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb vlib discriminated. 

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac vlib__basic_done := 
  solve [trivial with vlib | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial with vlib; hnf; intros;
  solve [try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split;
         try eassumption; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).


(* ************************************************************************** *)
(** * Boolean reflection *)
(* ************************************************************************** *)

(** These definitions are ported from ssr-bool. *)

(** Negation lemmas *)
Section NegationLemmas.

  Variables (b c : bool).

  Lemma negbT : b = false -> negb b.
  Proof. by case b. Qed.
  Lemma negbTE: negb b -> b = false.
  Proof. by case b. Qed.
  Lemma negbF : b -> negb b = false.
  Proof. by case b. Qed.
  Lemma negbFE: negb b = false -> b.
  Proof. by case b. Qed.
  Lemma negbNE: negb (negb b) -> b.
  Proof. by case b. Qed.

  Lemma negbLR : b = negb c -> negb b = c.
  Proof. by case c; intro X; rewrite X. Qed.

  Lemma negbRL : negb b = c -> b = negb c.
  Proof. by case b; intro X; rewrite <- X. Qed.

  Lemma contra : (c -> b) -> negb b -> negb c.
  Proof. by case b; case c. Qed.

End NegationLemmas.

(** Lemmas for ifs, which allow reasoning about the condition without 
    repeating it inside the proof. *)
Section BoolIf.

Variables (A B : Type) (x : A) (f : A -> B) (b : bool) (vT vF : A).

Inductive if_spec : A -> bool -> Set :=
  | IfSpecTrue  : b         -> if_spec vT true
  | IfSpecFalse : b = false -> if_spec vF false.

Lemma ifP : if_spec (if b then vT else vF) b.
Proof. by case_eq b; constructor. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if negb b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg : forall fT fF : A -> B,
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

End BoolIf.

(** The reflection predicate *)
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

(** Internal reflection lemmas *)
Section ReflectCore.

Variables (P : Prop) (b : bool) (Hb : reflect P b) (Q : Prop) (c : bool).

Lemma introNTF : (if c then ~ P else P) -> negb b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : negb b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. by case Hb; auto. Qed.

Lemma xorPif : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. by case Hb; [intros ? _ H ? | intros ? H _]; case H. Qed.

End ReflectCore.

(** Internal negated reflection lemmas *)
Section ReflectNegCore.

Variables (P : Prop) (b : bool) (Hb : reflect P (negb b)) (Q : Prop) (c : bool).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by intro X; apply (introNTF Hb) in X; rewrite <- X; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; apply (elimNTF Hb); case b. Qed.

Lemma equivPifn : (Q -> P) -> (P -> Q) -> if b then ~ Q else Q.
Proof. by rewrite <- if_neg; apply equivPif. Qed.

Lemma xorPifn : Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q.
Proof. by rewrite <- if_neg; apply xorPif. Qed.

End ReflectNegCore.

(** User-oriented reflection lemmas *)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Pb : reflect P b) (Pb' : reflect P (negb b')).

Lemma introT  : P -> b.
Proof. by apply (introTF Pb (c:=true)). Qed.
Lemma introF  : ~ P -> b = false.
Proof. by apply (introTF Pb (c:=false)). Qed.
Lemma introN  : ~ P -> negb b.
Proof. by apply (introNTF Pb (c:=true)). Qed.
Lemma introNf : P -> negb b = false.
Proof. by apply (introNTF Pb (c:=false)). Qed.
Lemma introTn : ~ P -> b'.
Proof. by apply (introTFn Pb' (c:=true)). Qed.
Lemma introFn : P -> b' = false.
Proof. by apply (introTFn Pb' (c:=false)). Qed.

Lemma elimT  : b -> P.
Proof. by apply (@elimTF _ _ Pb true). Qed.
Lemma elimF  : b = false -> ~ P.
Proof. by apply (@elimTF  _ _ Pb false). Qed.
Lemma elimN  : negb b -> ~P.
Proof. by apply (@elimNTF _ _ Pb true). Qed.
Lemma elimNf : negb b = false -> P.
Proof. by apply (@elimNTF _ _ Pb false). Qed.
Lemma elimTn : b' -> ~ P.
Proof. by apply (@elimTFn _ _ Pb' true). Qed.
Lemma elimFn : b' = false -> P.
Proof. by apply (@elimTFn _ _ Pb' false). Qed.

Lemma introP : (b -> Q) -> (negb b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case Pb; constructor; auto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by intro Qb; intro X; apply introT in X; revert X; case Qb. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. intro X; case X; [exact introT | exact introF]. Qed.

Lemma decPcases : if b then P else ~ P.
Proof. by case Pb. Qed.

Definition decP : {P} + {~ P}.
Proof. by generalize decPcases; case b; [left | right]. Defined.

End Reflect.

(* Allow the direct application of a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Qed.

Lemma idPn : reflect (negb b1) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (negb b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (negb (negb b1)).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor; try done; intro X; case X. Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; intro X; case X. Qed.

Lemma nandP : reflect (negb b1 \/ negb b2) (negb (b1 && b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

Lemma norP : reflect (negb b1 /\ negb b2) (negb (b1 || b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

End ReflectConnectives.

(* ************************************************************************** *)
(** * Equality types *)
(* ************************************************************************** *)

(** These definitions are ported from ssr-eq. *)

Inductive phantom (T :  Type) (p : T) :  Type := Phantom.
Implicit Arguments phantom [].
Implicit Arguments Phantom [].
Definition phant_id T1 T2 v1 v2 := phantom T1 v1 -> phantom T2 v2.
Definition idfun T := (fun x : T => x).

Module Equality.

Definition axiom T (e : T -> T -> bool) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : T -> T -> bool; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class cT' := match cT' return class_of cT' with @Pack _ c _ => c end.

Definition pack c := @Pack T c T.
Definition clone := fun c (_ : cT -> T) (_ : phant_id (pack c) cT) => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation eqType := type.
Notation EqMixin := Mixin.
Notation EqType T m := (@pack T m).
Notation "[ 'eqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T ]") : form_scope.
Notation "[ 'eqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'eqType'  'of'  T ]") : form_scope.
End Exports.

End Equality.
Export Equality.Exports.

Definition eq_op T := Equality.op (Equality.class T).
Implicit Arguments eq_op [[T]].

Lemma eqE : forall T x, eq_op x = Equality.op (Equality.class T) x.
Proof. done. Qed.

Lemma eqP : forall T, Equality.axiom (@eq_op T).
Proof. by unfold eq_op; destruct T as (? & []). Qed.
Implicit Arguments eqP [T].

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (negb (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (negb (x == y :> T))
  (at level 70, y at next level) : bool_scope.

Lemma vlib__internal_eqP : 
  forall (T: eqType) (x y : T), reflect (x = y) (x == y).
Proof. apply eqP. Qed.

Lemma neqP : forall (T: eqType) (x y: T), reflect (x <> y) (x != y).
Proof. intros; case eqP; constructor; auto. Qed.

Lemma beq_refl : forall (T : eqType) (x : T), x == x.
Proof. by intros; case eqP. Qed.

Lemma beq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Proof. intros; do 2 case eqP; congruence. Qed.

Hint Resolve beq_refl : vlib.
Hint Rewrite beq_refl : vlib_trivial.

Notation eqxx := beq_refl.


(* ************************************************************************** *)
(** * Basic simplification tactics *)
(* ************************************************************************** *)


Lemma vlib__negb_rewrite : forall b, negb b -> b = false.
Proof. by intros []. Qed.

Lemma vlib__andb_split : forall b1 b2, b1 && b2 -> b1 /\ b2.
Proof. by intros [] []. Qed.

Lemma vlib__nandb_split : forall b1 b2, b1 && b2 = false -> b1 = false \/ b2 = false.
Proof. intros [] []; auto. Qed. 

Lemma vlib__orb_split : forall b1 b2, b1 || b2 -> b1 \/ b2.
Proof. intros [] []; auto. Qed.

Lemma vlib__norb_split : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma vlib__eqb_split : forall b1 b2 : bool, (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. intros [] [] H H'; unfold is_true in *; auto using sym_eq. Qed.

Lemma vlib__beq_rewrite : forall (T : eqType) (x1 x2 : T), x1 == x2 -> x1 = x2.
Proof. by intros until 0; case eqP. Qed.


(** Set up for basic simplification: database of reflection lemmas *)

Create HintDb vlib_refl discriminated.  

Hint Resolve andP orP nandP norP negP vlib__internal_eqP neqP : vlib_refl.

Ltac vlib__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (*  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);  
      (* Previous statement no longer necessary in 8.4 *) *)
  clear H; intros; subst X;
  try subst.

Ltac vlib__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => 
      let H' := fresh H in case (vlib__andb_split H); clear H; intros H' H
  | [H: is_true (negb ?x) |- _] => rewrite (vlib__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: is_true (_ == _)  |- _] => generalize (vlib__beq_rewrite H); clear H; intro H
  | [H: @existT _ _ _ _ = @existT _ _ _ _ |- _] => apply inj_pair2 in H; try subst
  | [H: ?f _             = ?f _             |- _] => vlib__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => vlib__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end; (* autorewrite with vlib_trivial; *) try done.

(** Kill simple goals that require up to two econstructor calls. *)

Ltac vauto :=
  (clarify; try edone;
   try [> econstructor; (solve [edone | [> econstructor; edone]])]).

(** Check that the hypothesis [id] is defined. This is useful to make sure that
    an [assert] has been completely finished. *)
    
Ltac end_assert id := 
  let m := fresh in 
  pose (m := refl_equal id); clear m.

Ltac inv x := inversion x; clarify.
Ltac simpls  := simpl in *; try done.
Ltac ins := simpl in *; try done; intros.

Tactic Notation "case_eq" constr(x) := case_eq (x).

Tactic Notation "case_eq" constr(x) "as" simple_intropattern(H) :=
  destruct x as [] _eqn: H; try done.

Ltac vlib__clarsimp1 :=
  clarify; (autorewrite with vlib_trivial vlib in * ); 
  (autorewrite with vlib_trivial in * ); try done;
  clarify; auto 1 with vlib.

Ltac clarsimp := intros; simpl in *; vlib__clarsimp1.

Ltac autos   := clarsimp; auto with vlib.


(* ************************************************************************** *)
(** Destruct but give useful names *)
(* ************************************************************************** *)

Definition  NW (P: unit -> Prop) : Prop := P tt.

Notation "<< x : t >>" := (NW (fun x => t)) (at level 80, x ident, no associativity).
Notation "<< t >>" := (NW (fun _ => t)) (at level 79, no associativity).

Ltac unnw := unfold NW in *.
Ltac rednw := red; unnw.

Hint Unfold NW.

(** Destruct, but no case split *)
Ltac desc :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : is_true (_ && _) |- _ => 
          let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
          let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x   |- _ => clear H

(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with vlib_refl]]  *)
  end.

Ltac des :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : is_true (_ && _) |- _ => 
        let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
        let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x |- _ => clear H
(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with vlib_refl]] *)
    | H : ?p <-> ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => unfold NW at 1 in x'; red in y' | _ => idtac end;
      match q with | NW _ => unfold NW at 1 in y'; red in x' | _ => idtac end
    | H : ?p \/ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y'];
      [ match p with | NW _ => red in x' | _ => idtac end
      | match q with | NW _ => red in y' | _ => idtac end]
    | H : is_true (_ || _) |- _ => case (vlib__orb_split H); clear H; intro H
    | H : (_ && _) = false |- _ => case (vlib__nandb_split H); clear H; intro H
  end.

Ltac des_if_asm :=
  clarify;
  repeat 
    match goal with 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_if_goal :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_if :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_eqrefl :=
  match goal with
    | H: context[match ?X with _ => _ end Logic.eq_refl] |- _ =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    revert H;
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'; intros H
    | |- context[match ?X with _ => _ end Logic.eq_refl] =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'
  end.

Ltac desf_asm := clarify; des; des_if_asm.

Ltac desf := clarify; des; des_if.

Ltac clarassoc := clarsimp; autorewrite with vlib_trivial vlib vlibA in *; try done. 

Ltac vlib__hacksimp1 :=
   clarsimp;
   match goal with
     | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                         |rewrite <- H; clear H; clarsimp]
     | _ => solve [f_equal; clarsimp]
   end.

Ltac hacksimp :=
   clarsimp;
   try match goal with
   | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                              |rewrite <- H; clear H; clarsimp]
   | |- context[match ?p with _ => _ end] => solve [destruct p; vlib__hacksimp1]
   | _ => solve [f_equal; clarsimp]
   end.

(* ************************************************************************** *)
(** ** Delineating cases in proofs *)
(* ************************************************************************** *)

(** Named case tactics (taken from Libtactics) *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** Lightweight case tactics (without names) *)

Tactic Notation "--" tactic(c) :=
  first [
    assert (WithinCaseM := True); move WithinCaseM at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "++" tactic(c) :=
  first [
    assert (WithinCaseP := True); move WithinCaseP at top
  | fail 1 "because we are working on a different case." ]; c.

(* ************************************************************************** *)
(** ** Exploiting a hypothesis *)
(* ************************************************************************** *)

(** Exploit an assumption (adapted from CompCert). *)

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).

(* ************************************************************************** *)
(** * Induction *)
(* ************************************************************************** *)

Tactic Notation "induction" "[" ident_list(y) "]" ident(x)  :=
  first [ try (intros until x); revert y; induction x
        | red; try (intros until x); revert y; induction x ].

Tactic Notation "induction" "[" ident_list(y) "]" ident(x) "[" ident(z) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z
        | red; try (intros until x); revert y; induction x; destruct z ].

Tactic Notation "induction" "[" ident_list(y) "]" ident(x) "[" ident(z) ident (w) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z, w
        | red; try (intros until x); revert y; induction x; destruct z, w ].

(** Versions with hacksimp *)

Tactic Notation "induct" ident(x) := induction x; hacksimp.

Tactic Notation "induct" ident(x) "[" ident(z) "]" := 
  induction x; destruct z; hacksimp.

Tactic Notation "induct" ident(x) "[" ident(z) ident(w) "]" := 
  induction x; destruct z, w; hacksimp.

Tactic Notation "induct" "[" ident_list(y) "]" ident(x)  :=
  first [ try (intros until x); revert y; induction x; hacksimp
        | red; try (intros until x); revert y; induction x; hacksimp ].

Tactic Notation "induct" "[" ident_list(y) "]" ident(x) "[" ident(z) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z; hacksimp
        | red; try (intros until x); revert y; induction x; destruct z; hacksimp ].

Tactic Notation "induct" "[" ident_list(y) "]" ident(x) "[" ident(z) ident(w) "]"  :=
  first [ try (intros until x); revert y; induction x; destruct z, w; hacksimp
        | red; try (intros until x); revert y; induction x; destruct z, w; hacksimp ].


(* ************************************************************************** *)
(** * Views *)
(* ************************************************************************** *)

Ltac vlib__apply_refl :=
  intros;
    match goal with 
      | |- is_true ?p => eapply introT; [solve [trivial with vlib_refl]|]
      | |- ?p = true => eapply introT; [solve [trivial with vlib_refl]|]
      | |- ?p = false => eapply introFn; [solve [trivial with vlib_refl]|]
      | |- ?p = false => eapply introF; [solve [trivial with vlib_refl]|]
      | |- _ => red; vlib__apply_refl
    end. 

Tactic Notation "apply/" := vlib__apply_refl.

Tactic Notation "apply/" constr(X) :=
  first [eapply X | eapply elimT; [eapply X; edone|]
    | eapply introT; [eapply X; edone|]
    | eapply introFn; [eapply X; edone|]
    | eapply introF; [eapply X; edone|]].

Tactic Notation "split/" := 
  first [split | hnf; intros; apply/ ; split
        | try red; intros; apply vlib__eqb_split].

(** apply in assumption *)

Ltac vlib__apply_refl_in H :=
  first [eapply elimT in H; [|solve [trivial with vlib_refl]]
        |eapply elimFn in H; [|solve [trivial with vlib_refl]]
        |eapply elimF in H; [|solve [trivial with vlib_refl]]].

Ltac vlib__apply_with_in X H :=
  first [eapply X in H
        |eapply elimT in H; [|eapply X; edone]
        |eapply elimFn in H; [|eapply X; edone]
        |eapply elimF in H; [|eapply X; edone]].

Tactic Notation "apply/" "in" hyp(H) := vlib__apply_refl_in H.

Tactic Notation "apply/" constr(X) "in" hyp(H) := vlib__apply_with_in X H.

(** double apply *)

Tactic Notation "apply/" constr(X1) "/" constr(X2) :=
  eapply sameP; [apply X1; edone|eapply iffP; [apply X2; edone|instantiate|instantiate]].


(* ************************************************************************** *)
(** * Function notation ported from ssrfun.v *)
(* ************************************************************************** *)

Delimit Scope fun_scope with FUN.
Open Scope fun_scope.

Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y") : fun_scope.

Module Option.

Definition apply aT rT (f : aT -> rT) x u := 
  match u with
    | Some y => f y 
    | None => x
  end.

Definition default T := apply (fun x : T => x).

Definition bind aT rT (f : aT -> option rT) := apply f None.

Definition map aT rT (f : aT -> rT) := bind (fun x => Some (f x)).

End Option.

Notation oapp := Option.apply.
Notation odflt := Option.default.
Notation obind := Option.bind.
Notation omap := Option.map.
Notation some := (@Some _) (only parsing).

(** Definitions and notation for explicit functions with simplification. *)

Section SimplFun.

Variables aT rT : Type.

Inductive simpl_fun : Type := SimplFun (_ : aT -> rT).

Definition fun_of_simpl := fun f x => match f with SimplFun lam => lam x end. 

Coercion fun_of_simpl : simpl_fun >-> Funclass.

End SimplFun.


Notation "[ 'fun' : T => E ]" := (SimplFun (fun _ : T => E))
  (at level 0,
   format "'[hv' [ 'fun' :  T  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x => E ]" := (SimplFun (fun x => E))
  (at level 0, x ident,
   format "'[hv' [ 'fun'  x  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x : T => E ]" := (SimplFun (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fun' x y => E ]" := (fun x => [fun y => E])
  (at level 0, x ident, y ident,
   format "'[hv' [ 'fun'  x  y  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x y : T => E ]" := (fun x : T => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : T ) y => E ]" := (fun x : T => [fun y => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' x ( y : T ) => E ]" := (fun x => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : xT ) ( y : yT ) => E ]" :=
    (fun x : xT => [fun y : yT => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Definition erefl := @eq_refl.
Definition esym := eq_sym.
Definition nesym := sym_not_eq.
Definition etrans := eq_trans.
Definition congr1 := f_equal.
Definition congr2 := f_equal2.

(** A predicate for singleton types. *)
Definition all_equal_to T (x0 : T) := forall x, x = x0.

Lemma unitE : all_equal_to tt.
Proof. by intros []. Qed.

(** A generic wrapper type *)

Structure wrapped T := Wrap {unwrap : T}.
Canonical Structure wrap T x := @Wrap T x.

(* Prenex Implicits unwrap wrap Wrap. *)

(** Extensional equality for unary and binary functions + syntactic sugar. *)

Section ExtensionalEquality.

Variables A B C : Type.

Definition eqfun (f g : B -> A) : Prop := forall x, f x = g x.

Definition eqrel (r s : C -> B -> A) : Prop := forall x y, r x y = s x y.

Lemma frefl : forall f, eqfun f f.
Proof. done. Qed.

Lemma fsym : forall f g, eqfun f g -> eqfun g f.
Proof. red; done. Qed. 

Lemma ftrans : forall f g h (EQ1: eqfun f g) (EQ2: eqfun g h), eqfun f h.
Proof. by red; intros; rewrite EQ1. Qed.

Lemma rrefl : forall r, eqrel r r.
Proof. done. Qed.

End ExtensionalEquality.

Hint Resolve frefl rrefl.

Notation "f1 =1 f2" := (eqfun f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =1 f2 :> A" := (f1 =1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.
Notation "f1 =2 f2" := (eqrel f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =2 f2 :> A" := (f1 =2 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.

Section Composition.

Variables A B C : Type.

Definition funcomp u (f : B -> A) (g : C -> B) x := match u with tt => f (g x) end.
Local Notation comp := (funcomp tt).

Definition pcomp (f : B -> option A) (g : C -> option B) x := obind f (g x).

Lemma eq_comp : forall f f' g g', f =1 f' -> g =1 g' -> comp f g =1 comp f' g'.
Proof. red; intros; simpl; congruence. Qed.

End Composition.

Notation "[ 'eta' f ]" := (fun x => f x)
  (at level 0, format "[ 'eta'  f ]") : fun_scope.

Notation id := (fun x => x).
Notation "@ 'id' T " := (fun x : T => x)
  (at level 10, T at level 8, only parsing) : fun_scope.

Notation comp := (funcomp tt).
Notation "@ 'comp'" := (fun A B C => @funcomp A B C tt).
Notation "f1 \o f2" := (comp f1 f2) (at level 50) : fun_scope.

Section Morphism.

Variables (aT rT sT : Type) (f : aT -> rT).

Definition morphism_1 aF rF := forall x, f (aF x) = rF (f x).
Definition morphism_2 aOp rOp := forall x y, f (aOp x y) = rOp (f x) (f y).

End Morphism.

Notation "{ 'morph' f : x / a >-> r }" :=
  (morphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x / a }" :=
  (morphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a }") : type_scope.

Notation "{ 'morph' f : x y / a >-> r }" :=
  (morphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x y / a }" :=
  (morphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a }") : type_scope.

(* ************************************************************************** *)
(** * Properties of relations (ported from ssrfun.v)  *)
(* ************************************************************************** *)

Section Injections.

(* rT must come first so we can use @ to mitigate the Coq 1st order   *)
(* unification bug (e..g., Coq can't infer rT from a "cancel" lemma). *)
Variables (rT aT : Type) (f : aT -> rT).

Definition injective := forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition cancel g := forall x, g (f x) = x.

Definition pcancel g := forall x, g (f x) = Some x.

Definition ocancel (g : aT -> option rT) h := forall x, oapp h x (g x) = x.

Lemma can_pcan : forall g, cancel g -> pcancel (fun y => Some (g y)).
Proof. by red; intros; f_equal. Qed.

Lemma pcan_inj : forall g, pcancel g -> injective.
Proof. red; intros; apply (congr1 g) in H0; rewrite !H in *; clarify. Qed.

Lemma can_inj : forall g, cancel g -> injective.
Proof. eby intros; apply can_pcan in H; eapply pcan_inj. Qed.

Lemma canLR : forall g x y, cancel g -> x = f y -> g x = y.
Proof. intros; clarify. Qed.

Lemma canRL : forall g x y, cancel g -> f x = y -> x = g y.
Proof. intros; clarify. Qed. 

End Injections.

(* cancellation lemmas for dependent type casts.                             *)
Lemma esymK : forall T x y, cancel (@eq_sym T x y) (@eq_sym T y x).
Proof. by red; destruct x0. Qed.

Lemma etrans_id : forall T x y (eqxy : x = y :> T),
  eq_trans (eq_refl x) eqxy = eqxy.
Proof. by destruct eqxy. Qed.

Section InjectionsTheory.

Variables (A B C : Type) (f g : B -> A) (h : C -> B).

Lemma inj_id : injective (@id A).
Proof. done. Qed.

Lemma inj_can_sym : forall f', cancel f f' -> injective f' -> cancel f' f.
Proof. red; intros; apply H0, H. Qed.

Lemma inj_comp : injective f -> injective h -> injective (f \o h).
Proof. by red; simpl; intros; apply H0, H. Qed.

Lemma can_comp : forall f' h',
  cancel f f' -> cancel h h' -> cancel (f \o h) (h' \o f').
Proof. by red; simpl; intros; rewrite H, H0. Qed.

Lemma pcan_pcomp : forall f' h',
  pcancel f f' -> pcancel h h' -> pcancel (f \o h) (pcomp h' f').
Proof. by red; intros; unfold pcomp; simpl; rewrite H; simpl; rewrite H0. Qed.

Lemma eq_inj : injective f -> f =1 g -> injective g.
Proof. intros H H0 x y; simpl; rewrite <- !H0; apply H. Qed.

Lemma eq_can : forall f' g', cancel f f' -> f =1 g -> f' =1 g' -> cancel g g'.
Proof. by red; intros; rewrite <- H0, <- H1. Qed.

Lemma inj_can_eq : forall f',
  cancel f f' -> injective f' -> cancel g f' -> f =1 g.
Proof. by red; intros; apply H0; rewrite H1. Qed.

End InjectionsTheory.

Section Bijections.

Variables (A B : Type) (f : B -> A).

Inductive bijective : Prop := Bijective g (_ : cancel f g) (_ : cancel g f).

Hypothesis bijf : bijective.

Lemma bij_inj : injective f.
Proof. eby destruct bijf; eapply can_inj. Qed.

Lemma bij_can_sym : forall f', cancel f' f <-> cancel f f'.
Proof.
split; intros; [by apply inj_can_sym, bij_inj|].
by destruct bijf; intros x; rewrite <- (H1 x), H.
Qed.

Lemma bij_can_eq : forall f' f'', cancel f f' -> cancel f f'' -> f' =1 f''.
Proof.
  by intros; eapply inj_can_eq, bij_can_sym; [apply bij_can_sym | apply bij_inj |].
Qed.

End Bijections.

Section BijectionsTheory.

Variables (A B C : Type) (f : B -> A) (h : C -> B).

Lemma eq_bij : bijective f -> forall g, f =1 g -> bijective g.
Proof. by destruct 1; exists g; eapply eq_can; eauto. Qed.

Lemma bij_comp : bijective f -> bijective h -> bijective (f \o h).
Proof.
intros [f' fK f'K] [h' hK h'K].
by exists (h' \o f' : _ -> _); apply can_comp; auto.
Qed.

Lemma bij_can_bij : bijective f -> forall f', cancel f f' -> bijective f'.
Proof. by exists f; [apply (bij_can_sym H) |]. Qed.

End BijectionsTheory.

Section Involutions.

Variables (A : Type) (f : A -> A).

Definition involutive := cancel f f.

Hypothesis Hf : involutive.

Lemma inv_inj : injective f.
Proof. eapply can_inj, Hf. Qed.

Lemma inv_bij : bijective f.
Proof. by exists f. Qed.

End Involutions.


Section OperationProperties.

Variables S T R : Type.

Section SopTisR.
Implicit Type op : S -> T -> R.
Definition left_inverse e inv op := forall x, op (inv x) x = e.
Definition right_inverse e inv op := forall x, op x (inv x) = e.
End SopTisR.

Section SopTisS.
Implicit Type op : S -> T -> S.
Definition right_id e op := forall x, op x e = x.
Definition left_zero z op := forall x, op z x = z.
Definition right_commutative op := forall x y z, op (op x y) z = op (op x z) y.
Definition left_distributive op add :=
  forall x y z, op (add x y) z = add (op x z) (op y z).
End SopTisS.

Section SopTisT.
Implicit Type op : S -> T -> T.
Definition left_id e op := forall x, op e x = x.
Definition right_zero z op := forall x, op x z = z.
Definition left_commutative op := forall x y z, op x (op y z) = op y (op x z).
Definition right_distributive op add :=
  forall x y z, op x (add y z) = add (op x y) (op x z).
End SopTisT.

Section SopSisT.
Implicit Type op : S -> S -> T.
Definition self_inverse e op := forall x, op x x = e.
Definition commutative op := forall x y, op x y = op y x.
End SopSisT.

Section SopSisS.
Implicit Type op : S -> S -> S.
Definition idempotent op := forall x, op x x = x.
Definition associative op := forall x y z, op x (op y z) = op (op x y) z.
End SopSisS.

End OperationProperties.


(** ** Boolean laws *)

(** Shorter, more systematic names for the boolean connectives laws. *)

Lemma andTb : forall x, true && x = x.
Proof. done. Qed.
Lemma andFb : forall x, false && x = false.
Proof. done. Qed.
Lemma andbT : forall x, x && true = x.
Proof. by intros []. Qed.
Lemma andbF : forall x, x && false = false.
Proof. by intros []. Qed.
Lemma andbb : forall x, x && x = x.
Proof. by intros []. Qed.

Lemma andbC : forall x y, x && y = y && x.
Proof. by intros[][]. Qed.
Lemma andbA : forall x y z, x && (y && z) = x && y && z.
Proof. by intros[][][]. Qed.
Lemma andbCA : forall x y z, x && (y && z) = y && (x && z).
Proof. by intros[][][]. Qed.
Lemma andbAC : forall x y z, x && y && z = x && z && y.
Proof. by intros[][][]. Qed.

Lemma andbN : forall b, b && negb b = false.
Proof. by intros[]. Qed.
Lemma andNb : forall b, negb b && b = false.
Proof. by intros[]. Qed.

Lemma orTb : forall x, true || x = true.
Proof. done. Qed.
Lemma orFb : forall x, false || x = x.
Proof. done. Qed.
Lemma orbT : forall x, x || true = true.
Proof. by intros[]. Qed.
Lemma orbF : forall x, x || false = x.
Proof. by intros[]. Qed.
Lemma orbb : forall x, x || x = x.
Proof. by intros[]. Qed.

Lemma orbC : forall x y, x || y = y || x.
Proof. by intros[][]. Qed.
Lemma orbA : forall x y z, x || (y || z) = x || y || z.
Proof. by intros[][][]. Qed. 
Lemma orbCA : forall x y z, x || (y || z) = y || (x || z).
Proof. by intros[][][]. Qed.
Lemma orbAC : forall x y z, x || y || z = x || z || y.
Proof. by intros[][][]. Qed.

Lemma orbN : forall b, b || negb b = true.
Proof. by intros[]. Qed.
Lemma orNb : forall b, negb b || b = true.
Proof. by intros[]. Qed.

Lemma andb_orl : forall x y z, (x || y) && z = x && z || y && z.
Proof. by intros[][][]. Qed.
Lemma andb_orr : forall x y z, x && (y || z) = x && y || x && z.
Proof. by intros[][][]. Qed.
Lemma orb_andl : forall x y z, (x && y) || z = (x || z) && (y || z).
Proof. by intros[][][]. Qed.
Lemma orb_andr : forall x y z, x || (y && z) = (x || y) && (x || z).
Proof. by intros[][][]. Qed.

(** Pseudo-cancellation -- i.e, absorbtion *)

Lemma andbK : forall b1 b2, b1 && b2 || b1 = b1.
Proof. by intros[][]. Qed.
Lemma andKb : forall b1 b2, b1 || b2 && b1 = b1.
Proof. by intros[][]. Qed.
Lemma orbK : forall b1 b2, (b1 || b2) && b1 = b1.
Proof. by intros[][]. Qed.
Lemma orKb : forall b1 b2, b1 && (b2 || b1) = b1.
Proof. by intros[][]. Qed.

(** Exclusive or -- [xorb] *)

Lemma xorFb : forall x, xorb false x = x.
Proof. by intros[]. Qed.
Lemma xorbF : forall x, xorb x false = x.
Proof. by intros[]. Qed.
Lemma xorTb : forall x, xorb true x = negb x.
Proof. by intros[]. Qed.
Lemma xorbT : forall x, xorb x true = negb x.
Proof. by intros[]. Qed.
Lemma xorbb : forall x, xorb x x = false.
Proof. by intros[]. Qed.

Lemma xorbC : forall x y, xorb x y = xorb y x.
Proof. by intros[][]. Qed.
Lemma xorbA : forall x y z, xorb x (xorb y z) = xorb (xorb x y) z.
Proof. by intros[][][]. Qed. 
Lemma xorbCA : forall x y z, xorb x (xorb y z) = xorb y (xorb x z).
Proof. by intros[][][]. Qed. 
Lemma xorbAC : forall x y z, xorb (xorb x y) z = xorb (xorb x z) y.
Proof. by intros[][][]. Qed. 

Lemma xorbN : forall x y, xorb x (negb y) = negb (xorb x y).
Proof. by intros[][]. Qed.
Lemma xorNb : forall x y, xorb x (negb y) = negb (xorb x y).
Proof. by intros[][]. Qed.

Lemma andb_xorl : forall x y z, (xorb x y) && z = xorb (x && z) (y && z).
Proof. by intros[][][]. Qed. 
Lemma andb_xorr : forall x y z, x && (xorb y z) = xorb (x && y) (x && z).
Proof. by intros[][][]. Qed. 

(** Negation *)

Lemma negb_neg : forall x, negb (negb x) = x.
Proof. by intros[]. Qed.
Lemma negb_and : forall x y, negb (x && y) = negb x || negb y.
Proof. by intros[][]. Qed.
Lemma negb_or : forall x y, negb (x || y) = negb x && negb y.
Proof. by intros[][]. Qed.
Lemma negb_xor : forall x y, negb (xorb x y) = xorb (negb x) y.
Proof. by intros[][]. Qed.


(** ** Automation support *)

Hint Rewrite 
  andTb andFb andbT andbF 
  orTb orFb orbT orbF
  : vlib_trivial.

Hint Rewrite 
  andbb andbN andNb 
  orbb orbN orNb 
  andbK andKb orbK orKb
  xorbb xorFb xorbF xorTb xorbT xorbb negb_neg 
  : vlib.

Hint Rewrite andbA orbA xorbA : vlibA.


(** Comparison for [nat] *)

Fixpoint eqn_rec (x y: nat) {struct x} :=
   match x, y with
     | O, O => true
     | S x, S y => eqn_rec x y
     | _, _ => false
   end.

Definition eqn := match tt with tt => eqn_rec end.

Lemma eqnP: forall x y, reflect (x = y) (eqn x y).
Proof.
  induction[] x [y]; vauto. 
  change (eqn (S x) (S y)) with (eqn x y).
  case IHx; constructor; congruence.
Qed.

Canonical Structure nat_eqMixin := EqMixin eqnP.
Canonical Structure nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Lemma eqnE : eqn = (@eq_op _).
Proof. done. Qed.
