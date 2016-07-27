(* ************************************************************************** *)
(** * Basic tactics *)
(* ************************************************************************** *)

(** This file collects a number of basic tactics for better proof automation,
    structuring large proofs, or rewriting.  Many of the definitions have been
    ported from ss-reflect. *)

(** Symbols starting with [hahn__] are internal. *)

Require Import Bool Arith ZArith String.
Require ClassicalFacts.
Require Export Classical FunctionalExtensionality ProofIrrelevance.

Open Scope bool_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** Shorthand for applying functional extensionality. *)

Ltac exten := apply functional_extensionality.

(* ************************************************************************** *)
(** ** Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma hahn__true_is_true : true.
Proof. reflexivity. Qed.

Lemma hahn__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Hint Resolve hahn__true_is_true hahn__not_false_is_true.

(* ************************************************************************** *)
(** ** Very basic automation *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb hahn discriminated. 

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac hahn__basic_done := 
  solve [trivial with hahn | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial with hahn; hnf; intros;
  solve [try hahn__basic_done; split; 
         try hahn__basic_done; split; 
         try hahn__basic_done; split; 
         try hahn__basic_done; split; 
         try hahn__basic_done; split; hahn__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try hahn__basic_done; split; 
         try eassumption; try hahn__basic_done; split; 
         try eassumption; try hahn__basic_done; split; 
         try eassumption; try hahn__basic_done; split; 
         try eassumption; try hahn__basic_done; split;
         try eassumption; hahn__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).

(* ************************************************************************** *)
(** ** Equality types *)
(* ************************************************************************** *)

Module Equality.

  Definition axiom T (e : T -> T -> bool) := 
    forall x y, reflect (x = y) (e x y).
  
  Structure mixin_of T := Mixin {op : T -> T -> bool; _ : axiom op}.
  Notation class_of := mixin_of (only parsing).
  
  Section ClassDef.
  
    Structure type := Pack {sort; _ : class_of sort; _ : Type}.

    Definition class cT' := 
      match cT' return class_of (sort cT') with @Pack _ c _ => c end.
  
    Definition pack (T: Type) c := @Pack T c T.
  
  End ClassDef.
  
  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation eqType := type.
    Notation EqMixin := Mixin.
    Notation EqType T m := (@pack T m).
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

Lemma hahn__internal_eqP : 
  forall (T: eqType) (x y : T), reflect (x = y) (x == y).
Proof. apply eqP. Qed.

Lemma neqP : forall (T: eqType) (x y: T), reflect (x <> y) (x != y).
Proof. intros; case eqP; constructor; auto. Qed.

Lemma beq_refl : forall (T : eqType) (x : T), x == x.
Proof. by intros; case eqP. Qed.

Lemma beq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Proof. intros; do 2 case eqP; congruence. Qed.

Hint Resolve beq_refl : hahn.
Hint Rewrite beq_refl : hahn_trivial.

Notation eqxx := beq_refl.

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
  induction x; destruct y; try (constructor; done). 
  change (eqn (S x) (S y)) with (eqn x y).
  case IHx; constructor; congruence.
Qed.

Canonical Structure nat_eqMixin := EqMixin eqnP.
Canonical Structure nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Lemma eqnE : eqn = (@eq_op _).
Proof. done. Qed.


(* ************************************************************************** *)
(** ** Basic simplification tactics *)
(* ************************************************************************** *)

Lemma hahn__negb_rewrite : forall b, negb b -> b = false.
Proof. by intros []. Qed.

Lemma hahn__andb_split : forall b1 b2, b1 && b2 -> b1 /\ b2.
Proof. by intros [] []. Qed.

Lemma hahn__nandb_split : forall b1 b2, b1 && b2 = false -> b1 = false \/ b2 = false.
Proof. intros [] []; auto. Qed. 

Lemma hahn__orb_split : forall b1 b2, b1 || b2 -> b1 \/ b2.
Proof. intros [] []; auto. Qed.

Lemma hahn__norb_split : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma hahn__eqb_split : forall b1 b2 : bool, (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. intros [] [] H H'; unfold is_true in *; auto using sym_eq. Qed.

Lemma hahn__beq_rewrite : forall (T : eqType) (x1 x2 : T), x1 == x2 -> x1 = x2.
Proof. by intros until 0; case eqP. Qed.


(** Set up for basic simplification: database of reflection lemmas *)

Create HintDb hahn_refl discriminated.  

Hint Resolve hahn__internal_eqP neqP : hahn_refl.

Ltac hahn__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H; clear H; intros; subst X;
  try subst.

Ltac hahn__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => 
      let H' := fresh H in case (hahn__andb_split H); clear H; intros H' H
  | [H: is_true (negb ?x) |- _] => rewrite (hahn__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: is_true (_ == _)  |- _] => generalize (hahn__beq_rewrite H); clear H; intro H
  | [H: @existT _ _ _ _ = @existT _ _ _ _ |- _] => apply inj_pair2 in H; try subst
  | [H: ?f _             = ?f _             |- _] => hahn__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => hahn__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  hahn__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; hahn__clarify1
  end; (* autorewrite with hahn_trivial; *) try done.

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

Ltac hahn__clarsimp1 :=
  clarify; (autorewrite with hahn_trivial hahn in * ); 
  (autorewrite with hahn_trivial in * ); try done;
  clarify; auto 1 with hahn.

Ltac clarsimp := intros; simpl in *; hahn__clarsimp1.

Ltac autos   := clarsimp; auto with hahn.


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
    | H: is_true (_ == _) |- _ => generalize (hahn__beq_rewrite H); clear H; intro H
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
          let H' := fresh H in case (hahn__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
          let H' := fresh H in case (hahn__norb_split H); clear H; intros H H'
    | H : ?x = ?x   |- _ => clear H

(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with hahn_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with hahn_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with hahn_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with hahn_refl]]  *)
  end.

Ltac des :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (hahn__beq_rewrite H); clear H; intro H
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
        let H' := fresh H in case (hahn__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
        let H' := fresh H in case (hahn__norb_split H); clear H; intros H H'
    | H : ?x = ?x |- _ => clear H
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
    | H : is_true (_ || _) |- _ => case (hahn__orb_split H); clear H; intro H
    | H : (_ && _) = false |- _ => case (hahn__nandb_split H); clear H; intro H
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
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
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
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
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
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
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

Ltac clarassoc := clarsimp; autorewrite with hahn_trivial hahn hahnA in *; try done. 

Ltac hahn__hacksimp1 :=
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
   | |- context[match ?p with _ => _ end] => solve [destruct p; hahn__hacksimp1]
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


