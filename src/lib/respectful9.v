Require Import paco9.
Require Import sflib.

Set Implicit Arguments.

Section Respectful9.
  Variable T0: Type.
  Variable T1: forall (x0: @T0), Type.
  Variable T2: forall (x0: @T0) (x1: @T1 x0), Type.
  Variable T3: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
  Variable T4: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
  Variable T5: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
  Variable T6: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
  Variable T7: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
  Variable T8: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
  Definition rel := rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone9 gf.

  Inductive sound9 (clo: rel -> rel): Prop :=
  | sound9_intro
      (MON: monotone9 clo)
      (SOUND:
         forall r (PFIX: r <9= gf (clo r)),
           r <9= paco9 gf bot9)
  .
  Hint Constructors sound9.

  Structure respectful9 (clo: rel -> rel) : Prop :=
  | respectful9_intro
      (MON: monotone9 clo)
      (RESPECTFUL:
         forall l r (LE: l <9= r) (GF: l <9= gf r),
           clo l <9= gf (clo r)).
  Hint Constructors respectful9.

  Inductive grespectful9 (r: rel) e1 e2 e3 e4 e5 e6 e7 e8 e9: Prop :=
  | grespectful9_intro
      clo
      (RES: respectful9 clo)
      (CLO: clo r e1 e2 e3 e4 e5 e6 e7 e8 e9)
  .
  Hint Constructors grespectful9.

  Lemma gfclo9_mon: forall clo, sound9 clo -> monotone9 (gf <*> clo).
  Proof. intros; destruct H; eauto using gf_mon. Qed.
  Hint Resolve gfclo9_mon : paco.

  Lemma sound9_is_gf: forall clo (UPTO: sound9 clo),
      paco9 (gf <*> clo) bot9 <9= paco9 gf bot9.
  Proof.
    i. punfold PR. edestruct UPTO.
    eapply (SOUND (paco9 (gf <*> clo) bot9)); eauto.
    i. punfold PR0.
    eapply (gfclo9_mon UPTO); eauto.
    intros. destruct PR1; eauto. done.
  Qed.

  Lemma respectful9_is_sound9: respectful9 <1= sound9.
  Proof.
    intro clo.
    set (rclo := fix rclo clo n (r: rel) :=
           match n with
           | 0 => r
           | S n' => rclo clo n' r \9/ clo (rclo clo n' r)
           end).
    i. destruct PR. econs; eauto.
    i. set (rr e1 e2 e3 e4 e5 e6 e7 e8 e9 := exists n, rclo clo n r e1 e2 e3 e4 e5 e6 e7 e8 e9).
    assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8) by (exists 0; eauto); clear PR.
    cut (forall n, rclo clo n r <9= gf (rclo clo (S n) r)).
    { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H; pcofix CIH; i.
      unfold rr in *; des; eauto 10 using gf_mon. }
    induction n; i; [by s; eauto using gf_mon|].
    ss; des; [by eauto using gf_mon|].
    eapply gf_mon; [eapply RESPECTFUL; [|apply IHn|]|]; inst; s; eauto.
  Qed.

  Lemma respectful9_compose
        clo1 clo2
        (RES1: respectful9 clo1)
        (RES2: respectful9 clo2):
    respectful9 (clo1 <*> clo2).
  Proof.
    i. destruct RES1, RES2.
    econs.
    - ii. eapply MON; eauto.
    - i. eapply RESPECTFUL; [| |apply PR].
      + i. eapply MON0; eauto.
      + i. eapply RESPECTFUL0; eauto.
  Qed.

  Lemma grespectful9_respectful9: respectful9 grespectful9.
  Proof.
    econs; ii.
    - destructs IN RES; exists clo; eauto.
    - destructs PR RES; eapply gf_mon with (r:=clo r); eauto.
  Qed.

  Lemma gfgres9_mon: monotone9 (gf <*> grespectful9).
  Proof.
    destruct grespectful9_respectful9; eauto using gf_mon.
  Qed.
  Hint Resolve gfgres9_mon : paco.

  Lemma grespectful9_greatest: forall clo (RES: respectful9 clo), clo <10= grespectful9.
  Proof.
    eauto.
  Qed.

  Lemma grespectful9_incl: forall r, r <9= grespectful9 r.
  Proof.
    i; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve grespectful9_incl.

  Lemma grespectful9_compose: forall clo (RES: respectful9 clo) r,
      clo (grespectful9 r) <9= grespectful9 r.
  Proof.
    i; eapply grespectful9_greatest with (clo := clo <*> grespectful9);
      eauto using respectful9_compose, grespectful9_respectful9.
  Qed.

  Lemma grespectful9_incl_rev: forall r,
      grespectful9 (paco9 (gf <*> grespectful9) r) <9= paco9 (gf <*> grespectful9) r.
  Proof.
    intro r; pcofix CIH; i; pfold.
    eapply gf_mon, grespectful9_compose, grespectful9_respectful9.
    destruct grespectful9_respectful9; eapply RESPECTFUL, PR; i; [by eauto using grespectful9_incl|].
    punfold PR0.
      by eapply gfgres9_mon; eauto; i; destruct PR1; eauto.
  Qed.

  Inductive rclo9 clo (r: rel): rel :=
  | rclo9_incl
      e1 e2 e3 e4 e5 e6 e7 e8 e9
      (R: r e1 e2 e3 e4 e5 e6 e7 e8 e9):
      @rclo9 clo r e1 e2 e3 e4 e5 e6 e7 e8 e9
  | rclo9_step'
      r' e1 e2 e3 e4 e5 e6 e7 e8 e9
      (R': r' <9= rclo9 clo r)
      (CLOR':clo r' e1 e2 e3 e4 e5 e6 e7 e8 e9):
      @rclo9 clo r e1 e2 e3 e4 e5 e6 e7 e8 e9
  .

  Lemma rclo9_mon clo:
    monotone9 (rclo9 clo).
  Proof.
    ii. induction IN.
    - econs 1. auto.
    - econs 2; eauto.
  Qed.
  Hint Resolve rclo9_mon: paco.

  Lemma rclo9_base
        clo
        (MON: monotone9 clo):
    clo <10= rclo9 clo.
  Proof.
    s. i. econs 2; eauto.
    eapply MON; eauto. i.
    econs 1. eauto.
  Qed.

  Lemma rclo9_step
        (clo: rel -> rel) r:
    clo (rclo9 clo r) <9= rclo9 clo r.
  Proof.
    i. econs 2; eauto.
  Qed.

  Lemma rclo9_rclo9
        clo r
        (MON: monotone9 clo):
    rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
  Proof.
    i. induction PR; eauto.
    econs 2; eauto.
  Qed.

  Structure weak_respectful9 (clo: rel -> rel) : Prop :=
  | weak_respectful9_intro
      (MON: monotone9 clo)
      (RESPECTFUL:
         forall l r (LE: l <9= r) (GF: l <9= gf r),
           clo l <9= gf (rclo9 clo r)).
  Hint Constructors weak_respectful9.

  Lemma weak_respectful9_respectful9
        clo (RES: weak_respectful9 clo):
    respectful9 (rclo9 clo).
  Proof.
    inv RES. econs; eauto with paco. i.
    induction PR; i.
    - eapply gf_mon; eauto. i.
      apply rclo9_incl. auto.
    - exploit RESPECTFUL; [|apply H|apply CLOR'|].
      + i. eapply rclo9_mon; eauto.
      + i. eapply gf_mon; eauto.
        apply rclo9_rclo9; auto.
  Qed.

  Lemma upto9_init:
      paco9 (gf <*> grespectful9) bot9 <9= paco9 gf bot9.
  Proof.
    apply sound9_is_gf; eauto.
    apply respectful9_is_sound9.
    apply grespectful9_respectful9.
  Qed.

  Lemma upto9_final:
    paco9 gf <10= paco9 (gf <*> grespectful9).
  Proof.
    pcofix CIH. i. punfold PR. pfold.
    eapply gf_mon; [|apply grespectful9_incl].
    eapply gf_mon; eauto. right. des; auto.
  Qed.

  Lemma upto9_step
        r clo (RES: weak_respectful9 clo):
    clo (paco9 (gf <*> grespectful9) r) <9= paco9 (gf <*> grespectful9) r.
  Proof.
    i. apply grespectful9_incl_rev.
    exploit weak_respectful9_respectful9; eauto. i.
    eapply grespectful9_greatest; eauto.
    apply rclo9_base; auto. inv RES. auto.
  Qed.
End Respectful9.

Ltac pupto9_init := apply upto9_init; eauto with paco.
Ltac pupto9_final := apply upto9_final; eauto with paco.
Ltac pupto9 H := eapply upto9_step; [|exact H|]; eauto with paco.
