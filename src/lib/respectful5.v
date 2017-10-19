Require Import paco5.
Require Import sflib.

Set Implicit Arguments.

Section Respectful5.
  Variable T0: Type.
  Variable T1: forall (x0: @T0), Type.
  Variable T2: forall (x0: @T0) (x1: @T1 x0), Type.
  Variable T3: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
  Variable T4: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
  Definition rel := rel5 T0 T1 T2 T3 T4.

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone5 gf.

  Inductive sound5 (clo: rel -> rel): Prop :=
  | sound5_intro
      (MON: monotone5 clo)
      (SOUND:
         forall r (PFIX: r <5= gf (clo r)),
           r <5= paco5 gf bot5)
  .
  Hint Constructors sound5.

  Structure respectful5 (clo: rel -> rel) : Prop := respectful5_intro {
    MON: monotone5 clo;
    RESPECTFUL:
      forall l r (LE: l <5= r) (GF: l <5= gf r),
        clo l <5= gf (clo r);
  }.
  Hint Constructors respectful5.

  Inductive grespectful5 (r: rel) e1 e2 e3 e4 e5: Prop :=
  | grespectful5_intro
      clo
      (RES: respectful5 clo)
      (CLO: clo r e1 e2 e3 e4 e5)
  .
  Hint Constructors grespectful5.

  Lemma gfclo5_mon: forall clo, sound5 clo -> monotone5 (gf <*> clo).
  Proof. intros; destruct H; eauto using gf_mon. Qed.
  Hint Resolve gfclo5_mon : paco.

  Lemma sound5_is_gf: forall clo (UPTO: sound5 clo),
      paco5 (gf <*> clo) bot5 <5= paco5 gf bot5.
  Proof.
    i. punfold PR. edestruct UPTO.
    eapply (SOUND (paco5 (gf <*> clo) bot5)); eauto.
    i. punfold PR0.
    eapply (gfclo5_mon UPTO); eauto.
    intros. destruct PR1; eauto. done.
  Qed.

  Lemma respectful5_is_sound5: respectful5 <1= sound5.
  Proof.
    intro clo.
    set (rclo := fix rclo clo n (r: rel) :=
           match n with
           | 0 => r
           | S n' => rclo clo n' r \5/ clo (rclo clo n' r)
           end).
    i. destruct PR. econs; eauto.
    i. set (rr e1 e2 e3 e4 e5 := exists n, rclo clo n r e1 e2 e3 e4 e5).
    assert (rr x0 x1 x2 x3 x4) by (exists 0; eauto); clear PR.
    cut (forall n, rclo clo n r <5= gf (rclo clo (S n) r)).
    { intro X; revert x0 x1 x2 x3 x4 H; pcofix CIH; i.
      unfold rr in *; des; eauto 10 using gf_mon. }
    induction n; i; [by s; eauto using gf_mon|].
    ss; des; [by eauto using gf_mon|].
    eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; inst; s; eauto.
  Qed.

  Lemma respectful5_compose
        clo1 clo2
        (RES1: respectful5 clo1)
        (RES2: respectful5 clo2):
    respectful5 (clo1 <*> clo2).
  Proof.
    i. destruct RES1, RES2.
    econs.
    - ii. eapply MON0; eauto.
    - i. eapply RESPECTFUL0; [| |apply PR].
      + i. eapply MON1; eauto.
      + i. eapply RESPECTFUL1; eauto.
  Qed.

  Lemma grespectful5_respectful5: respectful5 grespectful5.
  Proof.
    econs; ii.
    - destructs IN RES; exists clo; eauto.
    - destructs PR RES; eapply gf_mon with (r:=clo r); eauto.
  Qed.

  Lemma gfgres5_mon: monotone5 (gf <*> grespectful5).
  Proof.
    destruct grespectful5_respectful5; eauto using gf_mon.
  Qed.
  Hint Resolve gfgres5_mon : paco.

  Lemma grespectful5_greatest: forall clo (RES: respectful5 clo), clo <6= grespectful5.
  Proof.
    eauto.
  Qed.

  Lemma grespectful5_incl: forall r, r <5= grespectful5 r.
  Proof.
    i; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve grespectful5_incl.

  Lemma grespectful5_compose: forall clo (RES: respectful5 clo) r,
      clo (grespectful5 r) <5= grespectful5 r.
  Proof.
    i; eapply grespectful5_greatest with (clo := clo <*> grespectful5);
      eauto using respectful5_compose, grespectful5_respectful5.
  Qed.

  Lemma grespectful5_incl_rev: forall r,
      grespectful5 (paco5 (gf <*> grespectful5) r) <5= paco5 (gf <*> grespectful5) r.
  Proof.
    intro r; pcofix CIH; i; pfold.
    eapply gf_mon, grespectful5_compose, grespectful5_respectful5.
    destruct grespectful5_respectful5; eapply RESPECTFUL0, PR; i; [by apply grespectful5_incl; eauto|].
    punfold PR0.
      by eapply gfgres5_mon; eauto; i; destruct PR1; eauto.
  Qed.

  Inductive rclo5 clo (r: rel): rel :=
  | rclo5_incl
      e1 e2 e3 e4 e5
      (R: r e1 e2 e3 e4 e5):
      @rclo5 clo r e1 e2 e3 e4 e5
  | rclo5_step'
      r' e1 e2 e3 e4 e5
      (R': r' <5= rclo5 clo r)
      (CLOR':clo r' e1 e2 e3 e4 e5):
      @rclo5 clo r e1 e2 e3 e4 e5
  .

  Lemma rclo5_mon clo:
    monotone5 (rclo5 clo).
  Proof.
    ii. induction IN.
    - econs 1. auto.
    - econs 2; eauto.
  Qed.
  Hint Resolve rclo5_mon: paco.

  Lemma rclo5_base
        clo
        (MON: monotone5 clo):
    clo <6= rclo5 clo.
  Proof.
    s. i. econs 2; eauto.
    eapply MON; eauto. i.
    econs 1. eauto.
  Qed.

  Lemma rclo5_step
        (clo: rel -> rel) r:
    clo (rclo5 clo r) <5= rclo5 clo r.
  Proof.
    i. econs 2; eauto.
  Qed.

  Lemma rclo5_rclo5
        clo r
        (MON: monotone5 clo):
    rclo5 clo (rclo5 clo r) <5= rclo5 clo r.
  Proof.
    i. induction PR; eauto.
    econs 2; eauto.
  Qed.

  Structure weak_respectful5 (clo: rel -> rel) : Prop := weak_respectful5_intro {
    WEAK_MON: monotone5 clo;
    WEAK_RESPECTFUL:
      forall l r (LE: l <5= r) (GF: l <5= gf r),
        clo l <5= gf (rclo5 clo r);
  }.
  Hint Constructors weak_respectful5.

  Lemma weak_respectful5_respectful5
        clo (RES: weak_respectful5 clo):
    respectful5 (rclo5 clo).
  Proof.
    inv RES. econs; eauto with paco. i.
    induction PR; i.
    - eapply gf_mon; eauto. i.
      apply rclo5_incl. auto.
    - exploit WEAK_RESPECTFUL0; [|apply H|apply CLOR'|].
      + i. eapply rclo5_mon; eauto.
      + i. eapply gf_mon; eauto.
        apply rclo5_rclo5; auto.
  Qed.

  Lemma upto5_init:
      paco5 (gf <*> grespectful5) bot5 <5= paco5 gf bot5.
  Proof.
    apply sound5_is_gf; eauto.
    apply respectful5_is_sound5.
    apply grespectful5_respectful5.
  Qed.

  Lemma upto5_final:
    paco5 gf <6= paco5 (gf <*> grespectful5).
  Proof.
    pcofix CIH. i. punfold PR. pfold.
    eapply gf_mon; [|apply grespectful5_incl].
    eapply gf_mon; eauto. i. right. inv PR0; auto.
  Qed.

  Lemma upto5_step
        r clo (RES: weak_respectful5 clo):
    clo (paco5 (gf <*> grespectful5) r) <5= paco5 (gf <*> grespectful5) r.
  Proof.
    i. apply grespectful5_incl_rev.
    exploit weak_respectful5_respectful5; eauto. i.
    eapply grespectful5_greatest; eauto.
    apply rclo5_base; auto. inv RES. auto.
  Qed.
End Respectful5.

Ltac pupto5_init := apply upto5_init; eauto with paco.
Ltac pupto5_final := apply upto5_final; eauto with paco.
Ltac pupto5 H := eapply upto5_step; [|exact H|]; eauto with paco.
