Require Import paco7.
Require Import sflib.

Set Implicit Arguments.

Section Respectful7.
  Variable T0: Type.
  Variable T1: forall (x0: @T0), Type.
  Variable T2: forall (x0: @T0) (x1: @T1 x0), Type.
  Variable T3: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
  Variable T4: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
  Variable T5: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
  Variable T6: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
  Definition rel := rel7 T0 T1 T2 T3 T4 T5 T6.

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone7 gf.

  Inductive sound7 (clo: rel -> rel): Prop :=
  | sound7_intro
      (MON: monotone7 clo)
      (SOUND:
         forall r (PFIX: r <7= gf (clo r)),
           r <7= paco7 gf bot7)
  .
  Hint Constructors sound7.

  Structure respectful7 (clo: rel -> rel) : Prop := respectful7_intro {
    MON: monotone7 clo;
    RESPECTFUL:
      forall l r (LE: l <7= r) (GF: l <7= gf r),
        clo l <7= gf (clo r);
  }.
  Hint Constructors respectful7.

  Inductive grespectful7 (r: rel) e1 e2 e3 e4 e5 e6 e7: Prop :=
  | grespectful7_intro
      clo
      (RES: respectful7 clo)
      (CLO: clo r e1 e2 e3 e4 e5 e6 e7)
  .
  Hint Constructors grespectful7.

  Lemma gfclo7_mon: forall clo, sound7 clo -> monotone7 (gf <*> clo).
  Proof. intros; destruct H; eauto using gf_mon. Qed.
  Hint Resolve gfclo7_mon : paco.

  Lemma sound7_is_gf: forall clo (UPTO: sound7 clo),
      paco7 (gf <*> clo) bot7 <7= paco7 gf bot7.
  Proof.
    i. punfold PR. edestruct UPTO.
    eapply (SOUND (paco7 (gf <*> clo) bot7)); eauto.
    i. punfold PR0.
    eapply (gfclo7_mon UPTO); eauto.
    intros. destruct PR1; eauto. done.
  Qed.

  Lemma respectful7_is_sound7: respectful7 <1= sound7.
  Proof.
    intro clo.
    set (rclo := fix rclo clo n (r: rel) :=
           match n with
           | 0 => r
           | S n' => rclo clo n' r \7/ clo (rclo clo n' r)
           end).
    i. destruct PR. econs; eauto.
    i. set (rr e1 e2 e3 e4 e5 e6 e7 := exists n, rclo clo n r e1 e2 e3 e4 e5 e6 e7).
    assert (rr x0 x1 x2 x3 x4 x5 x6) by (exists 0; eauto); clear PR.
    cut (forall n, rclo clo n r <7= gf (rclo clo (S n) r)).
    { intro X; revert x0 x1 x2 x3 x4 x5 x6 H; pcofix CIH; i.
      unfold rr in *; des; eauto 10 using gf_mon. }
    induction n; i; [by s; eauto using gf_mon|].
    ss; des; [by eauto using gf_mon|].
    eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; inst; s; eauto.
  Qed.

  Lemma respectful7_compose
        clo1 clo2
        (RES1: respectful7 clo1)
        (RES2: respectful7 clo2):
    respectful7 (clo1 <*> clo2).
  Proof.
    i. destruct RES1, RES2.
    econs.
    - ii. eapply MON0; eauto.
    - i. eapply RESPECTFUL0; [| |apply PR].
      + i. eapply MON1; eauto.
      + i. eapply RESPECTFUL1; eauto.
  Qed.

  Lemma grespectful7_respectful7: respectful7 grespectful7.
  Proof.
    econs; ii.
    - destructs IN RES; exists clo; eauto.
    - destructs PR RES; eapply gf_mon with (r:=clo r); eauto.
  Qed.

  Lemma gfgres7_mon: monotone7 (gf <*> grespectful7).
  Proof.
    destruct grespectful7_respectful7; eauto using gf_mon.
  Qed.
  Hint Resolve gfgres7_mon : paco.

  Lemma grespectful7_greatest: forall clo (RES: respectful7 clo), clo <8= grespectful7.
  Proof.
    eauto.
  Qed.

  Lemma grespectful7_incl: forall r, r <7= grespectful7 r.
  Proof.
    i; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve grespectful7_incl.

  Lemma grespectful7_compose: forall clo (RES: respectful7 clo) r,
      clo (grespectful7 r) <7= grespectful7 r.
  Proof.
    i; eapply grespectful7_greatest with (clo := clo <*> grespectful7);
      eauto using respectful7_compose, grespectful7_respectful7.
  Qed.

  Lemma grespectful7_incl_rev: forall r,
      grespectful7 (paco7 (gf <*> grespectful7) r) <7= paco7 (gf <*> grespectful7) r.
  Proof.
    intro r; pcofix CIH; i; pfold.
    eapply gf_mon, grespectful7_compose, grespectful7_respectful7.
    destruct grespectful7_respectful7; eapply RESPECTFUL0, PR; i; [by apply grespectful7_incl; eauto|].
    punfold PR0.
      by eapply gfgres7_mon; eauto; i; destruct PR1; eauto.
  Qed.

  Inductive rclo7 clo (r: rel): rel :=
  | rclo7_incl
      e1 e2 e3 e4 e5 e6 e7
      (R: r e1 e2 e3 e4 e5 e6 e7):
      @rclo7 clo r e1 e2 e3 e4 e5 e6 e7
  | rclo7_step'
      r' e1 e2 e3 e4 e5 e6 e7
      (R': r' <7= rclo7 clo r)
      (CLOR':clo r' e1 e2 e3 e4 e5 e6 e7):
      @rclo7 clo r e1 e2 e3 e4 e5 e6 e7
  .

  Lemma rclo7_mon clo:
    monotone7 (rclo7 clo).
  Proof.
    ii. induction IN.
    - econs 1. auto.
    - econs 2; eauto.
  Qed.
  Hint Resolve rclo7_mon: paco.

  Lemma rclo7_base
        clo
        (MON: monotone7 clo):
    clo <8= rclo7 clo.
  Proof.
    s. i. econs 2; eauto.
    eapply MON; eauto. i.
    econs 1. eauto.
  Qed.

  Lemma rclo7_step
        (clo: rel -> rel) r:
    clo (rclo7 clo r) <7= rclo7 clo r.
  Proof.
    i. econs 2; eauto.
  Qed.

  Lemma rclo7_rclo7
        clo r
        (MON: monotone7 clo):
    rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
  Proof.
    i. induction PR; eauto.
    econs 2; eauto.
  Qed.

  Structure weak_respectful7 (clo: rel -> rel) : Prop := weak_respectful7_intro {
    WEAK_MON: monotone7 clo;
    WEAK_RESPECTFUL:
      forall l r (LE: l <7= r) (GF: l <7= gf r),
        clo l <7= gf (rclo7 clo r);
  }.
  Hint Constructors weak_respectful7.

  Lemma weak_respectful7_respectful7
        clo (RES: weak_respectful7 clo):
    respectful7 (rclo7 clo).
  Proof.
    inv RES. econs; eauto with paco. i.
    induction PR; i.
    - eapply gf_mon; eauto. i.
      apply rclo7_incl. auto.
    - exploit WEAK_RESPECTFUL0; [|apply H|apply CLOR'|].
      + i. eapply rclo7_mon; eauto.
      + i. eapply gf_mon; eauto.
        apply rclo7_rclo7; auto.
  Qed.

  Lemma upto7_init:
      paco7 (gf <*> grespectful7) bot7 <7= paco7 gf bot7.
  Proof.
    apply sound7_is_gf; eauto.
    apply respectful7_is_sound7.
    apply grespectful7_respectful7.
  Qed.

  Lemma upto7_final:
    paco7 gf <8= paco7 (gf <*> grespectful7).
  Proof.
    pcofix CIH. i. punfold PR. pfold.
    eapply gf_mon; [|apply grespectful7_incl].
    eapply gf_mon; eauto. i. right. inv PR0; auto.
  Qed.

  Lemma upto7_step
        r clo (RES: weak_respectful7 clo):
    clo (paco7 (gf <*> grespectful7) r) <7= paco7 (gf <*> grespectful7) r.
  Proof.
    i. apply grespectful7_incl_rev.
    exploit weak_respectful7_respectful7; eauto. i.
    eapply grespectful7_greatest; eauto.
    apply rclo7_base; auto. inv RES. auto.
  Qed.
End Respectful7.

Ltac pupto7_init := apply upto7_init; eauto with paco.
Ltac pupto7_final := apply upto7_final; eauto with paco.
Ltac pupto7 H := eapply upto7_step; [|exact H|]; eauto with paco.
