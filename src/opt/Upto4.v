Require Import paco4.
Require Import sflib.

Set Implicit Arguments.

Section Respectful4.
  Variable T0: Type.
  Variable T1: forall (x0: @T0), Type.
  Variable T2: forall (x0: @T0) (x1: @T1 x0), Type.
  Variable T3: forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
  Definition rel := rel4 T0 T1 T2 T3.

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone4 gf.

  Inductive sound (clo: rel -> rel): Prop :=
  | sound_intro
      (MON: monotone4 clo)
      (SOUND:
         forall r (PFIX: r <4= gf (clo r)),
           r <4= paco4 gf bot4)
  .
  Hint Constructors sound.

  Structure respectful (clo: rel -> rel) : Prop :=
  | respectful_intro
      (MON: monotone4 clo)
      (RESPECTFUL:
         forall l r (LE: l <4= r) (GF: l <4= gf r),
           clo l <4= gf (clo r)).
  Hint Constructors respectful.

  Inductive grespectful (r: rel) e1 e2 e3 e4: Prop :=
  | grespectful_intro
      clo
      (RES: respectful clo)
      (CLO: clo r e1 e2 e3 e4)
  .
  Hint Constructors grespectful.

  Lemma gfclo_mon: forall clo, sound clo -> monotone4 (gf <*> clo).
  Proof. intros; destruct H; eauto using gf_mon. Qed.
  Hint Resolve gfclo_mon : paco.

  Lemma sound_is_gf: forall clo (UPTO: sound clo),
      paco4 (gf <*> clo) bot4 <4= paco4 gf bot4.
  Proof.
    i. punfold PR. edestruct UPTO.
    eapply (SOUND (paco4 (gf <*> clo) bot4)); eauto.
    i. punfold PR0.
    eapply (gfclo_mon UPTO); eauto.
    intros. destruct PR1; eauto. done.
  Qed.

  Lemma respectful_is_sound: respectful <1= sound.
  Proof.
    intro clo.
    set (rclo := fix rclo clo n (r: rel) :=
           match n with
           | 0 => r
           | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
           end).
    i. destruct PR. econs; eauto.
    i. set (rr e1 e2 e3 e4 := exists n, rclo clo n r e1 e2 e3 e4).
    assert (rr x0 x1 x2 x3) by (exists 0; eauto); clear PR.
    cut (forall n, rclo clo n r <4= gf (rclo clo (S n) r)).
    { intro X; revert x0 x1 x2 x3 H; pcofix CIH; i.
      unfold rr in *; des; eauto 10 using gf_mon. }
    induction n; i; [by s; eauto using gf_mon|].
    ss; des; [by eauto using gf_mon|].
    eapply gf_mon; [eapply RESPECTFUL; [|apply IHn|]|]; inst; s; eauto.
  Qed.

  Lemma respectful_compose
        clo1 clo2
        (RES1: respectful clo1)
        (RES2: respectful clo2):
    respectful (clo1 <*> clo2).
  Proof.
    i. destruct RES1, RES2.
    econs.
    - ii. eapply MON; eauto.
    - i. eapply RESPECTFUL; [| |apply PR].
      + i. eapply MON0; eauto.
      + i. eapply RESPECTFUL0; eauto.
  Qed.

  Lemma grespectful_respectful: respectful grespectful.
  Proof.
    econs; ii.
    - destructs IN RES; exists clo; eauto.
    - destructs PR RES; eapply gf_mon with (r:=clo r); eauto.
  Qed.

  Lemma gfgres_mon: monotone4 (gf <*> grespectful).
  Proof.
    destruct grespectful_respectful; eauto using gf_mon.
  Qed.
  Hint Resolve gfgres_mon : paco.

  Lemma grespectful_greatest: forall clo (RES: respectful clo), clo <5= grespectful.
  Proof.
    eauto.
  Qed.

  Lemma grespectful_incl: forall r, r <4= grespectful r.
  Proof.
    i; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve grespectful_incl.

  Lemma grespectful_compose: forall clo (RES: respectful clo) r,
      clo (grespectful r) <4= grespectful r.
  Proof.
    i; eapply grespectful_greatest with (clo := clo <*> grespectful);
      eauto using respectful_compose, grespectful_respectful.
  Qed.

  Lemma grespectful_incl_rev: forall r,
      grespectful (paco4 (gf <*> grespectful) r) <4= paco4 (gf <*> grespectful) r.
  Proof.
    intro r; pcofix CIH; i; pfold.
    eapply gf_mon, grespectful_compose, grespectful_respectful.
    destruct grespectful_respectful; eapply RESPECTFUL, PR; i; [by eauto using grespectful_incl|].
    punfold PR0.
      by eapply gfgres_mon; eauto; i; destruct PR1; eauto.
  Qed.
End Respectful4.
