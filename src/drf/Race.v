Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.

Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import MemoryRel.
Require Import SmallStep.

Set Implicit Arguments.


(* NOTE: `race_rw` requires two *distinct* threads to have a race.
 * However, C/C++ acknowledges intra-thread races.  For example,
 * according to the Standard, `f(x=1, x)` is RW-racy on `x`, since the
 * order of evaluation of the arguments is unspecified.  We currently
 * ignore this aspect of the race semantics.
 *)

Inductive Configuration_program_event c tid e : Prop :=
| configuration_program_event_intro lang st st' lc
    (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc))
    (STATE: (Language.step lang) e st st').
#[export]
Hint Constructors Configuration_program_event: core.

Inductive race_condition e1 e2 ord1 ord2 : Prop :=
| race_condition_rw loc val1 val2
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, val1, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ord2))
| race_condition_ww loc val1 val2
    (EVENT1: ProgramEvent.is_writing e1 = Some (loc, val1, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ord2))
.
#[export]
Hint Constructors race_condition: core.

Inductive race (c:Configuration.t) (ord1 ord2:Ordering.t): Prop :=
| race_intro
    tid1 e1
    tid2 e2
    (TID: tid1 <> tid2)
    (PROEVT1: Configuration_program_event c tid1 e1)
    (PROEVT2: Configuration_program_event c tid2 e2)
    (RACE: race_condition e1 e2 ord1 ord2)
.
#[export]
Hint Constructors race: core.

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc (small_step_all false) c1 c2)
    (RACE: race c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Lemma pf_racefree_steps
      c1 c2
      (FREE: pf_racefree c1)
      (STEPS: rtc (small_step_all false) c1 c2):
  pf_racefree c2.
Proof.
  ii. eapply FREE, RACE. etrans; eauto.
Qed.

Lemma small_step_to_program_step_writing
      c1 c2 e tid loc ord from ts val rel withprm
      (STEP: small_step withprm tid e c1 c2)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)):
  exists (pe : ProgramEvent.t),
  <<EVENT: Configuration_program_event c1 tid pe >> /\
  <<WRITE: ProgramEvent.is_writing pe = Some (loc, val, ord) >>.
Proof.
  inv STEP. inv STEP0; inv STEP; ss.
  inv LOCAL; inv EVENT; eauto 10.
Qed.

Lemma small_step_to_program_step_reading
      c1 c2 e tid loc ord ts val rel withprm
      (STEP: small_step withprm tid e c1 c2)
      (EVENT: ThreadEvent.is_reading e = Some (loc, ts, val, rel, ord)):
  exists (pe : ProgramEvent.t),
  <<EVENT: Configuration_program_event c1 tid pe >> /\
  <<WRITE: ProgramEvent.is_reading pe = Some (loc, val, ord) >>.
Proof.
  inv STEP. inv STEP0; inv STEP; ss.
  inv LOCAL; inv EVENT; eauto 10.
Qed.
