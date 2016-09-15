Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.

Set Implicit Arguments.

Module Language.
  Inductive receptive
            (state:Type)
            (step: forall (e:ProgramEvent.t) (s1:state) (s2:state), Prop): Prop :=
  | receptive_intro
      (READ:
         forall st loc ord
           val1 st1
           val2
           (STEP1: step (ProgramEvent.read loc val1 ord) st st1),
         exists st2,
           <<STEP2: step (ProgramEvent.read loc val2 ord) st st2>>)
      (UPDATE:
         forall st loc or ow
           vr1 vw1 st1
           vr2
           (STEP1: step (ProgramEvent.update loc vr1 vw1 or ow) st st1),
         exists vw2 st2,
           <<STEP2: step (ProgramEvent.update loc vr2 vw2 or ow) st st2>>)
  .

  Structure t := mk {
    syntax: Type;
    state: Type;

    init: syntax -> state;
    is_terminal: state -> Prop;
    step: forall (e:ProgramEvent.t) (s1:state) (s2:state), Prop;

    RECEPTIVE: receptive step;
  }.
End Language.
