Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import Loc.

Require Import Event.
Require Import Time.

Set Implicit Arguments.

Module Language.
  Structure t := mk {
    syntax: Type;
    state: Type;

    init: syntax -> state;
    is_terminal: state -> Prop;
    step: forall (e:ProgramEvent.t) (s1:state) (s2:state), Prop;
  }.
End Language.
