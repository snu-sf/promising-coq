Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.

Set Implicit Arguments.

Module Language.
  Structure t := mk {
    syntax: Type;
    state: Type;

    init: syntax -> state;
    is_terminal: state -> Prop;
    step: forall (s1:state) (e:option ThreadEvent.t) (s2:state), Prop;
  }.
End Language.
