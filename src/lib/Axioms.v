Require Export Classical.
Require Export FunctionalExtensionality.

Axiom prop_ext:
  forall (P Q : Prop), 
    (P <-> Q) -> P = Q.
