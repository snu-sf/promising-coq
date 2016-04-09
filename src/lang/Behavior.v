Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* NOTE: we serialize all the events within a behavior, but it may not
 * be the case.  The *NIX kernels are re-entrant: system calls may
 * race.
 *)
CoInductive behavior :=
| behvaior_nil
| behavior_event (e:Event.t) (b:behavior)
| behavior_inftau
.

(* TODO *)
Definition behaviors (conf:Configuration.t) (b:behavior): Prop :=
  False.
