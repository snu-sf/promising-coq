Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.

(* TODO: We currently consider only finite behaviors of program: we
 * ignore non-terminating executions.  This simplification affects two
 * aspects of the development:
 *
 * - Liveness.  In our definition, the liveness matters only for
 *   non-terminating execution.
 *
 * - Simulation.  We do not introduce simulation index for inftau
 *   behaviors (i.e. infinite loop without system call interactions).
 *
 * We will consdier infinite behaviors in the future work
 * (https://github.com/jeehoonkang/memory-model-explorer/issues/50).
 *)
(* NOTE: We serialize all the events within a behavior, but it may not
 * be the case.  The *NIX kernels are re-entrant: system calls may
 * race.
 *)
Inductive behavior :=
| behvaior_nil
| behavior_event (e:Event.t) (b:behavior)
.

(* TODO *)
Definition behaviors (conf:Configuration.t) (b:behavior): Prop :=
  False.
