Require Import sflib.

Require Import Event.
Require Import Configuration.
Require Import Program.

Set Implicit Arguments.

Inductive tausteps: forall (src:Configuration.t) (src':Configuration.t), Prop :=
| tausteps_nil
    src:
    tausteps src src
| tausteps_cons
    src src' src''
    (STEP: Configuration.step src None src')
    (STEPS: tausteps src' src''):
    tausteps src src''
.

Inductive srcsteps: forall (src:Configuration.t) (e:option Event.t) (src':Configuration.t), Prop :=
| srcsteps_stationary
    src src'
    (TAU: tausteps src src'):
    srcsteps src None src'
| srcsteps_progress
    src src' src'' e
    (TAU: tausteps src src')
    (PROGRESS: Configuration.step src' e src''):
    srcsteps src e src''
.

(* TODO: proper use of indexes *)
Module Simulation.
  Section Simulation.
    Variable (prog_src prog_tgt:Program.t).
    Variable (sim: forall (src tgt:Configuration.t), Prop).

    Definition LOAD: Prop :=
      forall tgt (TGT: Program.load prog_tgt tgt),
      exists src,
        <<SRC: Program.load prog_src src>> /\
        <<SIM: sim src tgt>>.

    Definition STEP: Prop :=
      forall src tgt e tgt'
        (SIM: sim src tgt)
        (STEP: Configuration.step tgt e tgt'),
      exists src',
        <<STEP: srcsteps src e src'>> /\
                <<SIM: sim src' tgt'>>.

    Definition OBSERVABLE: Prop :=
      forall src tgt
        (SIM: sim src tgt)
        (TERM: Configuration.is_observable tgt),
      exists src',
        <<STEP: tausteps src src'>> /\
        <<TERM: Configuration.is_observable src'>>.

    Definition TERMINAL: Prop :=
      forall src tgt
        (SIM: sim src tgt)
        (TERM: Configuration.is_terminal tgt),
      exists src',
        <<STEP: tausteps src src'>> /\
        <<TERM: Configuration.is_terminal src'>>.
  End Simulation.

  Structure t (prog_src prog_tgt:Program.t) := mk {
    sim: forall (src tgt:Configuration.t), Prop;

    load: LOAD prog_src prog_tgt sim;
    step: STEP sim;
    observable: OBSERVABLE sim;
    terminal: TERMINAL sim;
  }.
End Simulation.
