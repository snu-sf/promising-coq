# A Promising Semantics for Relaxed-Memory Concurrency

Jeehoon Kang, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis, Derek Dreyer.

Proceedings of the 44th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages ([POPL 2017](http://conf.researchr.org/home/POPL-2017)).

Please visit the [project website](http://sf.snu.ac.kr/promise-concurrency/) for more information.

## Build

- Requirement: [Coq 8.6](https://coq.inria.fr/download), Make, Rsync.

- Initialization

        git clone https://github.com/snu-sf/promising-coq.git
        cd promising-coq
        git submodule init
        git submodule update

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development in the `.build` directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References

### Model

- `lib` and `src/lib` contains libraries not necessarily related to the relaxed-memory concurrency.

- `src/lang`: Model (Section 2-4)
    + `Language.v`: abstract interface of the programming languages
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 3)
    + `Commit.v`: the rule for thread views (`*-HELPER` rules in Figure 3)
    + `Thread.v`: thread and its execution (`READ`, `WRITE`, `UPDATE`, `FENCE`, `SYSTEM CALL`, `SILENT`, `PROMISE` rules in Figure 3)
    + `Configuration.v`: configuration (machine state) and its execution (`MACHINE STEP` rule in Figure 3)
    + `Behavior.v`: the behaviors of a configuration

- `src/prop`: General properties on the memory model
    + Promise-free certification: `consistent_pf_consistent` (`PFConsistent.v`)
      In certification, promise is useless.

- `src/while` Toy "while" language
  This language provides the basis for the optimization & compilation results.

### Results

- `src/opt`: Compiler Transformations (Section 5.1)
    + Trace-Preserving Transformations: `sim_trace_sim_stmts` (`SimTrace.v`)
    + Strengthening: `sim_stmts_instr` (`SimTrace.v`)
    + Reorderings: `reorder_sim_stmts` (`Reorder.v`) and `reorder_release_fenceF_sim_stmts` (`ReorderRelFence.v`)
      The latter proves the reordering of `F_rel; *` is proved, while the former proves everything else.
    + Merges: `Merge.v`
    + Unused Plain Read Elimination: `elim_load_sim_stmts` (`ElimLoad.v`)
    + Read Introduction: `intro_load_sim_stmts` (`IntroLoad.v`)
    + Spliting acquire loads/updates and release writes/updates:
        `split_acquire_sim_stmts` (`SplitAcq.v`), `split_release_sim_stmts` (`SplitRel.v`), `split_acqrel_sim_stmts` (`SplitAcqRel.v`)
      These are used for the soundness proof of compilation to Power.

    + Proof Technique:
        * Simulation (Configuration): `sim` (`Simulation.v`) for the configuration simulation
        * Simulation (Thread): `sim_thread` (`SimThread.v`)
        * Adequacy (Configuration): `sim_adequacy` (`Adequacy.v`).  From the configuration simulation to the behaviors.
        * Adequacy (Thread): `sim_thread_sim` (`AdequacyThread.v`).  From the thread simulation to the configuration simulation.
        * Composition: `sim_compose` (`Composition.v`).  "horizontally" composing configuration simulations for disjoint configurations.
        * Compatibility: `sim_stmts_*` (`Compatibility.v`).

- `src/axiomatic`: definition of an axiomatic semantics, which is equivalent to our promise-free machine.
  This equivalence result is a stepping-stone for the compilation to TSO and Power (Section 5.2).
    + `model.v` and `Machine.v`: Definition of the axiomatic machine.
    + `SimRel.v`: Definition of the simulation relation.
    + `MsimG.v`, `GsimM.v`: the operational machine (`M`) simulates the axiomatic one (`G`), and vice versa.

- `src/drf`: DRF Theorems (Section 5.3)
    + Promise-Free DRF (Theorem 1): `drf_pf` (`DRF_PF.v`)
    + We did not formalize DRF-RA (Theorem 2) and DRF-SC (Theorem 3) yet.

- `src/invariant`: An Invariant-Based Program Logic (Section 5.4)
    + Soundness: `sound` (`Invariant.v`)
