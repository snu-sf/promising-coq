# A Promising Semantics for Relaxed-Memory Concurrency

[This branch](https://github.com/snu-sf/promising-coq/tree/popl17ae) is the [artifact](http://conf.researchr.org/track/POPL-2017/ArtifactEvaluation) for the POPL 2017 Submission #65: A Promising Semantics for Relaxed-Memory Concurrency.

## Build

- Requirement: [Coq 8.5pl2](https://coq.inria.fr/download), Make, Rsync.

- Initialization

        git clone https://github.com/snu-sf/promising-coq.git
        cd promising-coq
        git checkout popl17ae
        git submodule init
        git submodule update

  If you have a problem with Git, please download [promising-coq.zip](http://sf.snu.ac.kr/promising/release/promising-coq.zip). You can `make` and `./build.sh` after extracting it.

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development in the `.build` directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).

  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:

    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## Difference from the POPL Submission

Since the POPL submission, we changed the Coq development as follows. We are revising the paper for the camera-ready deadline. Here is an [intermediate draft for the paper](http://sf.snu.ac.kr/promising/release/promising.pdf).

- We removed SC accesses.

  After the submission, we found out that compilation of SC accesses (reads/writes/updates) to Power is unsound. In the author response, we clearly stated that "we must retract the claim that our semantics of SC accesses is implementable on Power", and "if we do not find a fix, we will remove SC accesses (reads, write and updates) from our model and explain clearly up front that SC accesses and consume reads are future work."

  We did not update the paper draft yet.

- We changed the conditions for release writes/updates and release fences.

  After the submission, we removed an asymmetry of the conditions for release writes/updates and fences on promises. We accordingly adapted the existing proofs of the "Results" (Section 5).

  We already updated the paper draft.  To summarize, we changed the semantics of release writes/updates and fences as follows:

    + Writes/Updates: The POPL submission version requires that, to release-write a message to `x`, the writing thread should not have any promise on `x`. Instead, the current version requires that any promise on `x` should have the bottom released view.

    + Fences: The current version requires that any promises by the thread issuing a release fence, should have the bottom released view.  The POPL submission version did not require that.

- Minor miscellaneous changes

  We bumped the Coq version, changed names for better consistency, etc. No update is needed for the paper.

## References

### Model

- `lib` and `src/lib` contains libraries not necessarily related to the relaxed-memory concurrency.

- `src/lang`: Model (Section 2-4)
    + `Language.v`: abstract interface of the programming languages
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 3)
    + `TView.v`: the rule for thread views (`*-HELPER` rules in Figure 3)
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
    + Reorderings: `reorder_sim_stmts` (`Reorder.v`) and `reorder_release_fenceF_sim_stmts` (`ReorderReleaseFenceF.v`)
      The latter proves the reordering of `F_rel; *` is proved, while the former proves everything else.
    + Merges: `Merge.v`
    + Unused Plain Read Elimination: `unused_load_sim_stmts` (`UnusedLoad.v`)
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
