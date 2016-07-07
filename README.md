# A Promising Semantics for Relaxed-Memory Concurrency

## Build

- You need Coq 8.5, and Make.
- You can build by the `make` command in the root directory.

## References

### Model

- `lib`, `src/lib` and `src/hahn` contains libraries not necessarily related to the relaxed-memory concurrency.
    + Hahn is a library with many lemmas about relations, transitive closures, etc.

- `src/lang`: Model (Section 2-4)
    + `Language.v`: abstract interface of the programming languages
    + `Memory.v`: memory model (`MEMORY: *` rules in Figure 3)
    + `Commit.v`: the rule for thread views (`*-HELPER` rules in Figure 3)
    + `Thread.v`: thread and its execution (`READ`, `WRITE`, `UPDATE`, `FENCE`, `SYSTEM CALL`, `SILENT`, `PROMISE` rules in Figure 3)
    + `Configuration.v`: configuration (machine state) and its execution (`MACHINE STEP` rule in Figure 3)
    + `Behavior.v`: the behaviors of a configuration

- `src/while` Toy "while" language
  This language provides the basis for the optimization & compilation results.

- `src/opt`: Compiler Transformations (Section 5.1)
    + Trace-Preserving Transformations: Lemma `sim_trace_sim_stmts` (`SimTrace.v`)
    + Strengthening: Lemma `sim_stmts_instr` (`SimTrace.v`)
    + Reorderings: `Reorder.v` (Lemma `reorder_sim_stmts`) and `ReorderReleaseFenceF.v` (Lemma `reorder_release_fenceF_sim_stmts`)
    + Merges: `Merge.v` (all the Lemmas in this file)
    + Unused Plain Read Elimination: Lemma `unused_load_sim_stmts` (`UnusedLoad.v`)
    + Proof Technique:
        * Simulation Relation: `Simulation.v` (Definition `sim` for the configuration simulation, and `sim_thread` for the thread simulation)
        * Adequacy: `Adequacy.v` (from the configuration simulation to the behaviors)
        * Composition: `Composition.v` ("horizontally" composing configuration simulations for disjoint configurations)
        * Compatibility: `Compatibility.v` (Lemmas `sim_stmts_frame`, `sim_stmts_nil`, `sim_stmts_seq`, `sim_stmts_ite`, `sim_stmts_dowhile`)

- `src/axiomatic`: Compilation to TSO and Power (Section 5.2)
    + `model.v` and `Machine.v`: Definition of the axiomatic machine..
    + `SimRel.v`: Definition of the simulation relation.
    + `sim.v`: Proof of the axiomatic machine is weaker than the operational one.
       This proof is complete except for the case of update steps, which is admitted.

- `src/drf`: DRF Theorems (Section 5.3)
    + Promise-Free DRF (Theorem 1): Theorem `pi_consistent_step_pi` (`PIStep.v`) and Theorem `pi_consistent_pi_step_pi_consistent` (`PromiseFree.v`) collectively proves the promise-free DRF.
    + We did not formalize DRF-RA (Theorem 2) and DRF-SC (Theorem 3).

- `src/invariant`: An Invariant-Based Program Logic (Section 5.4)
    + Promise-free certification: Lemma `consistent_pf_consistent` (`Certification.v`)
      In certification, promise is useless.
    + Soundness: Lemma `sound` (`Invariant.v`)
