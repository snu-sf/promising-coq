# A Promising Semantics for Relaxed-Memory Concurrency

Jeehoon Kang, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis, Derek Dreyer.

Proceedings of the 44th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages ([POPL 2017](http://conf.researchr.org/home/POPL-2017)).

Please visit the [project website](http://sf.snu.ac.kr/promise-concurrency/) for more information.

## Build

Requirements: opam (>=2.0.0), OCaml 5.x, Rocq 9.0+, dune (>=3.21)

1. Create a local opam switch and install dependencies
```
opam switch create . ocaml-base-compiler.5.4.0 --no-install
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -y rocq-promising . --no-action
opam install -y --deps-only rocq-promising
```

2. Build the project
```
dune build
```

## IDE (VSCode)

After building the project, the `_CoqProject` file is pre-configured so that
VSCode extensions (VsCoq or coq-lsp) can find the compiled files:

```
-R _build/default/src Promising
```

Make sure to run `dune build` first so that the compiled `.vo` files exist
in `_build/default/src/`.

## References

### Model

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

- `src/drf`: DRF Theorems (Section 5.3)
    + Promise-Free DRF (Theorem 1): `drf_pf` (`DRF_PF.v`)
    + We did not formalize DRF-RA (Theorem 2) and DRF-SC (Theorem 3) yet.

- `src/invariant`: An Invariant-Based Program Logic (Section 5.4)
    + Soundness: `sound` (`Invariant.v`)
