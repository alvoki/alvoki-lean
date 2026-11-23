# Alvoki repository review

**23 November 2026** · Reviewed [`1bd2625`](https://github.com/alvoki/alvoki-lean/tree/1bd2625e14ba1e62d0beb172cd149b0977046eb8), from format and proof modules through the Lean and Rust executables, Python fixtures, build scripts, and measurement artifacts.

Alvoki has a reproducible research history and enough evidence to select a stock-Lean core. The main architectural problem is that the repository is organized by experiment round. The current packed reader, merge strategies, benchmark harnesses, and some generic proofs sit in those layers. A new storage feature would have to choose between overlapping APIs and reconstruct their guarantees from several reports. The next structural milestone should make one validated packed-run API easy to find, build, prove against, and compare with the historical baselines. [Current module map](architecture.md) · [Proof coverage](verification-status.md)

## What is working

- **A small, portable reference format.** Version 1 uses two little-endian header words and a contiguous sequence of fixed-size records. Strict key order makes point and range lookup and right-biased merge easy to specify. Version 2 provides an explicit columnar experiment. The pinned baseline and independent Python fixtures give future changes a common reference. [Format specification](specifications.md) · [Fixtures](../fixtures/generate.py)
- **Credible performance comparisons.** The project retains earlier trials, adds matched Rust controls when workloads change, and records VM and compiler details. The output replay experiments separate selection from writing. The direct-scan suite adds use-case and peak-memory comparisons. Keep the old baselines and experiment drivers available when extracting shared code. [Replay experiment](merge-phases.md) · [Fused merge experiment](fused-merge.md) · [Trial files](../benchmarks)
- **Useful proof and runtime separation.** The lower-bound and byte-access proofs have concrete executable targets. The stock builder has an append contract. Runtime experiments live under their own sources and use separately linked binaries. This supports independent decisions about the stock implementation, source guarantees, and future toolchain work. [Proof coverage](verification-status.md) · [Runtime experiments](../lean/runtime-experiment)

## Findings

### 1. Keep shape-checked replay behind the experiment boundary

**High priority before API promotion.** `ReplayPlan.valid` checks opcodes, cursor bounds, and complete consumption. The check has no access to the keys. A trace can legally consume both runs while emitting out of order, or use a collision opcode for unequal keys. `replayWrite_refines` covers the exact bytes selected by the supplied trace. Exact benchmark output is protected by oracle-generated traces and independent expected bytes. [Validator](../lean/MergePhases.lean#L44) · [Replay theorem and plan](../lean/MergePhases.lean#L157) · [CLI check](../lean/MergePhasesMain.lean#L38)

I ran `alvoki-merge-phases` with the one-record runs `[(10, 100)]` and `[(0, 200)]`. In each of `check-replay-write`, `check-replay-prepared`, and `check-replay-spans`, trace bytes `[0, 1]` returned success and wrote `[(10, 100), (0, 200)]`. Trace `[2]` returned success and wrote only `[(0, 200)]`. The online merge returned the ordered union `[(0, 200), (10, 100)]` for both trials. [Replay output modes](../lean/MergePhasesMain.lean#L72)

Name the current invariant for cursor and opcode validity and keep replay internal to benchmarking. If a future caller needs a reusable merge plan, construct it from a verified selector or validate the key comparisons as well. Keep these two traces as regression cases at any boundary that promises valid sorted output.

### 2. Put record bounds and sortedness at the public interface

**High priority before API promotion.** `parseView` checks the byte layout and order before constructing a view. The public `View.key` and `View.value` accessors take an unrestricted `USize` and perform wrapping offset arithmetic, with out-of-extent reads using the reader's zero result. In a one-record v1 view containing key 10, `view.key view.count` returned 0 and `view.key (USize.ofNat (2^60))` returned 10 on x86-64 because multiplication by 16 wrapped to zero. The Rust baseline's public `record` also assumes a valid index and can panic on a slice access. Existing loops maintain their own cursors. [Lean accessors](../lean/Optimizations.lean#L99) · [Rust accessor](../rust/src/lib.rs#L39)

Give callers checked access or an index with a bound, and keep the machine accessors private. Some cached merge loops fetch the next head on advance, even when that advance exhausts the run. Subsequent cursor checks prevent use of the sentinel. Preserve that invariant or guard the fetch when extracting the internal API, then check the generated hot loop. Carry parser facts about length, offsets, and strict logical key order so search and merge proofs can use them. Tie the accepted input to a simple logical record sequence. This is the bridge from the existing lower-bound and byte proofs to claims about data read from disk. [Layout parser](../lean/Optimizations.lean#L149) · [Search refinement](../lean/OptProofs.lean) · [Cached heads](../lean/FusedMerge.lean#L34) · [Version-1 run wrapper](../lean/PackedRun.lean)

### 3. Extract one stock core and make experiments depend on it

**High priority.** `PackedRun` depends on the entire `Optimizations` module to obtain the checked view and word helpers. `NativeTune` owns both scan/encode probes and merge helpers used by the latest experiment. The generic byte proofs in `ScopedBytesProofs` import `MergePhases` and transitively compile the packed and native experiment stack. The default Lake executable still targets the original `Block` path. As a result, build defaults, proof dependencies, and performance baselines each present a different entry point. [Lake targets](../lean/lakefile.toml) · [Packed run](../lean/PackedRun.lean) · [Native tuning](../lean/NativeTune.lean) · [Builder proof imports](../lean/ScopedBytesProofs.lean#L1)

Use these boundaries, in dependency order:

| Layer | Responsibility | First extraction |
|---|---|---|
| Bytes | Fixed-width little-endian reads, byte extents, append-only builder, and their proofs | Let the builder proofs import the builder alone. Move the replay-specific lemmas next to replay. |
| Blocks and runs | Version-1 codec, validated view, lookup and range API, v1 runs, and parser refinement | Pull the reader and view out of the optimization harness. Keep the columnar implementation with its experiment until there is a workload that needs it. |
| Merge and scan | Logical right-biased union, simple reference merge, one measured stock emitter, and a direct fold where useful | Prove the merge and scan against the same logical union. Promote a fast path only once the chosen implementation has the required contract and pipeline evidence. |
| Benchmarks and runtime prototypes | Historical drivers, candidate variants, Rust controls, replay, and custom native lowerings | Depend on shared library and fixture code. Keep ABI-dependent variants opt-in. |

Start with import cuts and stable targets. Retain existing entry points during the transition, and check generated code and matched measurements whenever sharing code changes specialization or linkage. The representative operations for the first public surface are parse, lookup, range fold, and merge of version-1 runs. Broader storage-engine features need their own format and correctness contracts.

### 4. Give the supported paths one correctness gate

**High priority.** `scripts/reproduce.sh` checks the original proofs, the Verus search, and baseline fixtures. Optimized proofs, stock builder proofs, and recent native paths have their own scripts. There is no tracked CI workflow to assemble these checks. Many Python checks also depend on `assert`. I injected a wrong byte file into `fused_merge.check_merge`. Python rejected it with assertions enabled and returned successfully with `PYTHONOPTIMIZE=1`. This can allow a suite to report success without doing its comparisons. [Baseline reproduction](../scripts/reproduce.sh) · [Stock builder runner](../scripts/stock-builder.sh) · [Fused comparison](../benchmarks/fused_merge.py#L37)

Add a single stock correctness command and run it in CI on the supported Linux x86-64 toolchains. Include the baseline, optimized search and builder proof audits, `leanchecker`, the Verus core, and stock exact-output tests for read, write and merge. Use explicit comparison failures or reject Python optimization at the entry point. Keep runtime prototypes as a separate opt-in job and keep timing assertions out of CI. For portable setup, pin or record the installer and verifier artifacts as well as version labels, and check the resolved Verus release even when reusing its extracted directory. [Pinned setup](../scripts/bootstrap.sh)

### 5. Make benchmark fixtures and timed scopes reusable

**Medium priority.** The Python suites already share functions, but do so by importing other experiment drivers. `fused_merge` imports the profile generator from `scoped_builder`, which imports spans from `native`, and both depend on `packed` and `run`. Rust has several independent control binaries with similar algorithms and different timed scopes. This makes it easy to pick up changes to global paths, fixture behavior, or a control while reproducing an older comparison. [Fused driver imports](../benchmarks/fused_merge.py#L1) · [Scoped driver imports](../benchmarks/scoped_builder.py#L1) · [Rust controls](../rust/src/bin)

Extract common fixture/oracle, command invocation, and reporting code into small shared modules. Keep each timed kernel explicitly named and its release build visible. Record operation, output contract, included phases, layout, CPU, revisions and flags with each new timing batch. Keep old CSVs intact. Add a matched span-capable Rust control when drawing conclusions from stock Lean's disjoint or clustered span results against per-record Rust. The prepared-replay comparison already documents that distinction. [Stock replay scopes](stock-builder.md#performance) · [Direct and materialized scopes](fused-merge.md#direct-merged-scans)

### 6. Clarify what the repository delivers

**Medium priority.** The README historically gave equal space to successive experiments. Start with the supported format and correctness entry point, then use an experiment index and the technique guide to find variants. When a stock core is selected, document its supported platform and its proof boundary in the first screen of the README. If Alvoki is intended for reuse outside the project, choose a repository license before inviting downstream adoption. [README](../README.md) · [Architecture](architecture.md) · [Technique guide](high-performance-lean.md)

## Recommended order of work

| Step | Deliverable | Completion check |
|---|---|---|
| 1 | A stock smoke command, explicit fixture failures, and two replay counterexamples documented or encoded at the proper boundary | A failed comparison fails under the supported invocation, and a single command exercises the current stock proof and fixture targets. |
| 2 | Standalone byte-builder proofs and one validated v1 run API with safe indexing | The generic proofs build without the merge experiment. Parser acceptance establishes size, extent, and strict key-order facts for the view. |
| 3 | A common right-biased union model, one stock materialized merge, and a direct fold that refines the same model | Exact fixtures and source proofs check output order, collision behavior and fold equivalence. Matched pipeline measurements guide the materialized default. |
| 4 | A small shared harness, corpus-based workload checks, and a standard Lean write optimization experiment | Old results can still be located and reproduced. New results cover realistic span distributions. Any toolchain candidate reproduces the stock builder contract and keeps the same checks for aliasing, growth, clipping, and initialization. |

## Checks run for this review

All nine default suites passed on the existing pinned Linux x86-64 tools, including the Lean and Verus proof checks. The table summarizes the scope of each independent script. I ran fixture and proof modes without regenerating performance measurements.

| Script | Result |
|---|---|
| [`reproduce.sh`](../scripts/reproduce.sh) | Baseline Lean and Verus checks, 9 valid and 8 malformed fixtures across three binary configurations |
| [`optimize.sh`](../scripts/optimize.sh) | Optimized Lean proof checks, 14 valid and 14 malformed layout fixtures |
| [`packed.sh`](../scripts/packed.sh) | 8 storage and 9 exact merge fixtures |
| [`native.sh`](../scripts/native.sh) | 13 scan/encode and 21 exact merge fixtures |
| [`merge-phases.sh`](../scripts/merge-phases.sh) | 11 exact merge and checksum fixtures, 5 malformed traces |
| [`fixed-copy.sh`](../scripts/fixed-copy.sh) | Fixed-width output checks across four binaries |
| [`scoped-builder.sh`](../scripts/scoped-builder.sh) | Fixed-width output checks, 8 exact builder fixtures and 5 malformed traces |
| [`stock-builder.sh`](../scripts/stock-builder.sh) | Stock Lean proof checks, 8 exact byte fixtures and 5 malformed traces |
| [`fused-merge.sh`](../scripts/fused-merge.sh) | 22 exact-output, scan, and pipeline fixtures |
