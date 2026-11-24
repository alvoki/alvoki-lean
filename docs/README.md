# Alvoki documentation

- **Run the engine.** Install the pinned tools, try a persistent write and reopen, and reproduce the checks. [Getting started](getting-started.md)
- **Understand storage.** Follow a write through the WAL, see how checkpoints and recovery work, and look up the file formats. [Architecture](architecture.md#sequential-storage) · [Formats and behavior](specifications.md#wal-and-checkpoint-manifest)
- **Understand the proof boundary.** See the properties Lean checks today, the native assumptions they use, and the remaining end-to-end work. [Verification status](verification-status.md#storage-engine-guarantees) · [Proof roadmap](proof-roadmap.md)
- **Follow development.** See engine priorities and the results of recent proof and implementation work. [Roadmap](roadmap.md) · [Progress](progress.md) · [Proof index](proof-index.md)
- **Reproduce performance experiments.** Find workloads and measurements for the engine and the separate packed Lean, Rust and native experiments. [Benchmarks](benchmarks.md) · [High-performance Lean](high-performance-lean.md)
