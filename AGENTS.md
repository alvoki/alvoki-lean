# Alvoki development

- Read `docs/progress.md` before resuming. Keep it readable in one sitting. Replace superseded status with what now composes, the next open premise and the last verified baseline. Before replacing a note, carry forward any still-open obligation to the roadmap, an enduring assumption to its contract, or a counterexample to the relevant proof or regression test. Git history retains the delivery narrative.
- Run `bash scripts/reproduce.sh` from the repository root. Pin compatible toolchains and regenerate benchmark artifacts when measurement code changes.
- Keep the binary format and behavioral specification consistent across implementations. Add differential coverage when changing observable behavior.
- Preserve benchmark workload equivalence, release compilation, deterministic data, and the original raw timings. Record platform, commands, and benchmark changes.
- Keep formal contracts explicit. Do not weaken a specification to make a proof pass, and do not use `sorry`, `admit`, custom axioms, or proof steps that depend on native execution. Audit the actual theorem dependencies.
- Follow the [proof-engineering guidance](docs/proof-index.md#how-to-structure-a-proof). Start from an executable guarantee, prove local refinements at shared boundaries, and identify the theorem that composes them or the remaining composition obligation.
- Use the [proof architecture](docs/proof-architecture.md) for substantial proof work. Assign the parent claim, missing obligation, source path, allowed assumptions, facts to derive, downstream consumer, and acceptance checks before writing the proof. Review the specification with a concrete adversarial execution as well as reviewing the proof and its executable coverage.
- Work backwards from a real consumer. If adding an operation outcome requires revisiting every recovery outcome, inspect the state passed between them. Test it on a partial effect followed by a different continuation. After migrating callers, retire proofs whose guarantees are fully covered.
- Keep verification-only history and evidence out of the runtime path. Benchmark the affected native release workloads when proof-driven changes add or alter runtime work. See [performance requirements](docs/proof-roadmap.md#performance-requirements-for-verified-paths).
- Review executable behavior, proof assumptions, fault coverage, and performance at milestone boundaries and during longer milestones. Add confirmed findings and new proof obligations to the roadmap with their priority and completion criteria.
- Document which implementation a theorem applies to and identify remaining refinement, runtime, compiler, and environment assumptions.

## Agent work and review

- Aim to keep five subagents working in parallel on independent roadmap tasks. While a shared boundary is changing, give it one owner. Split work by independent producers or consumers once their interface is stable. Prioritize the end-to-end crash refinement in the proof roadmap.
- Pin independent Lean readability reviews to a commit and a concrete task or set of files. Favor straightforward code that makes mistakes harder. Introduce an abstraction only when it simplifies the code, and use comments to explain subtle reasons and invariants.
- Give each write task its own worktree and local branch. The task agent commits its candidate there for review.
- The coordinator and an independent reviewer review the exact candidate diff. The task agent addresses findings, then the coordinator runs the applicable integration checks. Use focused module and axiom checks during iteration. Run the applicable integration checks on the reviewed candidate before pushing. For a prose-only change, check its claims, links and the identity of the verified code. The coordinator alone pushes integrated work, one verified milestone at a time.
- After each push, the coordinator sends the new `main` commit to the active agents. Agents working on dependent changes rebase their task branches and rerun the affected checks before returning their candidates.
