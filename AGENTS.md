# Alvoki development

- Read `docs/progress.md` before resuming. Update it after meaningful work.
- Run `bash scripts/reproduce.sh` from the repository root. Pin compatible toolchains and regenerate benchmark artifacts when measurement code changes.
- Keep the binary format and behavioral specification consistent across implementations. Add differential coverage when changing observable behavior.
- Preserve benchmark workload equivalence, release compilation, deterministic data, and the original raw timings. Record platform, commands, and benchmark changes.
- Keep formal contracts explicit. Do not weaken a specification to make a proof pass, and do not use `sorry`, `admit`, custom axioms, or proof steps that depend on native execution. Audit the actual theorem dependencies.
- Keep verification-only history and evidence out of the runtime path. Benchmark the affected native release workloads when proof-driven changes add or alter runtime work. See [performance requirements](docs/proof-roadmap.md#performance-requirements-for-verified-paths).
- Review executable behavior, proof assumptions, fault coverage, and performance at milestone boundaries and during longer milestones. Add confirmed findings and new proof obligations to the roadmap with their priority and completion criteria.
- Commit and push each completed and verified milestone to the repository's remote branch. Keep unfinished work outside the published commit.
- Document which implementation a theorem applies to and identify remaining refinement, runtime, compiler, and environment assumptions.
