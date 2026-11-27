# Implementation experiments

| Question | Read |
|---|---|
| What do packed representation and native execution cost? | [Packed experiments](packed-experiments.md), [native experiments](native-experiments.md), [optimization comparisons](optimizations.md) |
| Where does merge spend its time? | [Measured phases](merge-phases.md) separates selecting winners from emitting their bytes. [Fused merge](fused-merge.md) studies combining the two. [Fast-path refinement](fast-path-refinement.md) explains which optimized outputs agree with the specification. |
| How can Lean produce packed bytes efficiently? | [Emission experiments](emission-experiments.md), [stock builder](stock-builder.md), [fixed copy](fixed-copy.md) and [scoped builder](scoped-builder.md). The scoped prototype fills a private buffer using a separate native backend. |
| How do versioned runs merge at a snapshot floor? | [Compaction experiment](compaction.md) compares the Lean kernels with a Rust control. For the table that uses checked runs, see [storage tables](../../lean/Alvoki/Storage/Table/README.md). |
