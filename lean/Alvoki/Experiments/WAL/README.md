# WAL components

This directory contains independent single-file and segmented WAL experiments. Start with the [segmented WAL guide](Segmented/README.md), which describes its format, API, assumptions, tests, and current limits. The [single-file recovery proofs](Proofs/README.md) and [segmented proofs](Segmented/README.md#verification) retain useful counterexamples about torn tails, uncertain append outcomes, recovery retries, and the limits of checksum-based detection.

These models do not make native refinement automatic. In particular, successful file and directory synchronization, exact reads, stable directory ownership, descriptor lifetime, and the joint file/name state after a crash remain explicit filesystem premises. See [WAL recovery notes](../../../../docs/design/wal-recovery.md) for the relevant counterexamples and premise boundaries.
