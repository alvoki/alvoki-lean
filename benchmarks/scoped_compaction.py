"""Run the existing packed v3 oracle and workload suite with scoped outputs."""

from compaction import BINARIES, ROOT, main


if __name__ == "__main__":
    lean = ROOT / "lean/.lake/build/bin"
    BINARIES["lean-fixed"] = lean / "alvoki-compaction-fixed"
    BINARIES["lean-scoped"] = lean / "alvoki-compaction-scoped"
    BINARIES["lean-scoped-branchless"] = lean / "alvoki-compaction-scoped-branchless"
    main()
