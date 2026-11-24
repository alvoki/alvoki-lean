"""Run Alvoki's existing exact fixtures and timing suites with alternate toolchains."""

import argparse
import csv
import os
from pathlib import Path
import random
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
import compaction
import merge_phases
from generate import WORD_MASK, block, dataset
from support import merged_records, set_inputs, split_spans, tag


def repeat_case(writer, rng, cpu, rounds, suite, size, workload, mode, binaries, run, expected):
    for round_number in range(1, rounds + 1):
        order = list(binaries.items())
        rng.shuffle(order)
        for position, (label, binary) in enumerate(order, 1):
            samples = run(binary)
            assert len(samples) == 4 and all(seen == expected for _, seen in samples)
            for trial, (elapsed, seen) in enumerate(samples[1:], 1):
                writer.writerow((suite, size, workload, mode, label, round_number, position,
                                 trial, elapsed, seen, cpu))


def run_focused(directory, out, sizes, rounds):
    """Repeat outlying cases in randomized, shorter batches to limit time drift."""
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(1749)
    left, right, trace, output = (directory / name for name in ("left", "right", "trace", "out"))
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("suite", "records", "workload", "mode", "variant", "round", "position",
                         "trial", "ns", "tag", "cpu"))
        for size in sizes:
            records = dataset(size)
            half, shift = size // 2, size // 8
            workloads = [
                ("alternating", split_spans(records, 1)),
                ("collision-heavy", (records[:half], [(key, value ^ WORD_MASK)
                 for key, value in records[shift:shift + size - half]])),
            ]
            for profile, (a, b) in workloads:
                paths = (left, right, trace)
                set_inputs(paths, a, b)
                expected = block(merged_records(a, b))
                for binary in merge_phases.BINARIES.values():
                    merge_phases.invoke(binary, "check-replay-write", paths, output)
                    assert output.read_bytes() == expected, binary
                repeat_case(writer, rng, cpu, rounds, "v1", size, profile, "replay-write",
                            merge_phases.BINARIES,
                            lambda binary: merge_phases.invoke(binary, "replay-write", paths, output, 4),
                            tag(expected))
            del records, workloads, a, b
            paths = (left, right, output)
            for profile, a, b, floor, snapshot in compaction.workloads(size):
                expected, checksum, *_ = compaction.check_case(paths, a, b, floor, snapshot)
                modes = ("rows", "pipeline") if profile in ("range-ingest", "hot-updates") else ("pipeline",)
                for mode in modes:
                    def run(binary):
                        result = compaction.invoke(binary, mode, paths, floor, snapshot, 4)
                        return [tuple(map(int, line.split())) for line in result.stdout.splitlines()]

                    repeat_case(writer, rng, cpu, rounds, "v3", size, profile, mode, compaction.BINARIES,
                                run, tag(expected) if mode == "rows" else checksum)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", action="append", nargs=2, metavar=("LABEL", "BIN_DIR"),
                        required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--sizes", type=int, nargs="+", default=[100_000, 1_000_000])
    parser.add_argument("--trials", type=int, default=9)
    parser.add_argument("--focused", action="store_true", help="run focused interleaved batches instead")
    args = parser.parse_args()

    binaries = {label: Path(path).resolve() for label, path in args.toolchain}
    if len(binaries) != len(args.toolchain) or "rust" not in binaries:
        parser.error("specify distinct labels and supply the rust control")
    if min(args.sizes) <= 0 or args.trials <= 0:
        parser.error("sizes and trial count must be positive")
    for suite, executable in ((compaction, "alvoki-compaction"),
                              (merge_phases, "alvoki-merge-phases")):
        suite.BINARIES = {label: binary_dir / executable for label, binary_dir in binaries.items()}
        for binary in suite.BINARIES.values():
            if not binary.is_file():
                parser.error(f"missing executable: {binary}")

    args.out.mkdir(parents=True, exist_ok=True)
    if args.focused:
        with tempfile.TemporaryDirectory() as scratch:
            run_focused(Path(scratch), args.out / "interleaved-trials.csv", args.sizes, args.trials)
        return
    with tempfile.TemporaryDirectory() as scratch:
        directory = Path(scratch)
        merge_phases.check_cases(directory)
        merge_phases.run(directory, args.out / "v1-merge-trials.csv", args.sizes, args.trials)
    with tempfile.TemporaryDirectory() as scratch:
        paths = tuple(Path(scratch) / name for name in ("left", "right", "out"))
        compaction.checks(paths)
        compaction.run(paths, args.out / "v3-compaction-trials.csv", args.sizes, args.trials)


if __name__ == "__main__":
    main()
