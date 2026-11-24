import argparse
import csv
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def checked_controls(probe):
    env = dict(os.environ)
    env.pop("LEAN_ABORT_ON_NONLINEAR", None)
    ordinary = subprocess.run([probe, "shared", "16"], env=env, check=True,
                              text=True, capture_output=True)
    assert ordinary.stdout.strip() == "7 -> 9"
    diagnostic = dict(env, LEAN_ABORT_ON_NONLINEAR="1")
    for mode, capacity, expected in (("unique", "16", "9"), ("growth", "1", "size 2, appended 9")):
        result = subprocess.run([probe, mode, capacity], env=diagnostic, check=True,
                                text=True, capture_output=True)
        assert result.stdout.strip() == expected
    for mode, capacity in (("shared", "16"), ("shared-growth", "1")):
        result = subprocess.run([probe, mode, capacity], env=diagnostic, text=True, capture_output=True)
        assert result.returncode and "marked by `markLinear` was used non-linearly" in result.stderr, mode
    print("Unique overwrite and forced growth passed; deliberate sharing triggered the native diagnostic.")


def main():
    parser = argparse.ArgumentParser(description="Check native writes to marked ByteArray destinations.")
    parser.add_argument("repository", type=Path)
    parser.add_argument("build", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--sizes", type=int, nargs="+", default=[1000, 100_000, 1_000_000])
    args = parser.parse_args()
    if min(args.sizes) < 1:
        parser.error("sizes must be positive")

    sys.path.insert(0, str(args.repository / "benchmarks"))
    import compaction
    import stock_builder
    from generate import block, dataset
    from support import MASK, compactions, invoke_replay, merged_records, set_inputs

    checked_controls(args.build / "linear-control")
    os.environ["LEAN_ABORT_ON_NONLINEAR"] = "1"
    binaries = args.build / ".lake/build/bin"
    replay = binaries / "alvoki-merge-phases"
    compact = binaries / "alvoki-compaction"
    native = binaries / "alvoki-native"
    replay_modes = ("replay-write", "replay-spans", "replay-prepared", "replay-prepare-and-write")
    stock_builder.MODES = [(mode, replay, mode) for mode in replay_modes]
    compaction.BINARIES = {"lean-marked": compact}

    with TemporaryDirectory() as temp, args.out.open("w", newline="") as evidence:
        directory = Path(temp)
        stock_builder.cases(directory)
        left_path, right_path, trace_path, output = [
            directory / name for name in ("left", "right", "trace", "output")
        ]
        compaction.checks((left_path, right_path, output))
        report = csv.writer(evidence, lineterminator="\n")
        report.writerow(("suite", "profile", "records", "mode", "output_bytes", "result"))
        for size in args.sizes:
            records = dataset(size)
            inputs = (left_path, right_path, trace_path)
            for profile, (left, right) in compactions(records):
                set_inputs(inputs, left, right)
                expected = block(merged_records(left, right))
                for mode in replay_modes:
                    invoke_replay(replay, f"check-{mode}", inputs, output)
                    assert output.read_bytes() == expected, (profile, size, mode)
                    report.writerow(("v1-replay", profile, size, mode, len(expected), "exact"))
            for profile, left, right, floor, snapshot in compaction.workloads(size):
                expected, *_ = compaction.check_case((left_path, right_path, output),
                                                     left, right, floor, snapshot)
                for mode in ("rows", "spans"):
                    report.writerow(("v3-compaction", profile, size, mode, len(expected), "exact"))
            left_path.write_bytes(block(records))
            expected = block([(key, value ^ MASK) for key, value in records])
            subprocess.run([native, "check-copy-dense", left_path, right_path, output, "1"],
                           check=True, capture_output=True)
            assert output.read_bytes() == expected, size
            report.writerow(("v1-rewrite", "dense", size, "copy-words", len(expected), "exact"))
            print(f"All marked writers produced exact bytes at {size:,} input records.")


if __name__ == "__main__":
    main()
