"""Rerun v3 candidates in mixed order on one core with exact output checks."""

import argparse
import csv
import os
from pathlib import Path
import random
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--case", action="append", nargs=3, required=True, metavar=("LABEL", "BINARY", "MODE"))
    parser.add_argument("--size", type=int, default=1_000_000)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--trials", type=int, default=3)
    args = parser.parse_args()
    if min(args.size, args.rounds, args.trials) < 1:
        parser.error("size, rounds and trials must be positive")

    sys.path.insert(0, str(args.repo.resolve() / "benchmarks"))
    from compaction import encoded, invoke, oracle, tag, workloads

    cases = [(label, Path(binary).resolve(strict=True), mode) for label, binary, mode in args.case]
    pipeline_modes = {"pipeline", "pipeline-rows", "cursor-pipeline"}
    if len({label for label, _, _ in cases}) != len(cases):
        parser.error("case labels must be unique")
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(6589)
    with tempfile.TemporaryDirectory() as temp, args.out.open("w", newline="") as stream:
        paths = tuple(Path(temp) / name for name in ("left", "right", "out"))
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "mode", "round", "position", "trial", "ns",
                         "checksum", "cpu", "retained", "spans"))
        for workload, left, right, floor, snapshot in workloads(args.size):
            paths[0].write_bytes(encoded(left))
            paths[1].write_bytes(encoded(right))
            retained, checksum, _, spans, _ = oracle(left, right, floor, snapshot)
            expected = encoded(retained)
            for label, binary, mode in cases:
                if mode in pipeline_modes:
                    continue
                paths[2].unlink(missing_ok=True)
                invoke(binary, f"check-{mode}", paths, floor, snapshot)
                if paths[2].read_bytes() != expected:
                    raise ValueError(f"{workload}/{label}: bytes differ from the independent oracle")
            for round_id in range(1, args.rounds + 1):
                order = rng.sample(cases, len(cases))
                for position, (label, binary, mode) in enumerate(order, 1):
                    wanted = checksum if mode in pipeline_modes else tag(expected)
                    samples = invoke(binary, mode, paths, floor, snapshot, args.trials + 1).stdout.splitlines()
                    if len(samples) != args.trials + 1:
                        raise ValueError(f"{workload}/{label}: wrong sample count")
                    for trial, sample in enumerate(samples):
                        elapsed, result = map(int, sample.split())
                        if elapsed <= 0 or result != wanted:
                            raise ValueError(f"{workload}/{label}: invalid timing or checksum")
                        if trial:
                            writer.writerow((args.size, workload, label, mode, round_id, position, trial, elapsed,
                                             result, cpu, len(retained), spans))
                stream.flush()


if __name__ == "__main__":
    main()
