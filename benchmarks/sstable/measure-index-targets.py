#!/usr/bin/env python3
"""Compare the recursive writer with a 64 KiB minimum above the leaf level."""
import argparse
import csv
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
BUILDER = Path("Alvoki/Experiments/SSTable/Recursive/Builder.lean")
PROGRAM = Path(".lake/build/bin/immutableSSTableCheck")

UNIFORM = "uniform"
UPPER = "upper-64k"
SIZES = (65_537, 1_000_000, 4_000_000)
TARGETS = ((4096, 1024), (4096, 4096), (16384, 16384))


def build(lean, output):
    subprocess.run(
        ["lake", "build", "immutableSSTableCheck"], cwd=lean, check=True
    )
    shutil.copy2(lean / PROGRAM, output)


def configure_upper_levels(lean):
    builder = lean / BUILDER
    text = builder.read_text()
    old = "      if page.shouldFlush ref writer.options.indexTarget then"
    new = (
        "      let target := if height = 1 then writer.options.indexTarget\n"
        "        else max writer.options.indexTarget (64 * 1024)\n"
        "      if page.shouldFlush ref target then"
    )
    if text.count(old) != 1:
        raise SystemExit("The recursive writer no longer matches the pinned benchmark source")
    builder.write_text(text.replace(old, new))


def write_samples(output, labels, samples):
    writer = csv.DictWriter(output, list(labels) + list(samples[0]), lineterminator="\n")
    if output.tell() == 0:
        writer.writeheader()
    writer.writerows(dict(labels, **sample) for sample in samples)
    output.flush()


def measure_queries(binaries, output, counts):
    for size_index, rows in enumerate(counts):
        for target_index, (data, leaf) in enumerate(TARGETS):
            policies = [UNIFORM] if leaf == 4096 else [UNIFORM, UPPER]
            if (size_index + target_index) % 2:
                policies.reverse()
            for policy in policies:
                output_text = subprocess.check_output(
                    [binaries[policy], "--bench-targets", str(rows), str(data), str(leaf)],
                    text=True,
                )
                samples = list(csv.DictReader(output_text.splitlines()))
                write_samples(output, {"policy": policy, "table_rows": rows}, samples)


def measure_rss(binaries, output, counts):
    for rows in (counts[0], counts[-1]):
        for data, leaf in (TARGETS[0], TARGETS[-1]):
            for trial in range(3):
                policies = (UNIFORM, UPPER) if trial % 2 == 0 else (UPPER, UNIFORM)
                for policy in policies:
                    with tempfile.TemporaryFile(mode="w+t") as sample_file:
                        child = subprocess.Popen(
                            [binaries[policy], "--bench-target-build", str(rows), str(data), str(leaf)],
                            stdout=sample_file,
                        )
                        _, status, usage = os.wait4(child.pid, 0)
                        child.returncode = os.waitstatus_to_exitcode(status)
                        if child.returncode:
                            raise subprocess.CalledProcessError(child.returncode, child.args)
                        sample_file.seek(0)
                        samples = list(csv.DictReader(sample_file))
                    write_samples(output, {
                        "policy": policy, "trial": trial, "max_rss_kib": usage.ru_maxrss,
                    }, samples)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path, help="directory for the two raw CSV files")
    parser.add_argument("--counts", type=int, nargs="+", default=SIZES)
    args = parser.parse_args()
    if len(args.counts) < 2 or min(args.counts) <= 0:
        parser.error("provide at least two positive table sizes")
    args.results.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="sstable-index-targets-", dir=ROOT.parent) as name:
        experiment = Path(name)
        lean = experiment / "lean"
        shutil.copytree(ROOT / "lean", lean, ignore=shutil.ignore_patterns(".lake"))
        binaries = {policy: experiment / policy for policy in (UNIFORM, UPPER)}
        build(lean, binaries[UNIFORM])
        configure_upper_levels(lean)
        build(lean, binaries[UPPER])
        with (args.results / "index-targets.csv").open("w", newline="") as output:
            measure_queries(binaries, output, args.counts)
        with (args.results / "index-targets-rss.csv").open("w", newline="") as output:
            measure_rss(binaries, output, args.counts)


if __name__ == "__main__":
    main()
