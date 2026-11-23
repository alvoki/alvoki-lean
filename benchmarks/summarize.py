#!/usr/bin/env python3
import csv
from collections import defaultdict
from pathlib import Path
from statistics import median
import sys

LANGUAGES = ("rust", "lean", "lean-fast")
BLOCK_WORK = {"encode", "decode", "validate", "load"}


def main(path):
    groups = defaultdict(lambda: defaultdict(list))
    with path.open() as source:
        for row in csv.DictReader(source):
            groups[(int(row["records"]), row["workload"])][row["language"]].append(row)
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("records", "workload", "language", "trials", "unit",
                     "min_ns_per_unit", "median_ns_per_unit", "max_ns_per_unit",
                     "units_per_s", "MiB_per_s", "time_vs_rust", "process_peak_rss_kib"))
    for (size, workload), samples in groups.items():
        rust_ns = median(int(row["ns"]) / int(row["operations"]) for row in samples["rust"])
        for label in LANGUAGES:
            rows = samples[label]
            times = [int(row["ns"]) / int(row["operations"]) for row in rows]
            center = median(times)
            block_work = workload in BLOCK_WORK
            throughput = f"{(16 + size * 16) * 1e9 / (2**20 * center):.2f}" if block_work else ""
            writer.writerow((size, workload, label, len(rows), "block" if block_work else "query",
                             f"{min(times):.2f}", f"{center:.2f}", f"{max(times):.2f}",
                             f"{1e9 / center:.2f}", throughput, f"{center / rust_ns:.3f}",
                             rows[0]["process_peak_rss_kib"]))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
