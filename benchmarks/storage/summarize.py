#!/usr/bin/env python3
"""Summarize raw native timings without mixing measurement passes."""
import argparse
import csv
import gzip
import math
from collections import defaultdict
from pathlib import Path
from statistics import median


def pctl(values, fraction):
    return sorted(values)[math.ceil(len(values) * fraction) - 1]


def read(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", newline="") as source:
        return list(csv.DictReader(source))


def trials(directory):
    plain = directory / "trials.csv"
    return read(plain if plain.is_file() else plain.with_suffix(".csv.gz"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    batches, calls = defaultdict(list), defaultdict(list)
    for row in trials(args.directory):
        if row["stage"] == "throughput" and row["scope"] == "batch":
            batches[row["case"]].append(row)
        elif row["stage"] == "latency" and row["scope"] == "call":
            calls[(row["case"], row["operation"])].append(int(row["elapsed_ns"]))
    print("case\ttrials\titems\twall ms [min–max]\tCPU ms\titems/s\t"
          "small allocs\tpeak RSS MiB\tcurrent RSS MiB")
    for case, rows in sorted(batches.items()):
        wall = [int(row["elapsed_ns"]) / 1e6 for row in rows]
        cpu = median(int(row["cpu_ns"]) / 1e6 for row in rows)
        allocs = median(int(row["small_allocations"]) for row in rows)
        rss = median(int(row["peak_rss_kib"]) / 1024 for row in rows)
        current = [int(row["resident_rss_kib"]) / 1024
                   for row in rows if row.get("resident_rss_kib")]
        current_text = f"{median(current):.2f}" if current else "–"
        items = int(rows[0]["items"])
        rate = f"{median(items * 1000 / ms for ms in wall):.0f}" if items else "–"
        print(f"{case}\t{len(rows)}\t{items}\t{median(wall):.3f} "
              f"[{min(wall):.3f}–{max(wall):.3f}]\t{cpu:.3f}\t{rate}\t{allocs:.0f}\t{rss:.2f}\t{current_text}")
    print("\ncase\tcall\tsamples\tp50 µs\tp95 µs\tp99 µs")
    for (case, call), values in sorted(calls.items()):
        print(f"{case}\t{call}\t{len(values)}\t"
              + "\t".join(f"{pctl(values, q) / 1000:.3f}" for q in (.50, .95, .99)))
    sync_csv = args.directory / "sync.csv"
    sync_rows = read(sync_csv if sync_csv.is_file() else sync_csv.with_suffix(".csv.gz"))
    if sync_rows:
        syncs = defaultdict(list)
        for row in sync_rows:
            syncs[(row["case"], row["syscall"], row["result"])].append(int(row["elapsed_ns"]))
        print("\ncase\tsync\tresult\tsamples\tp50 µs\tp95 µs\tp99 µs")
        for (case, syscall, result), ns in sorted(syncs.items()):
            print(f"{case}\t{syscall}\t{result}\t{len(ns)}\t"
                  + "\t".join(f"{pctl(ns, q) / 1000:.3f}" for q in (.50, .95, .99)))


if __name__ == "__main__":
    main()
