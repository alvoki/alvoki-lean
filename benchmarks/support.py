"""Shared fixtures, subprocess contracts, and reporting for the experiment drivers."""

import csv
import os
from pathlib import Path
import random
from statistics import median
import subprocess
import sys
import time

if not __debug__:
    raise SystemExit("Alvoki checks require Python assertions. Disable -O and PYTHONOPTIMIZE.")

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "fixtures"))
from generate import WORD_MASK, block, dataset

BLOCK_BINARIES = {
    "rust": ROOT / "rust/target/release/alvoki-block",
    "lean-fast": ROOT / "lean/.lake/build/bin/alvoki",
    "lean": ROOT / "lean/.lake/build/bin/alvoki",
}
MERGE_BINARIES = {
    "lean": ROOT / "lean/.lake/build/bin/alvoki-merge-phases",
    "rust": ROOT / "rust/target/release/alvoki-merge-phases",
}
MASK = 0xFEDCBA9876543210
TRACE_FIXTURE = ([(10, 100)], [(0, 200)])
INVALID_TRACES = (b"", b"\x01", b"\x01\x00\x00", b"\xff\x00", b"\x02\x01", b"\x00\x01", b"\x02")


def invoke_block(label, binary, mode, data, queries, param, repeats, **kwargs):
    env = dict(os.environ, ALVOKI_FAST="1" if label == "lean-fast" else "0")
    env.pop("ALVOKI_RSS", None)
    return subprocess.run(
        [binary, mode, data, queries, str(param), str(repeats)],
        text=True, capture_output=True, env=env, **kwargs,
    )


def measured(label, binary, mode, data, queries, param, repeats):
    env = dict(os.environ, ALVOKI_FAST="1" if label == "lean-fast" else "0", ALVOKI_RSS="1")
    command = [binary, mode, data, queries, str(param), str(repeats)]
    start = time.perf_counter_ns()
    output = subprocess.run(command, text=True, capture_output=True, env=env, check=True)
    elapsed = time.perf_counter_ns() - start
    *samples, rss = output.stdout.splitlines()
    header, amount, unit = rss.split()
    assert (header, unit) == ("VmHWM:", "kB")
    return samples, int(amount), elapsed


def run_once(binary, mode, data, aux, output):
    subprocess.run([binary, mode, data, aux, output, "1"], check=True,
                   env={key: value for key, value in os.environ.items() if key != "ALVOKI_RSS"})


def merged_records(left, right):
    return sorted((dict(left) | dict(right)).items())


def checksum(records):
    return sum(k ^ v for k, v in records) & WORD_MASK


def merge_inputs(size, order):
    half = size // 2
    records = dataset(size)
    if order == "alternating":
        return records[::2], records[1::2]
    if order == "disjoint":
        return records[:half], records[half:]
    # The right side overwrites keys shared with the last quarter of the left side.
    return records[:half], [(k, v ^ WORD_MASK) for k, v in records[size // 4:size // 4 + size - half]]


def summarize(path):
    groups = {}
    with path.open() as source:
        for row in csv.DictReader(source):
            key = tuple(row[name] for name in ("records", "workload", "variant"))
            groups.setdefault(key, []).append(row)
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("records", "workload", "variant", "trials", "min_ms", "median_ms", "max_ms",
                     "median_ns_per_unit", "peak_rss_kib"))
    for group, rows in sorted(groups.items(), key=lambda pair: (int(pair[0][0]), *pair[0][1:])):
        times = [int(row["ns"]) for row in rows]
        writer.writerow((*group, len(rows), f"{min(times) / 1e6:.6f}", f"{median(times) / 1e6:.6f}",
                         f"{max(times) / 1e6:.6f}", f"{median(times) / int(rows[0]['operations']):.3f}",
                         rows[0]["peak_rss_kib"]))


def split_spans(records, length):
    sides = ([], [])
    for start in range(0, len(records), length):
        sides[(start // length) % 2].extend(records[start:start + length])
    return sides


def mixed_spans(records):
    sides = ([], [])
    start = 0
    turn = 0
    lengths = (1, 1, 4, 16, 64, 256, 16, 4)
    while start < len(records):
        length = lengths[turn % len(lengths)]
        sides[turn % 2].extend(records[start:start + length])
        start += length
        turn += 1
    return sides


def decisions(left, right):
    """Build a trace outside the timer from the independent sorted-union oracle."""
    left_keys = set(dict(left))
    right_keys = set(dict(right))
    return bytes(
        2 if key in left_keys and key in right_keys else int(key in right_keys)
        for key in sorted(left_keys | right_keys)
    )


def tag(encoded):
    return int.from_bytes(encoded[:8], "little") ^ int.from_bytes(encoded[-8:], "little") ^ len(encoded)


def invoke_replay(binary, mode, inputs, output, reps=1, check=True):
    result = subprocess.run([binary, mode, *inputs, output, str(reps)],
                            text=True, capture_output=True, check=check)
    return result if not check else [tuple(map(int, line.split())) for line in result.stdout.splitlines()]


def set_inputs(inputs, left, right):
    a, b, trace = inputs
    a.write_bytes(block(left))
    b.write_bytes(block(right))
    trace.write_bytes(decisions(left, right))


def native_mode(variant, mode):
    return f"builder-{mode}" if variant == "rust-scoped" else mode


def compactions(records):
    rng = random.Random(471)
    shuffled = ([], [])
    for record in records:
        shuffled[rng.randrange(2)].append(record)
    clustered = ([], [])
    offset = 0
    side = 0
    while offset < len(records):
        end = offset + rng.choice((32, 128, 512, 2048))
        clustered[side].extend(records[offset:end])
        offset = end
        side ^= 1
    half = len(records) // 2
    updates = len(records) - half
    common = min(half, updates * 3 // 4)
    hot = sorted(rng.sample(records[:half], common) + records[half:half + updates - common])
    return (
        ("alternating", split_spans(records, 1)),
        ("shuffled-interleave", shuffled),
        ("clustered-ranges", clustered),
        ("update-heavy", (records[:half], [(key, value ^ MASK) for key, value in hot])),
    )
