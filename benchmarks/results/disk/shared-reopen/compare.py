import csv
import os
import platform
from pathlib import Path
import random
from statistics import median
from struct import pack
import subprocess
import sys
from tempfile import TemporaryDirectory

root = Path(__file__).resolve().parent
if len(sys.argv) != 2:
    raise SystemExit("Usage: python3 compare.py ALVOKI_CHECKOUT")
sys.path.insert(0, str(Path(sys.argv[1]).resolve() / "benchmarks"))
from disk_replay import write_wal

def encode_marker(byte_count):
    # Match the Lean marker's three little-endian words and FNV-1a checksum.
    payload = pack("<QQ", 0x31544D434F564C41, byte_count)
    checksum = 14695981039346656037
    for byte in payload:
        checksum = ((checksum ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return payload + pack("<Q", checksum)

allowed = os.sched_getaffinity(0)
cpu = 1 if 1 in allowed else min(allowed)
os.sched_setaffinity(0, {cpu})
matrix = ((32, "aligned"), (32, "repair"), (2048, "aligned"), (2048, "repair"))
pairs = 14
samples = {}
with TemporaryDirectory() as scratch, (root / "trials.csv").open("w", newline="") as output:
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(["records", "path", "pair", "position", "variant", "ns", "cpu"])
    cases = {}
    for records, path in matrix:
        directory = Path(scratch) / f"{records}-{path}"
        directory.mkdir()
        wal = directory / "WAL"
        write_wal(wal, records, "descending")
        complete = wal.read_bytes()
        (directory / "WAL.commit").write_bytes(encode_marker(len(complete)))
        fixture = complete + (b"ALVOWAL1\x00\x00\x00" if path == "repair" else b"")
        cases[records, path] = (directory, wal, fixture)
    for pair in range(1, pairs + 1):
        order = list(matrix)
        random.Random(1874 + pair).shuffle(order)
        variants = ("base", "candidate") if pair % 2 else ("candidate", "base")
        for records, path in order:
            directory, wal, fixture = cases[records, path]
            for position, variant in enumerate(variants, 1):
                wal.write_bytes(fixture)
                cmd = [root / variant, directory, str(records), "1"]
                if path == "repair":
                    cmd.append("--repair-tail")
                elapsed = int(subprocess.check_output(cmd, text=True).strip())
                assert elapsed > 0
                samples[records, path, pair, variant] = elapsed
                writer.writerow((records, path, pair, position, variant, elapsed, cpu))
                output.flush()
print(f"CPU {cpu}, {pairs} interleaved pairs, {platform.platform()}")
for records, path in matrix:
    base = [samples[records, path, pair, "base"] for pair in range(1, pairs + 1)]
    candidate = [samples[records, path, pair, "candidate"] for pair in range(1, pairs + 1)]
    paired = median(after / before for before, after in zip(base, candidate))
    print(f"{records} {path}: {median(base) / 1e6:.3f} -> {median(candidate) / 1e6:.3f} ms; median paired ratio {paired:.3f}x")
