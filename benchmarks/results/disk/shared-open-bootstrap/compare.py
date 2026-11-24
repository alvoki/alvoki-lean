import csv
import os
from pathlib import Path
import random
from statistics import median
from struct import pack
import subprocess
import sys
from tempfile import TemporaryDirectory

if len(sys.argv) != 5:
    raise SystemExit("usage: compare.py REPO BASE_BIN CANDIDATE_BIN OUT.csv")

repo, base, candidate, output = (Path(arg).resolve() for arg in sys.argv[1:])
sys.path.insert(0, str(repo / "benchmarks"))
from disk_replay import write_wal


def marker(byte_count):
    payload = pack("<QQ", 0x31544D434F564C41, byte_count)
    checksum = 14695981039346656037
    for byte in payload:
        checksum = ((checksum ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return payload + pack("<Q", checksum)


allowed = os.sched_getaffinity(0)
cpu = 1 if 1 in allowed else min(allowed)
os.sched_setaffinity(0, {cpu})
matrix = [(0, "fresh", False)] + [
    (records, mode, repair)
    for records in (32, 2048)
    for mode in ("marked", "legacy")
    for repair in (False, True)
]
pairs = 14
variants = [("base", base), ("candidate", candidate)]
with TemporaryDirectory() as scratch, output.open("w", newline="") as file:
    writer = csv.writer(file, lineterminator="\n")
    writer.writerow(("records", "mode", "tail", "pair", "position", "variant", "ns", "cpu"))
    fixture = {}
    ratios = {case: [] for case in matrix}
    times = {(case, name): [] for case in matrix for name, _ in variants}
    for records in (32, 2048):
        path = Path(scratch) / str(records)
        write_wal(path, records, "descending")
        fixture[records] = path.read_bytes()
    for pair in range(1, pairs + 1):
        order = list(matrix)
        random.Random(1874 + pair).shuffle(order)
        for records, mode, repair in order:
            case = (records, mode, repair)
            batch = {}
            for position, (name, binary) in enumerate(variants if pair % 2 else reversed(variants), 1):
                with TemporaryDirectory(dir=scratch) as database:
                    directory = Path(database)
                    flags = []
                    if mode == "fresh":
                        flags.append("--fresh")
                    else:
                        wal = fixture[records]
                        if mode == "marked":
                            (directory / "WAL.commit").write_bytes(marker(len(wal)))
                        if mode == "legacy":
                            flags.append("--legacy")
                        if repair:
                            flags.append("--repair-tail")
                            wal += b"ALVOWAL1\x00\x00\x00"
                        (directory / "WAL").write_bytes(wal)
                    elapsed = int(subprocess.check_output(
                        [binary, directory, str(records), "1", *flags], text=True).strip())
                    if elapsed <= 0:
                        raise ValueError(f"{name} produced a nonpositive timing")
                batch[name] = elapsed
                times[case, name].append(elapsed)
                writer.writerow((records, mode, "repair" if repair else "aligned", pair, position,
                                 name, elapsed, cpu))
            ratios[case].append(batch["candidate"] / batch["base"])
    for case in matrix:
        before = median(times[case, "base"]) / 1e6
        after = median(times[case, "candidate"]) / 1e6
        print(f"CPU {cpu}, {case}: {before:.3f} -> {after:.3f} ms, paired {median(ratios[case]):.3f}x")
