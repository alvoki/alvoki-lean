import argparse
import csv
import os
from pathlib import Path
import random
import statistics
import struct
import subprocess
import tempfile

from disk_replay import CHECKSUM, FIELDS, MARKER_FIELDS, with_checksum

parser = argparse.ArgumentParser(description="Compare bounded and per-segment native WAL replay.")
parser.add_argument("binary", type=Path, help="scratch-built replay executable")
parser.add_argument("--out", type=Path, help="write raw samples to this CSV")
parser.add_argument("--cpu", type=int, default=1, help="pin the comparison to this CPU")
parser.add_argument("--checks-only", action="store_true", help="skip timing and resource measurements")
parser.add_argument("--paired", action="store_true", help="compare vector and deferred paths for 12 paired trials")
args = parser.parse_args()
if not args.checks_only and args.out is None:
    parser.error("measurements require --out")
if args.cpu not in os.sched_getaffinity(0):
    parser.error("the selected CPU is outside the available affinity")
binary = args.binary.resolve()
cpu = args.cpu
os.sched_setaffinity(0, {cpu})
frame_size = FIELDS.size + CHECKSUM.size
wal_magic = 0x314C41574F564C41
marker_magic = 0x31544D434F564C41


def dataset(directory, count, segments, watermark):
    directory.mkdir()
    for first in range(0, count, (count + segments - 1) // segments):
        width = (count + segments - 1) // segments
        end = min(count, first + width)
        with (directory / f"WAL-segment-{first}").open("wb") as handle:
            for index in range(first, end):
                covered = index < watermark
                key = count - index - 1
                fields = FIELDS.pack(wal_magic, index + 1, key, int(covered), 0 if covered else key + 1)
                handle.write(with_checksum(fields))
            if end == count:
                handle.write(b"unselected tail")
    marker = MARKER_FIELDS.pack(marker_magic, count * frame_size)
    (directory / "WAL.commit").write_bytes(with_checksum(marker))
    subprocess.run([binary, "manifest", directory, str(watermark)], check=True)
    return (count - 1) // width * width


def run(mode, directory, *args):
    with tempfile.TemporaryFile() as captured:
        proc = subprocess.Popen([binary, mode, directory, *args], stdout=captured, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
        captured.seek(0)
        return proc.returncode, captured.read().decode().strip(), usage.ru_maxrss


def valid_result(mode, directory, count, watermark, keeper):
    status, output, rss = run(mode, directory)
    if status != 0:
        raise RuntimeError(f"{mode} rejected valid input: {output}")
    elapsed, committed, generation, rows, lowest, active, kept, physical = output.split(",")
    expected = [count, 1, count - watermark, keeper, (count - keeper) * frame_size]
    if list(map(int, (committed, generation, rows, active, kept))) != expected:
        raise RuntimeError(f"{mode} returned the wrong table, keeper or bounds: {output}")
    if lowest != "(some 1)" or int(physical) != int(kept) + len(b"unselected tail"):
        raise RuntimeError(f"{mode} returned wrong value or keeper physical metadata: {output}")
    return int(elapsed), rss


def errors(directory):
    first = directory / "WAL-segment-0"
    second = sorted(directory.glob("WAL-segment-*"), key=lambda path: int(path.name.split("-")[-1]))[1]
    original = first.read_bytes()
    other = second.read_bytes()
    covered_checksum = bytearray(original)
    covered_checksum[40] ^= 1
    wrong_ordinal = FIELDS.pack(wal_magic, 99, 63, 1, 0)
    second_checksum = bytearray(other)
    second_checksum[40] ^= 1
    wrong_frame = with_checksum(wrong_ordinal) + original[frame_size:]
    for label, prefix, others, same in (
        ("covered-checksum", covered_checksum, other, True),
        ("covered-ordinal", wrong_frame, other, True),
        ("ordinal+later-checksum", wrong_frame, second_checksum, True),
        ("sealed-size", original, other[:-1], True),
        ("checksum+later-size", covered_checksum, other[:-1], False),
    ):
        first.write_bytes(prefix)
        second.write_bytes(others)
        vector, early, serial, deferred = [run(mode, directory) for mode in ("vector", "early", "serial", "deferred")]
        if not (early[0] and deferred[0] and early[1] == deferred[1] == vector[1]):
            raise RuntimeError(f"unexpected deferred {label}: {vector}, {early}, {deferred}")
        if not (vector[0] and serial[0] and (vector[1] == serial[1]) == same):
            raise RuntimeError(f"unexpected {label}: {vector}, {serial}")
        print(f"{label}: baseline and deferred both report {vector[1]}")
    first.write_bytes(covered_checksum)
    second.write_bytes(other)
    keeper = max(directory.glob("WAL-segment-*"), key=lambda path: int(path.name.split("-")[-1]))
    saved_keeper = keeper.read_bytes()
    keeper.write_bytes(saved_keeper[:1])
    vector, deferred = [run(mode, directory) for mode in ("vector", "deferred")]
    if not (vector[0] and deferred[0] and vector[1] == deferred[1] and "keeper" in vector[1]):
        raise RuntimeError(f"unexpected checksum+short-keeper: {vector}, {deferred}")
    print(f"checksum+short-keeper: {vector[1]} / {deferred[1]}")
    keeper.write_bytes(saved_keeper)
    if os.geteuid() != 0:
        try:
            second.chmod(0)
            vector, deferred = [run(mode, directory) for mode in ("vector", "deferred")]
            if not (vector[0] and deferred[0] and vector[1] == deferred[1] and "permission" in vector[1].lower()):
                raise RuntimeError(f"unexpected checksum+later-io: {vector}, {deferred}")
            print(f"checksum+later-io: {vector[1]} / {deferred[1]}")
        finally:
            second.chmod(0o600)
    first.write_bytes(original)
    second.write_bytes(other)


def deep(directory, count, watermark, keeper, newer):
    expected = ",".join(f"{key}:{key + 1}" for key in range(count - watermark))
    for mode in ("vector", "early", "serial", "deferred"):
        status, output, _ = run(mode, directory, "--deep")
        if status != 0:
            raise RuntimeError(f"{mode} rejected deep fixture: {output}")
        summary, rows, plan = output.splitlines()
        observed_keeper, retained_bytes = map(int, summary.split(",")[5:7])
        if (rows != expected or plan != f"{watermark},{newer}" or observed_keeper != keeper or
                retained_bytes != (count - keeper) * frame_size):
            raise RuntimeError(f"{mode} returned an unexpected exact range or keeper plan: {output}")


with tempfile.TemporaryDirectory(prefix="alvoki-replay-measure-") as target:
    root = Path(target)
    small = root / "checks"
    keeper = dataset(small, 64, 4, 3)
    for mode in ("vector", "early", "serial", "deferred"):
        valid_result(mode, small, 64, 3, keeper)
    deep(small, 64, 3, keeper, [])
    errors(small)
    boundary = root / "aligned-checkpoint"
    keeper = dataset(boundary, 64, 4, 16)
    deep(boundary, 64, 16, keeper, [])
    last = boundary / f"WAL-segment-{keeper}"
    last.write_bytes(last.read_bytes()[:-len(b"unselected tail")])
    (boundary / "WAL-segment-64").write_bytes(b"unselected tail")
    (boundary / "WAL-segment-70").write_bytes(b"discardable")
    deep(boundary, 64, 16, 64, [70])
    print("All modes returned exact ranges and keeper bytes, including a zero-prefix keeper.")
    if args.checks_only:
        raise SystemExit(0)
    paired = args.paired
    print(f"CPU {cpu}. Results are marker-limited preparation milliseconds and full process peak RSS MiB.")
    count, watermark, rounds = 600000, 17, (12 if paired else 3)
    rng = random.Random(20261124)
    with args.out.open("w", newline="") as raw:
        output = csv.writer(raw, lineterminator="\n")
        output.writerow(["records", "segments", "pair", "mode", "elapsed_ns", "peak_rss_kib"])
        for segments in ((8, 32) if paired else (1, 8, 32)):
            directory = root / str(segments)
            keeper = dataset(directory, count, segments, watermark)
            modes = ("vector", "deferred") if paired else ("vector", "early", "serial", "deferred")
            values = {mode: [] for mode in modes}
            for pair in range(rounds + 1):
                order = list(values)
                rng.shuffle(order)
                for mode in order:
                    result = valid_result(mode, directory, count, watermark, keeper)
                    if pair:
                        values[mode].append(result)
                        output.writerow((count, segments, pair, mode, *result))
            for mode in list(values):
                ns, rss = zip(*values[mode])
                print(f"{segments:2} {mode:6s} {statistics.median(ns)/1e6:9.2f} ms "
                      f"{statistics.median(rss)/1024:8.2f} MiB")
