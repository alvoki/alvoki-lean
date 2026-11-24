#!/usr/bin/env python3
"""Time native reopen through the first successful point read after a writer SIGKILL."""

import argparse
from collections import defaultdict
import csv
from itertools import islice
import os
from pathlib import Path
import re
import selectors
import signal
from statistics import median
import subprocess
import tempfile

from disk_replay import FRAME_SIZE, wal_frames


def kill_after_acknowledgements(binary, path, prefix, suffix, timeout):
    with tempfile.TemporaryFile(mode="w+t") as error_log:
        with subprocess.Popen(
            [binary, "write", path, str(prefix), str(suffix)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=error_log, text=True,
        ) as writer:
            try:
                with selectors.DefaultSelector() as selector:
                    selector.register(writer.stdout, selectors.EVENT_READ)
                    if not selector.select(timeout):
                        raise RuntimeError(f"{binary.name}: timed out waiting for durable acknowledgements")
                received = writer.stdout.readline().strip()
                expected = f"acknowledged {prefix + suffix}"
                if received != expected:
                    error_log.seek(0)
                    error = error_log.read().strip()
                    raise RuntimeError(f"{binary.name}: expected {expected!r}, got {received!r}: {error}")
                writer.kill()
                if writer.wait(timeout=timeout) != -signal.SIGKILL:
                    raise RuntimeError(f"{binary.name}: writer did not die by SIGKILL")
            finally:
                if writer.poll() is None:
                    writer.kill()


def measure(binary, path, prefix, suffix, timeout, torn_tail):
    path.mkdir()
    kill_after_acknowledgements(binary, path, prefix, suffix, timeout)
    if torn_tail:
        # An independently encoded partial next frame, beyond the durable marker.
        keeper = path / f"WAL-segment-{prefix}"
        if keeper.stat().st_size != suffix * FRAME_SIZE:
            raise RuntimeError("unexpected aligned keeper extent")
        part = next(islice(wal_frames(prefix + suffix + 1, "ascending"), prefix + suffix, None))[:17]
        with keeper.open("ab") as wal:
            wal.write(part)
            wal.flush()
            os.fsync(wal.fileno())

    result = subprocess.run(
        [binary, "read", path, str(prefix), str(suffix)],
        capture_output=True, text=True, timeout=timeout,
    )
    if result.returncode != 0:
        raise RuntimeError(f"{binary.name}: recovery failed: {result.stderr.strip()}")
    elapsed_line, rss_line = result.stdout.strip().splitlines()
    elapsed = int(elapsed_line)
    rss = re.fullmatch(r"VmHWM:\s+(\d+)\s+kB\s*", rss_line)
    if rss is None and rss_line != "-":
        raise RuntimeError(f"{binary.name}: invalid VmHWM sample {rss_line!r}")
    if elapsed <= 0:
        raise RuntimeError(f"{binary.name}: invalid reopen time {elapsed}")
    if torn_tail:
        # Validate repair after timing so this read cannot warm the timed path.
        expected = b"".join(islice(wal_frames(prefix + suffix, "ascending"), prefix, None))
        if keeper.read_bytes() != expected:
            raise RuntimeError("torn-tail repair did not preserve the exact committed WAL suffix")
    return elapsed, int(rss[1]) if rss else None


def run(args):
    available = os.sched_getaffinity(0)
    cpu = min(available) if args.cpu is None else args.cpu
    if cpu not in available:
        raise ValueError(f"CPU {cpu} is outside the available affinity mask")
    os.sched_setaffinity(0, {cpu})
    cases = [
        ("alvoki", args.lean_bin.resolve(), False),
        ("rocksdb", args.rocks_bin.resolve(), False),
    ]
    if not args.aligned_only:
        cases.append(("alvoki", args.lean_bin.resolve(), True))
    samples = defaultdict(list)
    peaks = defaultdict(list)
    with tempfile.TemporaryDirectory(prefix="alvoki-engine-reopen-", dir=args.scratch) as scratch:
        with args.out.open("w", newline="") as output:
            csv_out = csv.writer(output, lineterminator="\n")
            csv_out.writerow(("engine", "case", "prefix_records", "suffix_records", "trial", "open_first_read_ns",
                                 "first_read_peak_rss_kib", "cpu"))
            for trial in range(1, args.trials + 1):
                # Rotate execution order so a single engine does not always go first.
                offset = (trial - 1) % len(cases)
                for suffix in args.suffix_sizes:
                    for name, binary, torn in cases[offset:] + cases[:offset]:
                        case = "injected-torn-tail" if torn else "aligned-sigkill"
                        path = Path(scratch) / f"{name}-{case}-{suffix}-{trial}"
                        elapsed, peak = measure(binary, path, args.prefix, suffix, args.timeout, torn)
                        csv_out.writerow((name, case, args.prefix, suffix, trial, elapsed, peak, cpu))
                        output.flush()
                        samples[name, case, suffix].append(elapsed)
                        if peak is not None:
                            peaks[name, case, suffix].append(peak)
    for (name, case, suffix), timings in sorted(samples.items()):
        peak_values = peaks[name, case, suffix]
        peak_summary = f"{median(peak_values):.0f} KiB median peak RSS" if peak_values else "peak RSS unavailable"
        print(f"{name:8} {case:18} {suffix:6} suffix records  {median(timings) / 1e6:9.3f} ms median   {peak_summary}")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--lean-bin", required=True, type=Path)
    cli.add_argument("--rocks-bin", required=True, type=Path)
    cli.add_argument("--out", required=True, type=Path)
    cli.add_argument("--scratch", type=Path, help="directory on the filesystem to benchmark")
    cli.add_argument("--prefix", type=int, default=1024, help="records checkpointed/flushed before the suffix")
    cli.add_argument("--suffix-sizes", nargs="+", type=int, default=[16, 128, 512])
    cli.add_argument("--trials", type=int, default=3)
    cli.add_argument("--cpu", type=int)
    cli.add_argument("--timeout", type=float, default=120, help="writer and reader timeout in seconds")
    cli.add_argument("--aligned-only", action="store_true", help="skip the Alvoki-specific torn-tail fixture")
    args = cli.parse_args()
    if min(args.suffix_sizes + [args.prefix, args.trials, args.timeout]) <= 0:
        cli.error("record counts, trial count and timeout must be positive")
    if len(set(args.suffix_sizes)) != len(args.suffix_sizes):
        cli.error("use distinct suffix record counts")
    run(args)


if __name__ == "__main__":
    main()
