#!/usr/bin/env python3
"""Collect native release trials. Requires only Python's standard library."""
import argparse
import csv
import gzip
import json
import os
from pathlib import Path
import platform
import random
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass

ROOT = Path(__file__).resolve().parents[2]
NATIVE_FIELDS = ("scope", "operation", "items", "elapsed_ns", "cpu_ns",
                 "small_allocations", "peak_rss_kib")


@dataclass(frozen=True)
class Case:
    name: str
    args: tuple
    fixture: bool = False
    latency: bool = False


def matrix(suite, quick):
    if suite == "l0":
        reads = 64 if quick else 2048
        for depth in (2, 8, 16):
            for lookup in ("newest", "oldest", "miss"):
                yield Case(f"l0-{lookup}-{depth}", (lookup, "{path}", depth, reads), latency=True)
        for rows in (64, 256):
            yield Case(f"l0-flush-{rows}", ("flush", "{path}", 0, rows))
        yield Case("l0-mixed-8", ("mixed", "{path}", 8, 8 if quick else 64), latency=True)
        return

    for policy in ("log", "boundary"):
        for name, capacity, before, items in (
            ("in-place", 128, 0, 128), ("rotate", 8, 0, 128),
            ("short-history", 128, 1, 64), ("long-history", 128, 2049, 64),
        ):
            yield Case(f"wal-{policy}-{name}",
                       ("wal", "append", "{path}", policy, capacity, items, before),
                       latency=True)
        for capacity, items in ((128, 0), (128, 128), (128, 2048), (16, 2048), (128, 8192)):
            if quick and items > 128:
                continue
            yield Case(f"wal-{policy}-reopen-{items}-cap{capacity}",
                       ("wal", "reopen", "{path}", policy, capacity, items, 0), fixture=True)
    yield Case("wal-decode-cpu", ("codec", 8 if quick else 1024))
    rows, queries = (1025, 128) if quick else (65537, 4096)
    for operation in ("lookup", "scan", "build", "build-sync"):
        yield Case(f"sst-{operation}", ("sst", operation, "{path}", rows, queries),
                   fixture=operation in ("lookup", "scan"), latency=operation == "lookup")


def text(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def optional(command, cwd=ROOT):
    try:
        return text(command, cwd)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def metadata(args, binary, cases, cpu):
    build_repo = binary.parent.parents[3]
    cpuinfo = Path("/proc/cpuinfo").read_text()
    model = re.search(r"^model name\s*:\s*(.*)$", cpuinfo, re.M)
    governor = Path(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")
    return {
        "source_head": text(["git", "rev-parse", "HEAD"], build_repo),
        "source_status": text(["git", "status", "--porcelain"], build_repo),
        "harness_head": text(["git", "rev-parse", "HEAD"]),
        "harness_status": text(["git", "status", "--porcelain"]),
        "binary": str(binary),
        "binary_sha256": text(["sha256sum", binary]).split()[0],
        "command": shlex.join(sys.argv),
        "kernel": platform.platform(),
        "cpu": cpu,
        "cpu_model": model.group(1) if model else None,
        "governor": governor.read_text().strip() if governor.exists() else None,
        "affinity_available": sorted(os.sched_getaffinity(0)),
        "virtualization": optional(["systemd-detect-virt"]),
        "mount": text(["findmnt", "-T", args.data_dir, "-no", "SOURCE,FSTYPE,VFS-OPTIONS"]),
        "block_devices": optional(["lsblk", "-d", "-o", "NAME,ROTA,TRAN,MODEL"]),
        "lean": text(["lean", "--version"], build_repo / "lean"),
        "lake": text(["lake", "--version"], build_repo / "lean"),
        "cc": text(["cc", "--version"]).splitlines()[0],
        "cxx": text(["c++", "--version"]).splitlines()[0],
        "cases": [vars(case) for case in cases],
        "cache": args.cache,
        "seed": args.seed,
        "warmups": args.warmups,
        "repeats": args.repeats,
        "strace": optional(["strace", "--version"]) if args.strace else None,
        "sync_timing": args.sync_timing,
    }


def command(binary, cpu, case, path, mode, prepare=False):
    argv = [str(arg).replace("{path}", str(path)) for arg in case.args]
    if prepare:
        argv[1] = "prepare"
    if argv[0] != "codec":
        argv.append(mode)
    return ["taskset", "-c", str(cpu), str(binary), *argv]


def measure(args, binary, cpu, case, fixture, scratch, stage, profiler):
    env = dict(os.environ, LC_ALL="C")
    env.pop("ALVOKI_BENCH_TRACE", None)
    env.pop("ALVOKI_BENCH_SYNC_FILE", None)
    with tempfile.TemporaryDirectory(dir=scratch) as name, \
            tempfile.TemporaryDirectory(dir=args.output) as diagnostics:
        path = fixture or Path(name, "data")
        if not fixture and case.args[0] != "sst":
            path.mkdir()
        if case.args[:2] in (("sst", "lookup"), ("sst", "scan")):
            with path.open("rb") as file:
                if args.cache == "advised":
                    os.posix_fadvise(file.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                else:
                    while file.read(1024 * 1024):
                        pass
        cmd = command(binary, cpu, case, path, stage)
        trace = Path(diagnostics, "trace.txt")
        sync = Path(diagnostics, "sync.csv")
        if stage == "sync-timing":
            env["LD_PRELOAD"] = str(profiler)
            env["ALVOKI_BENCH_SYNC_FILE"] = str(sync)
        if stage == "syscall":
            env["ALVOKI_BENCH_TRACE"] = "1"
            cmd = ["strace", "-ff", "-qq", "-T", "-s", "96", "-e", "trace=%file,%desc",
                   "-o", str(trace), *cmd]
        result = subprocess.run(cmd, check=True, stdout=subprocess.PIPE, text=True, env=env)
        rows = list(csv.DictReader(result.stdout.splitlines(), fieldnames=NATIVE_FIELDS))
        if sum(row["scope"] == "batch" for row in rows) != 1:
            raise ValueError(f"expected one measurement from {case.name}")
        if stage == "syscall":
            # Keep exactly the measured region, including syscall return values and durations.
            for thread_trace in trace.parent.glob(f"{trace.name}.*"):
                with thread_trace.open() as source:
                    for line in source:
                        if "STORAGE_BENCH_BEGIN" in line:
                            with gzip.open(args.output / f"{case.name}.strace.gz", "wt") as saved:
                                return rows, syscall_rows(source, saved), []
            raise ValueError(f"missing strace start marker for {case.name}")
        if stage == "sync-timing":
            with sync.open(newline="") as source:
                return rows, [], list(csv.reader(source))
        return rows, [], []


def syscall_rows(source, saved):
    calls = defaultdict(lambda: [0, 0, 0])
    for line in source:
        if "STORAGE_BENCH_END" in line:
            return [(name, *values) for name, values in sorted(calls.items())]
        saved.write(line)
        match = re.match(r"(\w+)\(.*\)\s+=\s+(-?\d+).*<([\d.]+)>\s*$", line)
        if match:
            name, result, seconds = match.groups()
            state = calls[name]
            state[0] += 1
            state[1] += round(float(seconds) * 1_000_000_000)
            if name in ("read", "pread64", "write", "pwrite64") and int(result) > 0:
                state[2] += int(result)
    raise ValueError("missing strace end marker")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, required=True, help="existing filesystem under test")
    parser.add_argument("--output", type=Path, required=True, help="new directory for raw results")
    parser.add_argument("--suite", choices=("components", "l0"), default="components")
    parser.add_argument("--binary", type=Path, default=ROOT / "lean/.lake/build/bin/storageBench")
    parser.add_argument("--case", action="append", help="exact case name, repeat to select several")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--seed", type=int, default=20261128)
    parser.add_argument("--cache", choices=("warm", "advised"), default="warm")
    parser.add_argument("--quick", action="store_true", help="smaller smoke workload")
    parser.add_argument("--strace", action="store_true", help="one separate untimed trace per case")
    parser.add_argument("--sync-timing", action="store_true",
                        help="separate non-ptrace fsync/fdatasync timing pass")
    args = parser.parse_args()
    if args.repeats < 1 or args.warmups < 0:
        parser.error("require positive repeats and nonnegative warmups")
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("--cpu must be in the current affinity mask")
    binary = args.binary.resolve()
    if not os.access(binary, os.X_OK):
        parser.error(f"build the benchmark binary first: {binary}")
    if args.strace and not shutil.which("strace"):
        parser.error("--strace requires strace")
    cases = list(matrix(args.suite, args.quick))
    if args.case:
        unknown = set(args.case) - {case.name for case in cases}
        if unknown:
            parser.error(f"unknown cases: {', '.join(sorted(unknown))}")
        cases = [case for case in cases if case.name in args.case]
    if args.cache == "advised" and any(case.args[:2] not in (("sst", "lookup"), ("sst", "scan"))
                                       for case in cases):
        parser.error("--cache advised requires selecting only sst-lookup and/or sst-scan")
    info = metadata(args, binary, cases, args.cpu)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "environment.json").write_text(json.dumps(info, indent=2) + "\n")
    stages = [("warmup", args.warmups), ("throughput", args.repeats), ("latency", args.repeats)]
    if args.strace:
        stages.append(("syscall", 1))
    if args.sync_timing:
        stages.append(("sync-timing", args.repeats))
    rng = random.Random(args.seed)
    with tempfile.TemporaryDirectory(prefix="alvoki-storage-", dir=args.data_dir) as datadir, \
            (args.output / "trials.csv").open("w", newline="") as samples, \
            (args.output / "syscalls.csv").open("w", newline="") as traces, \
            (args.output / "sync.csv").open("w", newline="") as sync:
        scratch = Path(datadir)
        writer = csv.DictWriter(samples, fieldnames=("case", "stage", "trial", *NATIVE_FIELDS))
        writer.writeheader()
        trace_writer = csv.writer(traces)
        trace_writer.writerow(("case", "syscall", "calls", "traced_ns", "transferred_bytes"))
        sync_writer = csv.writer(sync)
        sync_writer.writerow(("case", "trial", "call", "syscall", "elapsed_ns", "result"))
        profiler = args.output.resolve() / "sync_timing.so"
        if args.sync_timing:
            subprocess.run(["cc", "-O3", "-DNDEBUG", "-Wall", "-Wextra", "-fPIC", "-shared",
                            str(Path(__file__).with_name("sync_timing.c")), "-ldl", "-o", str(profiler)],
                           check=True)
        fixtures = {}
        for case in cases:
            if case.fixture:
                path = scratch / case.name
                if case.args[0] == "wal":
                    path.mkdir()
                subprocess.run(command(binary, args.cpu, case, path, "throughput", prepare=True),
                               check=True)
                fixtures[case.name] = path
        for stage, repetitions in stages:
            for trial in range(repetitions):
                shuffled = cases.copy()
                rng.shuffle(shuffled)
                for case in shuffled:
                    if stage == "latency" and not case.latency:
                        continue
                    print(f"{stage} {trial}: {case.name}", file=sys.stderr)
                    rows, counts, sync_samples = measure(
                        args, binary, args.cpu, case, fixtures.get(case.name), scratch, stage, profiler)
                    if stage != "syscall":
                        writer.writerows(dict(case=case.name, stage=stage, trial=trial, **row)
                                         for row in rows)
                    trace_writer.writerows((case.name, *row) for row in counts)
                    sync_writer.writerows((case.name, trial, *row) for row in sync_samples)
                    samples.flush()
                    traces.flush()
                    sync.flush()


if __name__ == "__main__":
    main()
