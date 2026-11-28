#!/usr/bin/env python3
"""Measure Linux peak RSS for equivalent writer-only workloads."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / "lean/.lake/build/bin/immutableSSTableCheck"
COUNTS = tuple(int(value) for value in sys.argv[1:]) or (1_000_000, 8_000_000)

print("format,rows,elapsed_ns,trial,max_rss_kib", flush=True)
for count in COUNTS:
    for trial in range(3):
        versions = ("05", "06") if trial % 2 == 0 else ("06", "05")
        for version in versions:
            with tempfile.TemporaryFile(mode="w+t") as output:
                child = subprocess.Popen(
                    [BINARY, "--bench-build", version, str(count)], stdout=output
                )
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
                if child.returncode:
                    raise SystemExit(f"SSTable benchmark exited with {child.returncode}")
                output.seek(0)
                print(f"{output.read().strip()},{trial},{usage.ru_maxrss}", flush=True)
