import os
from pathlib import Path
import subprocess as sp
import sys
import tempfile

p = Path(sys.argv[1])
bench = p / "lean/.lake/build/bin/latency-fixture"
env = {**os.environ, "ALVOKI_LATENCY_HELPER": str(p/"helper"), "LC_ALL": "C"}
for mode in ("once", "persistent"):
    for failure in ("file", "directory", "start", "none"):
        with tempfile.TemporaryDirectory() as d:
            def fixture(cmd, mode, fail="none", check=True):
                return sp.run([bench, cmd, d], capture_output=True, text=True, timeout=10, check=check,
                    env={**env, "ALVOKI_LATENCY_MODE": mode, "ALVOKI_LATENCY_FAIL": fail})
            fixture("seed","reference")
            res = fixture("append" if failure == "none" else "fail",mode,failure,check=False)
            values = fixture("read", "reference").stdout.strip()
            expected = "2 some (some 99)" if failure in ("directory", "none") else "1 some (some 60)"
            status = res.returncode == 0 and values == expected
            print(mode, failure, res.returncode, values, status, res.stderr.strip(), sep="  ")
            if not status:
                raise SystemExit(f"Unexpected recovery for {mode} {failure}. Expected {expected}.")
