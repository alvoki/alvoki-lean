import csv
from io import StringIO
import os
from pathlib import Path
from statistics import median
import subprocess
import sys

if len(sys.argv) != 4:
    raise SystemExit("usage: python3 compare_checkpoint.py BASE_BIN CANDIDATE_BIN OUT.csv")

base, candidate = (Path(path).resolve() for path in sys.argv[1:3])
output = Path(sys.argv[3])
allowed = os.sched_getaffinity(0)
cpu = 1 if 1 in allowed else min(allowed)
os.sched_setaffinity(0, {cpu})
pairs = 14
variants = [("base", base), ("candidate", candidate)]
with output.open("w", newline="") as file:
    writer = csv.writer(file, lineterminator="\n")
    writer.writerow(("runs", "rows_per_run", "pair", "position", "variant", "trial", "ns", "cpu"))
    for runs, rows_per_run in ((4, 32), (32, 128)):
        samples = {name: [] for name, _ in variants}
        ratios = []
        for pair in range(1, pairs + 1):
            order = variants if pair % 2 else reversed(variants)
            batch = {}
            for position, (name, binary) in enumerate(order, 1):
                raw = subprocess.check_output([binary, str(runs), str(rows_per_run), "3", "--reopen"], text=True)
                trials = list(csv.DictReader(StringIO(raw)))
                if len(trials) != 3:
                    raise ValueError(f"{name} produced {len(trials)} samples, expected 3")
                times = []
                for trial in trials:
                    elapsed = int(trial["ns"])
                    if elapsed <= 0:
                        raise ValueError(f"{name} produced a nonpositive timing")
                    times.append(elapsed)
                    writer.writerow((runs, rows_per_run, pair, position, name, trial["trial"], elapsed, cpu))
                samples[name].extend(times)
                batch[name] = median(times)
            ratios.append(batch["candidate"] / batch["base"])
        before = median(samples["base"]) / 1e6
        after = median(samples["candidate"]) / 1e6
        print(f"CPU {cpu}, {runs} runs of {rows_per_run} rows: {before:.3f} -> {after:.3f} ms; "
              f"median paired ratio {median(ratios):.3f}x ({pairs} pairs)")
