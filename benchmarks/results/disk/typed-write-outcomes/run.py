import csv
import io
import os
import pathlib
import statistics
import subprocess
import sys


if len(sys.argv) != 4:
    raise SystemExit("usage: python3 run.py BASE_WT CANDIDATE_WT OUT.csv")

binary = "lean/.lake/build/bin/alvoki-disk-write"
binaries = {
    "baseline": pathlib.Path(sys.argv[1]).resolve() / binary,
    "candidate": pathlib.Path(sys.argv[2]).resolve() / binary,
}
results = pathlib.Path(sys.argv[3])
cpu = min(os.sched_getaffinity(0))
os.sched_setaffinity(0, {cpu})
samples = {build: {} for build in binaries}
with results.open("w", newline="") as file:
    writer = csv.DictWriter(file, fieldnames=["build", "pair", "writes", "trial", "ns"], lineterminator="\n")
    writer.writeheader()
    for pair, builds in enumerate((("baseline", "candidate"), ("candidate", "baseline")), 1):
        for build in builds:
            trial_data = subprocess.check_output([binaries[build], "64", "7"], text=True)
            for trial in csv.DictReader(io.StringIO(trial_data)):
                writer.writerow({"build": build, "pair": pair, **trial})
                samples[build][pair, int(trial["trial"])] = int(trial["ns"])

for build, trials in samples.items():
    print(f"{build}: {statistics.median(trials.values()) / (64 * 1_000_000):.3f} ms/write")
ratios = [samples["candidate"][trial] / before for trial, before in samples["baseline"].items()]
print(f"median per-trial ratio: {statistics.median(ratios):.3f}; {len(ratios)} paired samples; pinned CPU {cpu}")
print(results)
