import csv
from io import StringIO
import os
from pathlib import Path
from statistics import median
import subprocess
import sys
base, candidate = map(Path, sys.argv[1:])
cpu = 1 if 1 in os.sched_getaffinity(0) else min(os.sched_getaffinity(0))
os.sched_setaffinity(0, {cpu})
pairs = 12
workloads = [
    ("write", ["32", "3"], 32),
    ("checkpoint", ["4", "32", "3"], 1),
]
root = Path(__file__).parent
for name, args, count in workloads:
    pools, ratios = {"base": [], "candidate": []}, []
    with (root / f"{name}-trials.csv").open("w") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(["pair", "position", "variant", "trial", "ns", "cpu"])
        for pair in range(1, pairs + 1):
            pair_medians = {}
            variants = [("base", base), ("candidate", candidate)]
            for position, (variant, binary) in enumerate(variants[::(1 if pair % 2 else -1)], 1):
                rows = list(csv.DictReader(StringIO(subprocess.check_output(
                    [binary / f"alvoki-disk-{name}", *args], text=True
                ).strip())))
                assert len(rows) == 3
                values = [int(row["ns"]) for row in rows]
                assert min(values) > 0
                for row in rows:
                    writer.writerow((pair, position, variant, row["trial"], row["ns"], cpu))
                pools[variant].extend(values)
                pair_medians[variant] = median(values)
            ratios.append(pair_medians["candidate"] / pair_medians["base"])
    print(f"CPU {cpu}, {pairs} interleaved {name} pairs: {median(pools['base']) / 1e6 / count:.3f} -> "
          f"{median(pools['candidate']) / 1e6 / count:.3f} ms/op, median paired ratio {median(ratios):.3f}x")
