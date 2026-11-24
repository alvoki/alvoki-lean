import csv
from collections import defaultdict
from pathlib import Path
import random
from statistics import median
import sys

measurements = defaultdict(lambda: defaultdict(list))
positions = {}
for name in sys.argv[1:]:
    with Path(name).open(newline="") as file:
        for row in csv.DictReader(file):
            key = (row["cpu"], row["case"], row["kind"], int(row["pair"]))
            side = int(row["side"])
            measurements[key][side].append(int(row["ns"]))
            positions[key, side] = int(row["position"])

strata = defaultdict(lambda: defaultdict(list))
order = defaultdict(list)
for key, sides in measurements.items():
    cpu, case, kind, _ = key
    if len(sides[0]) != 3 or len(sides[1]) != 3:
        raise ValueError(f"incomplete observations for {key}")
    ratio = median(sides[1]) / median(sides[0])
    strata[case, kind][cpu].append(ratio)
    if kind == "AB":
        order[case, positions[key, 0]].append(ratio)

rng = random.Random(51417)
for (case, kind), by_cpu in sorted(strata.items()):
    readings = [ratio for group in by_cpu.values() for ratio in group]
    values = sorted(
        median([ratio for group in by_cpu.values() for ratio in rng.choices(group, k=len(group))])
        for _ in range(10000)
    )
    cores = ", ".join(f"{cpu} {median(group):.3f}x ({len(group)})" for cpu, group in sorted(by_cpu.items()))
    print(f"{case:14s} {kind} {len(readings):2d} pairs: {median(readings):.3f}x"
          f" [{values[250]:.3f}, {values[9750]:.3f}], cores {cores}")
for (case, position), ratios in sorted(order.items()):
    print(f"{case} AB with baseline in position {position}: {median(ratios):.3f}x ({len(ratios)} pairs)")
