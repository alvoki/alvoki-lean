import csv
import os
from pathlib import Path
from statistics import median
import subprocess
import sys

workdir = Path(__file__).resolve().parent
os.sched_setaffinity(0, {int(sys.argv[1]) if len(sys.argv) > 1 else 4})
points = 256 * 4096
ranges = 32 * 4096
samples = {'base': [], 'checked': []}
with (workdir / ('trials-' + sys.argv[2] + '.csv') if len(sys.argv) > 2 else 'trials.csv').open('w', newline='') as report:
    writer = csv.writer(report, lineterminator="\n")
    writer.writerow(['pair', 'position', 'variant', 'lookup_ns', 'range_ns'])
    for pair in range(1, 15):
        order = ('base', 'checked') if pair % 2 else ('checked', 'base')
        for position, variant in enumerate(order, 1):
            result = subprocess.check_output([workdir / variant, 'measure', workdir / 'database'], text=True)
            lookup_ns, range_ns = map(int, result.strip().split(','))
            samples[variant].append((lookup_ns, range_ns))
            writer.writerow([pair, position, variant, lookup_ns, range_ns])
            report.flush()
for index, workload, count in [(0, 'lookup', points), (1, 'range', ranges)]:
    before = median(sample[index] for sample in samples['base'])
    after = median(sample[index] for sample in samples['checked'])
    paired = median(after[index] / before[index] for before, after in zip(samples['base'], samples['checked']))
    print(f'{workload}: {before / count:.2f} -> {after / count:.2f} ns/op; '
          f'pooled ratio {after / before:.4f}; median paired ratio {paired:.4f}')
