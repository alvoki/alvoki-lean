import csv
import pathlib
import statistics
import subprocess
work = pathlib.Path(__file__).resolve().parent

def measure(variant):
    command = ["taskset", "-c", "2", work / ("reopen-" + variant), work / "wal-public"]
    return int(subprocess.check_output(command, text=True).strip()) / 1e6

results = {"candidate": [], "leaf": []}
for variant in results:
    measure(variant)
with (work / "healthy-reopen.csv").open("w") as output:
    w = csv.writer(output)
    w.writerow(["pair", "variant", "ms_for_250"])
    for i in range(7):
        order = ["candidate", "leaf"] if i % 2 == 0 else ["leaf", "candidate"]
        for variant in order:
            value = measure(variant)
            results[variant].append(value)
            w.writerow([i+1, variant, value])
for variant, samples in results.items():
    print(variant, min(samples), statistics.median(samples), max(samples))
