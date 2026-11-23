import csv
import os
from pathlib import Path
import random
import statistics as st
import subprocess as sp
import tempfile
import sys

root = Path(sys.argv[1])
allowed = os.sched_getaffinity(0)
cpu = int(os.environ.get("ALVOKI_CPU", max(allowed)))
if cpu not in allowed:
    raise SystemExit(f"CPU {cpu} is outside this process's affinity")
writes, trials = (int(arg) for arg in sys.argv[2:4])
if writes <= 0 or trials <= 0:
    raise SystemExit("writes and trials must be positive")
os.sched_setaffinity(0, {cpu})
env = {**os.environ, "ALVOKI_LATENCY_HELPER":str(root / "helper"),"LC_ALL":"C"}
env.pop("ALVOKI_LATENCY_FAIL", None)
cases = ["legacy", "reference", "plain", "stderr", "once", "persistent", "direct"]
rng = random.Random(721)
ns = {case: [] for case in cases}
bench = root / "lean/.lake/build/bin/alvoki-disk-write"
with (root / "latency-raw.csv").open("w", newline="") as f:
    out = csv.writer(f, lineterminator="\n")
    out.writerow(["mode", "round", "writes", "ns"])
    for rep in range(trials):
        rng.shuffle(cases)
        for mode in cases:
            p = sp.run([bench, str(writes), "1"], env={**env, "ALVOKI_LATENCY_MODE": mode},
                       timeout=max(10, writes / 10), check=True,
                       stdout=sp.PIPE, text=True)
            count, trial, total = map(int,p.stdout.splitlines()[1].split(","))
            if (count, trial) != (writes, 1):
                raise ValueError(f"Invalid benchmark result {p.stdout}")
            out.writerow([mode, rep, writes, total])
            ns[mode].append(total/writes)

def report(trials,label,out_units,scale):
    print(f"{label:20s} {st.median(trials)/scale:7.3f} {min(trials)/scale:7.3f} {max(trials)/scale:7.3f} {out_units}")

print(f"CPU {cpu}")
print(f"end-to-end acknowledged write (p50 / min / max of {trials} trial means)")
for mode in ("legacy", "reference", "plain", "stderr", "once", "persistent", "direct"):
    report(ns[mode],mode,"ms",1e6)

with tempfile.TemporaryDirectory() as t:
    d = Path(t)
    (d / "WAL").write_bytes(b"x")
    (d / "WAL.commit.next").write_bytes(b"x")
    for file in ["WAL","WAL.commit.next"]:
        with (d / file).open("rb") as f:
            os.fsync(f.fileno())
    p = sp.run([root/"lean/.lake/build/bin/latency-micro",root/"helper",d],
               check=True,stdout=sp.PIPE,env=env,text=True,timeout=10)
(root/"micro-raw.csv").write_text(p.stdout)
micro = {}
for row in csv.DictReader(p.stdout.splitlines()):
    micro.setdefault(row["case"],[]).append(int(row["ns"]))
print("Lean process primitives, settled files (p50/min/max of 32 single invocations)")
for mode, vals in micro.items():
    report(vals,mode,"ms",1e6)

with tempfile.TemporaryDirectory() as t:
    p=sp.run([root/"helper","stats",t,"128"],check=True,stdout=sp.PIPE,env=env,text=True,timeout=10)
(root/"rust-stages.csv").write_text("prepare,fsync_wal,fsync_marker,rename,fsync_dir\n"+p.stdout)
stages = [list(map(int,line.split(","))) for line in p.stdout.splitlines()]
print("Rust in-process stages, same record sizes and syscall order (p50/min/max of 128 operations)")
for label,vals in zip(["prepare","fsync_wal","fsync_marker","rename","fsync_dir"], zip(*stages)):
    report(vals,label,"us",1e3)
report([sum(r) for r in stages], "total", "us", 1e3)
