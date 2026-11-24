import csv
import os
from pathlib import Path
import random
from statistics import median
from struct import pack
import subprocess
import sys
from tempfile import TemporaryDirectory

if len(sys.argv) != 3 or sys.argv[2] not in {'ab1', 'ab2', 'aa'}:
    raise SystemExit('usage: compare.py ALVOKI_CHECKOUT ab1|ab2|aa')
repo = Path(sys.argv[1]).resolve()
cohort = sys.argv[2]
sys.path.insert(0, str(repo / 'benchmarks'))
from disk_replay import write_wal


def marker(length):
    payload = pack('<QQ', 0x31544D434F564C41, length)
    checksum = 14695981039346656037
    for byte in payload:
        checksum = ((checksum ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return payload + pack('<Q', checksum)


root = Path(__file__).resolve().parent
allowed = os.sched_getaffinity(0)
cpu = 1 if 1 in allowed else min(allowed)
os.sched_setaffinity(0, {cpu})
variants = ('base', 'candidate')
cases = [('replay', 32, 0), ('replay-tail', 32, 0), ('replay', 2048, 0), ('replay-tail', 2048, 0),
         ('checkpoint', 4, 32), ('checkpoint-reopen', 32, 128), ('write', 16, 0)]
pairs = 12
ratios = {case: [] for case in cases}
with TemporaryDirectory() as scratch, (root / f'{cohort}.csv').open('w', newline='') as handle:
    writer = csv.writer(handle, lineterminator='\n')
    writer.writerow(('workload', 'size', 'rows', 'pair', 'position', 'variant', 'trial', 'ns', 'cpu'))
    fixtures = {}
    for size in (32, 2048):
        fixture = Path(scratch) / f'wal-{size}'
        write_wal(fixture, size, 'descending')
        fixtures[size] = fixture.read_bytes()
    for pair in range(1, pairs + 1):
        order = list(cases)
        random.Random(1287 + pair).shuffle(order)
        for case in order:
            workload, size, rows = case
            observations = {}
            for pos, variant in enumerate(variants if pair % 2 else reversed(variants), 1):
                binary = 'base' if cohort == 'aa' else variant
                if workload.startswith('replay'):
                    with TemporaryDirectory(dir=scratch) as database:
                        directory = Path(database)
                        wal = fixtures[size]
                        (directory / 'WAL.commit').write_bytes(marker(len(wal)))
                        flags = ['--repair-tail'] if workload.endswith('-tail') else []
                        (directory / 'WAL').write_bytes(wal + (b'ALVOWAL1\x00\x00\x00' if flags else b''))
                        elapsed = subprocess.check_output([root / f'{binary}-alvoki-disk-replay', directory,
                                                           str(size), '3', *flags], text=True)
                elif workload.startswith('checkpoint'):
                    flags = ['--reopen'] if workload.endswith('-reopen') else []
                    elapsed = subprocess.check_output([root / f'{binary}-alvoki-disk-checkpoint', str(size),
                                                       str(rows), '3', *flags], text=True)
                else:
                    elapsed = subprocess.check_output([root / f'{binary}-alvoki-disk-write', str(size), '3'], text=True)
                samples = (list(map(int, elapsed.splitlines())) if workload.startswith('replay')
                           else [int(row['ns']) for row in csv.DictReader(elapsed.splitlines())])
                if len(samples) != 3 or min(samples) <= 0:
                    raise RuntimeError(f'{workload} emitted invalid samples')
                for trial, ns in enumerate(samples, 1):
                    writer.writerow((*case, pair, pos, variant, trial, ns, cpu))
                observations[variant] = median(samples)
            ratios[case].append(observations['candidate'] / observations['base'])
for case in cases:
    print(f'{cohort} CPU {cpu}, {case}: {median(ratios[case]):.3f}x')
