# Comparing ALVSST05 and ALVSST06 index residency

The experiment uses the uniform writer targets and the checked readers from
the paired benchmark. It measures both formats on the same generated keys
and values, across four layouts at 65,537, 1,000,000 and 4,000,000 rows.
The data and index target pairs are 4/1, 4/4 and 16/16 KiB. The last pair
uses the normal defaults. Each probe checks its result against the known
value or seek position. The 512 deterministic keys give 256 hits, 256
misses and 512 seeks. Build timings include flush. File sync is outside
the benchmark.

```sh
export ELAN_HOME=/path/to/toolchains/elan
export PATH="$ELAN_HOME/bin:$PATH"
taskset -c 4 bash benchmarks/sstable/run-index-cache.sh > /tmp/index-cache.csv
LC_ALL=C taskset -c 4 lean/.lake/build/bin/sstableIndexCacheBench 4000000 4096 1024 262144 > /tmp/index-cache-large-budget.csv
```

Measurements used Lean 4.36.0 release, Linux 6.18.57, GCC 14.2.0 for the
native helpers and overlayfs on CPU 4 of an AMD EPYC 9V74 guest. The
inventory pass touches the file metadata before timing. The Linux page
cache is left warm. A file read here means a positional request through
the native file source, with no assertion about physical disk accesses.
[Primary raw samples](index-cache.csv) · [256 KiB sensitivity samples](index-cache-large-budget.csv)

## Residency modes

- **No index cache.** Each probe runs checked open on the held file
  descriptor, with a fresh read and validation of the footer, root and
  any lower index pages. It retains no index packets between probes.
  The checked-open microbenchmark reports the footer/root cost separately
  from lookup and seek.
- **Default.** Checked open retains the decoded root, as in production.
  Each timed probe uses that already-open table and reads and decodes
  its selected lower pages.
- **Resident wire.** Each format has the same fixed 64 KiB budget for
  complete encoded index packets, including the root. A separate
  population step admits the root and then pages by descending height
  and ascending file offset. Whole packets that exceed the remaining
  budget are skipped. This is a static, query-independent policy with
  measured population cost and contents. A benchmark `Source` serves
  these bytes from memory. Each timed probe still uses checked open and
  validates every packet on its path, even a resident packet. The
  equivalent 256 KiB run repeats the largest narrow-index configuration.
- **Resident decoded model.** For the same admitted offsets, a
  trace-only counterfactual omits repeated validation of those pages.
  It reports the remaining checks and their separately measured decode
  replay cost. It provides no lookup latency or decoded heap estimate.

The wire budget charges the full encoded packet length. It measures
resident index payload bytes. The map, cache bookkeeping, allocator and
the benchmark's page catalog sit outside that budget. The default
mode's decoded root is visible through the `root_bytes` wire-size proxy.
The `resident_bytes` column tracks encoded cache payload, so it is zero
for the default mode.

The primary matrix has two independent sweeps and three warm wall-time
samples per measured operation in each sweep. An
independent trace records file-origin size, footer, index and data
requests, and memory hits separately. A third pass replays those index
packet decodes on already-read bytes, with exact CRC, decode, parent-row
bounds and fence checks. That replay excludes lookup selection, footer
checks, data decode and transport. The trace and replay are recorded
once per group. Repeated rows have independent operation timings and
share that group evidence.

A timed cache of validated Lean reference arrays would need a hook past
the byte `Source` in both readers, including at root installation. A
separate experimental traversal could also supply the decoded arrays.
Evaluating equal decoded memory across formats needs a policy for
charging the arrays and key allocations. This checkpoint measures a
controlled encoded budget on the shared checked-reader path and treats
decoded residency as the counterfactual described above.

## Results

The variable-key, variable-value layout at 4/1 KiB isolates the effect of
root residency. Times are medians over both sweeps. Read and byte counts
below include only file-origin index requests. The raw rows have separate
columns for data and footer requests.

| Rows | Residency | Hit µs, 05 / 06 | File index reads per hit, 05 / 06 |
| ---: | --- | ---: | ---: |
| 65,537 | Default | 5.52 / 8.99 | 1 / 2 |
| 65,537 | No index cache | 12.38 / 11.22 | 2 / 3 |
| 65,537 | Resident wire | 10.91 / 9.99 | 0 / 0 |
| 1,000,000 | Default | 8.34 / 12.45 | 1 / 3 |
| 1,000,000 | No index cache | 76.05 / 15.48 | 2 / 4 |
| 1,000,000 | Resident wire | 75.45 / 13.49 | 0.92 / 0.92 |
| 4,000,000 | Default | 6.99 / 13.34 | 1 / 3 |
| 4,000,000 | No index cache | 309.31 / 25.12 | 2 / 4 |
| 4,000,000 | Resident wire | 520.22 / 14.67 | 1.97 / 1.46 |

At 1M rows and 4/1 KiB, ALVSST05 has a 29,016-byte root and height two.
ALVSST06 has a 114-byte root and height four. Checked open takes about
70 and 2.3 µs respectively in the default mode. The files are
43,709,162 and 43,710,975 bytes, and median build time per row is roughly
0.37 and 0.45 µs in the recorded wall-time environment. Default miss
medians are 7.32 and 12.59 µs. Default seek medians are 6.47 and 12.87 µs.

In the 1M-row wire-cache case both formats make exactly 235 file-origin
index requests, totaling 233,832 bytes across 256 hits. The cache uses
64,842 bytes for 05 and 64,657 bytes for 06 under the same 65,536-byte
cap. Replayed validation takes roughly 68 and 8 µs per hit. Serving the
large 05 root from memory still leaves its repeated decode on the
path. With the same offsets treated as already decoded, each lookup
would retain on average fewer than one index validation, and replay
for the remaining pages is about 2.6 and 2.5 µs per hit.

At 4M rows with a 1 KiB index target, the 116,030-byte 05 root exceeds
the 64 KiB cap. Its requests fetch about 114 KiB of index data per hit
in the wire-cache mode. The 369-byte 06 root fits and that mode
fetches about 1.4 KiB per hit. Repeated decoding of the wide root
dominates this configuration. Wall time and replay measurements in
the shared VM can vary between sweeps. Use the read, byte and decode
counts for precise comparisons, and treat small timing differences
and the magnitude of the widest-page timings as workload observations.

At the normal 16/16 KiB defaults, all 65,537-row ALVSST06 layouts
have a single index level. Their default lookup reads only the data
packet after open. ALVSST05 loads one lower index page. At 1M and 4M
rows both formats use two index levels with these targets. The
default case then reads and decodes a lower index page on every hit.
Large index pages still incur that validation even when a wire cache
serves their bytes.

The 256 KiB repeat admits both roots in the largest 4/1 KiB
variable/variable case. File-origin index reads over 256 hits are
237 for 05 and 239 for 06. Every probe still validates its entire
index path in the measured wire-cache mode. In the modeled decoded
case those same 237 and 239 packets are the only ones left to
validate, with no conclusion here about actual decoded-cache latency.
