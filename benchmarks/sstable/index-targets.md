# ALVSST06 index packing targets

This experiment uses the writer and reader at `1d389918`. It compares the
uniform index target with a 64 KiB minimum on levels above the leaf. The
runner builds both release executables from a scratch source tree. It
changes one target calculation in that tree and uses the same fixture and
reader in both executables. The checked-in code extends the benchmark fixture and runner.

```sh
export ELAN_HOME=/path/to/toolchains/elan
export PATH="$ELAN_HOME/bin:$PATH"
LC_ALL=C taskset -c 4 python3 benchmarks/sstable/measure-index-targets.py /tmp/index-target-results
```

The capture used Lean 4.36.0 (release), GCC 14.2.0 for the C/C++ helpers,
overlayfs on Linux 6.18.57 and CPU 4 on an AMD EPYC 9V74 guest. The same
deterministic data and query schedule as the paired benchmark cover four
layouts at 65,537, 1,000,000 and 4,000,000 rows. Each group checks the
returned values before reporting three warm read timings and one streaming
build time with flush. Builds run without file sync. The runner alternates
policy order between groups. Read traces exclude open, which checks and
retains the root. The raw `leaf_blocks` column counts every non-root index
page. The depth counts index levels, with the cached root included in
the depth. [Paired benchmark](recursive.md) · [Raw timings and read counts](index-targets.csv)

## Lookup results

The table uses 4 KiB data packets and a 1 KiB leaf target. The layouts
listed as variable have a variable-width key, value, or both. Latency
ranges summarize the warm sample medians for those three layouts.

| Rows | Layout | Height, uniform / upper 64 KiB | Index reads per hit, uniform / upper | Hit µs, uniform / upper |
| ---: | --- | --- | --- | --- |
| 65,537 | Fixed / fixed | 2 / 2 | 1 / 1 | 5.70 / 5.63 |
| 65,537 | Variable layouts | 3 / 2 | 2 / 1 | 8.68–9.01 / 5.53–5.91 |
| 1,000,000 | Fixed / fixed | 3 / 2 | 2 / 1 | 9.48 / 5.99 |
| 1,000,000 | Variable layouts | 3–4 / 2 | 2–3 / 1 | 9.79–13.24 / 6.59–6.63 |
| 4,000,000 | Fixed / fixed | 4 / 2 | 3 / 1 | 13.55 / 6.04 |
| 4,000,000 | Variable layouts | 4 / 3 | 3 / 2 | 13.43–14.36 / 159.43–171.24 |

At 65,537 rows the uniform 4 KiB index target also fits every layout in
two levels. Its hits take 12.75–13.73 µs because a request decodes a larger
leaf. At the normal 16 KiB data and 16 KiB index targets, the 65,537-row
tables fit in one index level and hit medians are 3.35–3.62 µs with the
uniform policy. At 1M and 4M rows the same targets yield two levels for
all layouts with both policies. Hit medians sit between 46 and 50 µs.

With a 1 KiB leaf and larger upper levels, every 1M-row layout keeps its
larger upper page in the cached root. Median open time rises from
3.6–4.9 µs to 25.1–77.6 µs. At 4M rows the fixed/fixed root is about
35 KiB and still cached. Each variable layout has at least one
uncached upper level. Its mean index bytes per hit grow from roughly
3 KiB to 58–61 KiB even though it makes one fewer index read. Misses that
descend the index show the same change. These traces count requested
bytes. Every fetched index page is decoded and validated as a whole.

For the writer-only memory capture, each sample starts a fresh process and
uses variable-width keys and values. Linux `wait4` reports peak RSS,
including the runtime. This measure excludes inventory, open and reads.
The table reports the median of three fresh processes per cell.
[Raw writer peak RSS samples](index-targets-rss.csv)

| Rows | Data / leaf target | Peak RSS KiB, uniform / upper 64 KiB | Build M rows/s, uniform / upper 64 KiB |
| ---: | --- | --- | --- |
| 65,537 | 4 KiB / 1 KiB | 13,228 / 13,352 | 2.55 / 2.48 |
| 65,537 | 16 KiB / 16 KiB | 15,348 / 15,396 | 2.69 / 2.63 |
| 4,000,000 | 4 KiB / 1 KiB | 13,268 / 15,220 | 2.50 / 2.50 |
| 4,000,000 | 16 KiB / 16 KiB | 15,364 / 15,344 | 2.70 / 2.47 |

## Packing decision

Keep the uniform writer policy for the general candidate. A larger upper
target helps a bounded workload that can keep the wide page at the root
and amortize opening it. An unconditional floor moves the expensive
decode into the lookup path once the table outgrows that root.

A true larger root target could defer emission of the current top
directory and repartition those buffered references into ordinary-sized
pages if it outgrows the root budget. The repartition would add a writer
transition and its coverage and progress proofs. Simply promoting the
oversized directory would reproduce the measured interior-page regression.
The current results support workload-specific tuning and measuring
fetched bytes alongside read counts before adding a spill transition.

The [index residency experiment](index-cache.md) compares both formats with a shared metadata byte budget and separates read traffic from validation.
