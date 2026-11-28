# ALVSST06 candidate

The candidate starts from main at `a375c871879e51558be60661d86f73b9cbaa904c`. The
[L0 read investigation](https://github.com/alvoki/alvoki-lean/pull/30)
provides the reached-state proof pattern. Keep ALVSST05 available as the
comparison path and build ALVSST06 in independent modules. Files require
rebuilding between formats.

## Recursive index

Keep the existing data body, index reference fields and byte ordering. Full
last keys are inclusive fences. A page covers a positive, contiguous row range.
Its ordered references partition that range and their file extents are
nonoverlapping and end at or before the parent offset. At height one the
references describe data. Otherwise they describe pages at exactly the
preceding height. Each page’s final fence equals its parent reference’s fence.
Use a single recursive image predicate, with the existing exact data packet
witness at its base. The caller still sees the same byte Table.Represents
contract, including arbitrary row-index cursors. The typed codec proof can
consume that contract unchanged.

The builder holds one pending data block and one pending array of references
per index height. It appends child packets before their parents. A new
reference triggers a flush only when the pending page has at least two
references and adding the new reference would exceed the target. Feed the
resulting reference to the next level and retain the new reference at the
original level. At finish, promote the fringe to existing upper levels until
the highest pending page can be written as the root. The empty table has
height zero and no root. A nonempty table always has an index root.

The minimum fan-out of a completed page is two. A final fringe page may have
one reference, so a level with n child references can deliver at most
ceil(n/2) pages upward. For n ≥ 2 this is strictly smaller than n. A highest
pending page is written as root, including in the singleton case. With at
most 2^63 − 1 data blocks, at most 63 index heights suffice. The executable
builder has the same height cap.

ALVSST05 allows an individual reference up to 16 MiB minus the CRC. Two such
references fit in 32 MiB including one CRC. Retain that individual key
bound and the 16 MiB data packet cap. Allow a logical index packet up to
32 MiB so the minimum fan-out also holds when both fences are maximal.
Split a read over 16 MiB into two exact positional requests and check the
CRC of the concatenation. This keeps the native allocation cap for each
request. Force a flush before a third entry would cross the configured
target. Alternatives include externalizing large fence keys, which adds
I/O to routing, and shortening fences, which may save little when adjacent
keys share a long prefix. Keep full fences in the first candidate to reuse
existing partition and fence reasoning.

The fixed trailer identifies ALVSST06, the existing layout and root extent,
and the root height. A packet's checksum context includes its format-specific
kind, expected table ID and offset. The kind distinguishes index heights. The
footer uses its own fixed context and carries the table ID, compared with
the independently supplied expected ID. Root extent must end at the trailer.
Check every selected edge before reading it. Positive packet lengths and
backward-only extents preclude cycles, even when a malformed file has
self-consistent checksum bytes. Height decreases in the reader independently
of those bytes. The checks protect the packets used by a call. Global
semantic correctness consumes the exact writer image.

Optional metadata can later live in independently framed packets with a
bounded directory referenced by a versioned trailer. Defer that machinery
until a consumer needs it. Compact references could remove implied starts or
encode bounded lengths more tightly. The 40-byte reference gives the first
candidate direct matches to existing wire and proof code.

## Proof and native handoff

Start with a small index target and one row per data packet. The append
producer must establish the exact packet bytes and bind its logical region
to the descriptor and frame at the current output cursor. Prove the
per-level pending-page invariant by induction over accepted references and
the exact append results. The flush creates the same recursive witness it
consumes one level up. The final footer points to this witness, and the
existing exclusive-create and flush/sync schedule publishes it on the same
descriptor. Directory publication stays with the caller.

Reuse the ALVSST05 data round-trip, typed transport and lower-bound partition
lemmas. Audit the metadata proof for reuse at the reference-decoder boundary.
Replace the fixed root/leaf image, builder and reader proofs. At read time
instantiate the PR #30 pattern with a pinned descriptor, exact successful
size and read results, and the caller's frame on both outcomes. Prove the
recursive descent once by induction on height. Use the same selected child
and local decoded row in the healthy reference and the fallible read
schedule. A failed selected read must preserve the reached frame and
propagate its error. Exercise a healthy hit, ordinary miss and a failed
interior read followed by a successful lookup. The acceptance proof starts
with the real supplier and append/sync result and ends with checked native
lookup. A fixture provides separate execution evidence.

## Membership filter decision

Use one ordinary Bloom filter per bounded data region, partitioned by the
same key ranges as the recursive index. Here partitioning means separate
filters for disjoint ordered key ranges. Choose a partition size after
measuring the additional positive lookup read against the data reads it can
save. The builder can use the exact rows already buffered for that region.
An empty or unprofitable mask can be omitted if the reader falls back.
A present filter gets a distinct CRC packet kind and a checked extent. It
must describe precisely the selected data region in the writer image. A
failed read or validation of a referenced filter is a lookup error. Missing
optional metadata invokes ordinary data lookup. Seek and next always use
the ordered data path.

Indicative space at about 1% false positives assumes uniform hashing and
adequately filled partitions. Packet and directory overhead are extra.
These are design estimates.

| Algorithm | Indicative bits/key | Query and construction tradeoff |
| --- | ---: | --- |
| Classic Bloom | 9.6 at 7 probes | Several scattered bit reads. For one whole table, either know the final size, grow via subfilters, or stage hashes. A fixed mask is simple to prove. |
| Blocked Bloom | Typically above 9.6 for comparable FPR | Probes stay in one cache block. Local occupancy and hashing affect FPR. Can stream into a sized partition with the same invariant plus block selection. |
| Key-range partitioned Bloom | 9.6 before rounding and metadata | One region mask per lookup. Sized from one existing bounded row buffer. Partition routing and insertion monotonicity are the main proof obligations. |
| Xor | About 10 at 8-bit fingerprints (~0.39% FPR) | Three array probes. Peeling needs the partition's keys or hashes, workspace and possible retries. The proof must also cover assignment and failed construction. |
| Binary Fuse | About 9–10 at 8-bit fingerprints (~0.39% FPR, size dependent) | Three probes. Better large-partition space than classic Xor. Segment sizing, retries and peeling require extra construction state and proof. |
| Ribbon | Can approach the information-theoretic 6.64 at 1%, with configuration-dependent overhead | Banded linear equations trade construction space and complexity for fewer persisted bits. A bounded region can stage its equations. The solver and query agreement need proof. |

See [Bloom analysis and double hashing](https://www.eecs.harvard.edu/~michaelm/postscripts/rsa2008.pdf),
[blocked Bloom](https://doi.org/10.1145/1498698.1594220),
[Xor](https://arxiv.org/abs/1912.08258),
[Binary Fuse](https://arxiv.org/abs/2201.01174),
[Ribbon](https://arxiv.org/abs/2103.02515).

Prove that the positions set by inserting a key stay set under all later
insertions. Attach the builder's actual mask to the same exact packet
witness as its data rows. The witness covers every accepted opaque value,
including a tombstone. On a successful negative filter test, derive absence
in the selected region and combine it with the fence partition to derive
public absence. The proof must consume the serialized mask through the
checked read path. CRC32C provides accidental corruption detection. It
does not authenticate arbitrary bytes. Measure FPR independently.

## Iterator and measurements

A later stateful cursor can hold the validated data packet and index path.
It advances inside that packet and climbs to the next sibling at the
boundary. Its proof should erase the path and retain the logical row
index and the protected read frame. Keep stateless arbitrary-index
iteration available. Compression, prefix-compressed data, direct I/O,
general caching and concurrency stay out of this candidate.

Use the existing native benchmark's deterministic workloads and correctness
oracles. Compare equal layouts, packet targets, warm-up and release settings.
Collect per-operation native samples, read calls and bytes, root depth,
construction throughput and process peak RSS. Record platform and raw data.
For filters also sample realistic in-range misses to estimate FPR and data
read avoidance. Test small-target deep trees separately from default targets.

## Candidate evidence

The native fixture writes the exact image through the existing synced
descriptor schedule and opens it with the expected ID. It covers every
layout, multiple heights, all cursors and key-boundary observations, a
reported read error followed by another lookup, and a root self-edge
with its CRC recomputed. It also forces two maximum-size fences into a
single logical page and reads it through the native adapter.

Lean proves the per-edge extents, two-reference capacity, metadata
round-trip and split reads. One induction over height routes both key
search and row-index cursors. The resulting `Image.open_represents`
proves public lookup, seek and arbitrary cursor behavior from the exact
recursive image. `checkedNativeLookup` uses the acquired descriptor and
gives the public lookup result on success with a preserved frame on
every returned outcome.

The kernel-checked vertical experiment runs the actual builder with
three ordered rows and minimum targets, proves the two-level image
at the synced inode, and composes it with checked open and public lookup.
It proves a healthy open and the public table contract, and derives the
framed lookup under local read primitive contracts for that inode.
The experiment uses a constant checksum to keep kernel reduction small.
The native fixture uses CRC32C and exercises the same executable schedules.
A universal producer theorem establishing the recursive image for arbitrary
successful builds remains open.
[Vertical Lean experiment](../../lean/Alvoki/Checks/Tests/RecursiveSSTableProducer.lean)

The paired measurements are recorded separately.
[Reproduction and raw measurements](../../benchmarks/sstable/recursive.md)
