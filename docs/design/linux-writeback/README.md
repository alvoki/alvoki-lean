# Lost Linux writeback

The current Alvoki proofs require a successful barrier to persist the selected
bytes. A failed block write can leave a clean cache page containing bytes
that a later successful `fsync` will never write. That state is outside the
current proved fault model. The experiment below reproduces it on ext4 and
XFS. [Filesystem assumptions](../filesystem-assumptions.md)

## Reproduce

From this directory on Linux x86-64, build the guest and QEMU runner with
Docker BuildKit. QEMU uses CPU emulation. The container needs neither KVM
nor host block devices. Each run creates a fresh sparse image, passes it
as the only guest disk and removes it on exit. Capture the serial output
to keep a run. For a TLS-inspecting network, pass a trusted CA bundle with
`--secret id=ca_bundle,src=/path/to/ca-certificates.crt` to the build.

```sh
docker build -t alvoki-writeback-research:local .
for fs in ext4 xfs; do
  for mode in buffered dsync direct direct-dsync; do
    bash run.sh "$fs" "$mode" --compare > "$fs-$mode.log" || exit
  done
done
```

A run without `--compare` succeeds when the guest reaches
`PROBE_COMPLETE` and the runner exits successfully. With `--compare`, it
also compares the observed return values, error codes, byte counts and
page flags against the [reference observations](reference). The same
references apply to both filesystems. A completed run with different
observations exits with status 3 and prints a unified diff on stderr.
The full serial log goes to stdout in either mode.

The pinned Alpine packages provide Linux `6.18.65-0-virt` (`linux-virt
6.18.65-r0`), QEMU 11.0.3, device-mapper 2.03.35, e2fsprogs 1.47.4 and
xfsprogs 7.0.1. Package versions are recorded in the [Dockerfile](Dockerfile).
Rebuilding those exact versions requires an Alpine mirror that still
serves them. The guest's 1 GiB raw disk uses virtio with QEMU `cache=none`.
ext4 uses `mkfs.ext4 -F -b 4096` and mounts with `data=ordered`. XFS uses
`mkfs.xfs -f -b size=4096 -m reflink=0` and mounts with default options.
Other mkfs settings use the pinned tools' defaults. The serial output
includes filesystem features or geometry and the actual mount options.

The reference runs used `rw,relatime,data=ordered` on ext4, with 256-byte
inodes, extents, 64-bit addressing and metadata checksums. XFS reported
`rw,relatime,inode64,logbufs=8,logbsize=32k,noquota`, with 512-byte sectors
and inodes, four allocation groups, metadata CRCs and an internal log
of 16384 blocks. Both used 4096-byte filesystem blocks.

## Fault and observations

1. Write a block of A bytes and sync the file and its parent. Find its
   physical extent with FIEMAP and check the baseline directly on the
   backing disk. The target is eight 512-byte sectors in the allocated
   data extent.
2. Close the initialization descriptor. Open the writer with the selected
   flags, a buffered reader and an independent peer description, in that
   order. Remap only the target range to the device-mapper `error` target,
   then issue the B overwrite and immediately call `fsync` on the writer.
3. Restore the linear mapping and compare the buffered read with a raw
   `O_DIRECT` read on the backing disk. In buffered mode, measure the
   mapped page's dirty and writeback flags via pagemap and kpageflags.
4. Open a fresh description **after** the writer has observed the failure.
   Sync the writer again, then the fresh description, then the peer that
   was open before the fault. Compare cache and backing again, evict the
   file page, and check what is visible. Finally rewrite the known B bytes
   and sync the fresh description.

Each row below was observed on **both** filesystems with a 4096-byte
overwrite. A and B stand for the complete old and new blocks.

| Mode | Overwrite `pwrite` | Writer's first `fsync` | Writer retry / fresh / peer `fsync` | Cache / backing after retries |
| --- | --- | --- | --- | --- |
| Buffered + `fsync` | 4096 | EIO | OK / OK / EIO | B / A |
| Buffered + `O_DSYNC` | EIO | OK | OK / OK / EIO | B / A |
| `O_DIRECT` + `fsync` | EIO | OK | OK / OK / OK | A / A |
| `O_DIRECT` + `O_DSYNC` | EIO | OK | OK / OK / OK | A / A |

In buffered mode the page contained B with `dirty=0` and `writeback=0`.
Eviction returned A in all runs. An explicit rewrite of the known B
bytes followed by a successful sync persisted B in all runs. The
pre-fault peer's EIO in the buffered cases shows that error consumption by
one description does not consume another description's outstanding
notification. A new description can still report a previously unseen
error. The open and sync order matters. [Linux VFS error reporting](https://github.com/torvalds/linux/blob/v6.18/Documentation/filesystems/vfs.rst#handling-errors-during-writeback)
· [Linux error cursor sampling](https://github.com/torvalds/linux/blob/v6.18/lib/errseq.c#L113)
· [Rebello et al., ATC 2020](https://www.usenix.org/conference/atc20/presentation/rebello)

This is a failed overwrite on an existing extent. It injects a real
block failure rather than replacing a userspace return code. It covers
neither the complete WAL schedule nor an actual power cut, and targets
data sectors only. File growth, delayed allocation, torn sectors,
metadata or journal faults and device cache failures were outside the
measurement. The host-backed image and cache eviction demonstrate the
observed difference between the guest page cache and backing bytes.

## Implications for the current components

- **Single-file WAL.** Reopen scans visible records and syncs the selected
  data. Log-only recovery could choose a complete pending record from the
  cache and report it as settled even though a later loss of that cache
  exposes the old block. The boundary variant relies on the corresponding
  premise for the selected marker slots. The experiment isolates the
  primitive counterexample underlying those hypothetical traces.
  [Recovery schedule](../../../lean/Alvoki/Experiments/WAL/Recovery.lean)
- **DurableBlob.** A reported staged-file sync error stops before rename.
  Reopen reads the active file and settles its directory binding. That
  directory barrier cannot recover data lost on the selected inode.
  [Publish and reopen](../../../lean/Alvoki/Experiments/DurableBlob/Protocol.lean)
- **Segmented WAL.** CONTROL stages and syncs before rename and the root
  barrier. Reopen settles the root before selecting and reading child
  WALs. Child recovery has the same data and marker premises as single-file
  recovery. The control and root barriers depend on their separate file
  and namespace assumptions. [Segmented protocol](../../../lean/Alvoki/Experiments/WAL/Segmented/Protocol.lean)

Process interruption can leave cached bytes visible. Power loss can
discard those bytes. A reported sync error after a completed effect is
compatible with the new bytes already being durable. Lost writeback can
instead leave stale backing bytes behind a clean cache page. A retry
barrier alone cannot distinguish these outcomes. Rewriting is a repair
option when the correct bytes are known and the new writes and barriers
succeed. Fail-stop requires a reliable way to gate reopening after a
reported storage failure. If previously acknowledged bytes disappear
from the only copy, recovery must be able to fail or obtain the bytes
from a redundant source. [Future WAL options](../wal-v2.md)
