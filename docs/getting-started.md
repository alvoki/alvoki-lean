# Getting started

## Set up the pinned tools

From the repository root on Linux x86-64, run the following with Bash, `curl`, `tar`, `unzip`, `sha256sum`, Python 3, and a C compiler available as `cc`. Bootstrap installs Lean 4.36.0, Rust 1.100.0, and Verus 0.2026.11.22.1ce6a59. Set `ALVOKI_TOOLCHAINS` before running this block to choose a toolchain directory. The default is `../work/toolchains`.

```bash
bash scripts/bootstrap.sh "${ALVOKI_TOOLCHAINS:-../work/toolchains}"
export ALVOKI_TOOLCHAINS="$(cd "${ALVOKI_TOOLCHAINS:-../work/toolchains}" && pwd)"
export ELAN_HOME="$ALVOKI_TOOLCHAINS/elan"
export PATH="$ELAN_HOME/bin:$PATH"
```

## Write, close, and reopen a database

Run this block from the repository root. It creates a temporary Lake project and an empty database directory. Lake links the Linux adapter's native file operations and runs the example against the current checkout.

```bash
(
  set -e
  scratch=$(mktemp -d)
  trap 'rm -rf "$scratch"' EXIT
  mkdir "$scratch/db"
  ln -s "$PWD/lean" "$scratch/alvoki"
  cp lean/lean-toolchain "$scratch/lean-toolchain"

  cat > "$scratch/lakefile.toml" <<'EOF'
name = "alvoki-quickstart"

[[require]]
name = "alvoki"
path = "alvoki"

[[lean_exe]]
name = "quickstart"
root = "Quickstart"
EOF

  cat > "$scratch/Quickstart.lean" <<'EOF'
import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one database directory")
  let writer ← DiskTable.open path
  let sequence ← try
    writer.write 7 (some 42)
  finally
    writer.close

  let reader ← DiskTable.open path
  try
    let pin ← reader.acquire
    try
      let some (some value) ← reader.lookup pin.handle 7
        | throw (IO.userError "key 7 was missing after reopen")
      unless pin.sequence == sequence && value == 42 do
        throw (IO.userError "unexpected value or sequence after reopen")
      IO.println s!"Sequence {pin.sequence}, key 7 = {value}"
    finally
      reader.release pin.handle
  finally
    reader.close
EOF

  cd "$scratch"
  lake exe quickstart "$scratch/db"
)
```

The program prints `Sequence 1, key 7 = 42`. A write returns its sequence after durable WAL publication. A snapshot handle belongs to the session that acquired it, so the example acquires a fresh handle after reopening. Use an existing dedicated directory for each database, and release snapshot handles when you finish reading. [Sequential storage API](architecture.md#sequential-storage) · [Proof coverage and assumptions](verification-status.md)

## Build, test, and reproduce

Run these commands from the repository root in the same shell. The sequential suite checks the engine proofs, audits axiom dependencies, runs differential tests, and exercises native failure and recovery fixtures. The stock suite also checks the standalone Lean, Rust, and Verus implementations. [Correctness workflow](../.github/workflows/correctness.yml)

```bash
(cd lean && lake build Alvoki.Storage alvoki-disk-checks)
bash scripts/check-sequential.sh
bash scripts/check.sh
```

The reproduction script builds the baseline implementations and checks them against the Python reference. With `--out`, it also collects benchmark timings. Keep Python assertions enabled for the checks. The runtime option to `check.sh` runs the optional C and linkage experiments. [Benchmark workloads](performance/benchmarks.md)

```bash
bash scripts/reproduce.sh
bash scripts/reproduce.sh --out /tmp/alvoki-trials.csv --sizes 1000 --trials 3
python3 benchmarks/summarize.py /tmp/alvoki-trials.csv
bash scripts/environment.sh
bash scripts/check.sh --runtime
```

The disk replay benchmark measures native reopen with ascending, descending, and seeded shuffled insert orders. Use `--segments 1 8 32` with enough rows to compare segment layouts, and `--repair-tail` to exercise keeper repair. Compare medians on the same machine. Add `--max-slowdown 1.25` to fail a comparison if any median exceeds 125% of its baseline. [Disk replay benchmark](performance/benchmarks.md#disk-replay)

```bash
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv
```
