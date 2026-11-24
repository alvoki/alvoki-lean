import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Publication.DiskPublicationModel

open System Alvoki Alvoki.Storage

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def rejects (action : IO α) (message : String) : IO Unit := do
  let rejected ← try
    let _ ← action
    pure false
  catch _ => pure true
  check rejected message

private def expectRejectedWrite (db : DiskTable) (cause : String) : IO Unit := do
  let .error (.rejected (.userError message)) ← (db.writeWithOutcome 12 (some 120)).toBaseIO
    | throw (IO.userError "write did not report a pre-append rejection")
  check (message == cause) "write rejection changed the cause"

private def expectManifest (dir : FilePath) (generation watermark floor runCount : UInt64) :
    IO Unit := do
  let header ← IO.FS.readBinFile (dir / "MANIFEST")
  let .ok manifest := Manifest.IntegrityCheckpoint.decode header
    | throw (IO.userError "cannot decode installed manifest")
  check (decide (manifest.header = ⟨generation, watermark, floor, runCount⟩)) "unexpected manifest"
  let files ← (List.range runCount.toNat).mapM fun index => IO.FS.readBinFile (dir / s!"run-{generation}-{index}.v3")
  check (manifest.validateRuns files) "manifest does not identify the exact ordered run files"

private def checkCodecs : IO Unit := do
  let first : WAL.Write := ⟨1, 4, some 40⟩
  let second : WAL.Write := ⟨2, 7, none⟩
  let bytes := WAL.encode [first, second]
  for tailSize in [:WAL.frameSize] do
    let third := WAL.encodeFrame ⟨3, 4, some 41⟩
    let .ok events := WAL.decode (bytes ++ third.extract 0 tailSize)
      | throw (IO.userError s!"WAL rejected incomplete tail length {tailSize}")
    check (decide (events = [first, second])) "a partial WAL frame applied a write"
  for offset in [:WAL.frameSize] do
    let corrupt := bytes.set! offset (bytes[offset]! ^^^ 1)
    check (failed (WAL.decode corrupt)) s!"WAL accepted corrupted byte {offset}"
  let fullDamage := ByteArray.mk (Array.replicate WAL.frameSize 0)
  check (failed (WAL.decode (bytes ++ fullDamage))) "WAL decoder ignored a damaged complete final frame"
  check (failed (recover (WAL.encode [second]))) "recovery accepted a gap"
  check (failed (recover (WAL.encode [first, first]))) "recovery accepted a duplicated sequence"
  check (failed (recover (WAL.encode [second, first]))) "recovery accepted reordered writes"
  let files := List.replicate 4 ByteArray.empty
  let valid := (Manifest.IntegrityCheckpoint.fromRuns ⟨5, 3, 2, 4⟩ files).encode
  for offset in [:valid.size] do
    check (failed (Manifest.IntegrityCheckpoint.decode (valid.set! offset (valid[offset]! ^^^ 1))))
      s!"manifest accepted corrupted byte {offset}"
  let invalidFloor := (Manifest.IntegrityCheckpoint.fromRuns ⟨5, 3, 4, 4⟩ files).encode
  check (failed (Manifest.IntegrityCheckpoint.decode invalidFloor))
    "manifest accepted a floor above its watermark"

private def checkReopen (dir : FilePath) : IO Unit := do
  let maxKey := UInt64.ofNat (UInt64.size - 1)
  let db ← DiskTable.open dir
  rejects (DiskTable.open dir) "two handles opened one database for writes"
  let .ok first ← (db.writeWithOutcome 4 (some 40)).toBaseIO
    | throw (IO.userError "typed write did not acknowledge a successful commit")
  check (first == 1) "first write sequence"
  check ((← db.write 7 (some 70)) == 2) "second write sequence"
  check ((← db.write maxKey (some 99)) == 3) "third write sequence"
  let old ← db.acquire
  db.checkpoint
  expectManifest dir 1 3 0 1
  check ((← db.write 4 (some 41)) == 4) "overwrite sequence"
  check ((← db.write 7 none) == 5) "delete sequence"
  db.checkpoint
  expectManifest dir 2 5 0 2
  check (← db.advanceFloor 3) "active snapshot should allow its own floor"
  check (!(← db.advanceFloor 4)) "floor advanced above an active snapshot"
  check (← db.compact 0) "compaction rejected adjacent files"
  db.checkpoint
  expectManifest dir 3 5 3 1
  check ((← db.lookup old.handle 4) == some (some 40)) "compaction lost pinned older value"
  check ((← db.range old.handle 0 maxKey).map (List.map (·.key)) == some [4, 7])
    "compaction changed pinned range or included the exclusive endpoint"
  check ((← db.write 8 (some 80)) == 6) "post-checkpoint sequence"
  db.close
  rejects (db.acquire) "closed database accepted reads"
  let wal := dir / "WAL"
  let complete ← IO.FS.readBinFile wal
  let marker := dir / "WAL.commit"
  let boundary ← IO.FS.readBinFile marker
  expectRejectedWrite db "database is closed"
  check (decide ((← IO.FS.readBinFile wal) = complete ∧ (← IO.FS.readBinFile marker) = boundary))
    "rejected write changed the WAL or its marker"
  let next := (WAL.encodeFrame ⟨7, 9, some 90⟩).extract 0 11
  IO.FS.writeBinFile wal (complete ++ next)
  let reopened ← DiskTable.open dir
  check ((← IO.FS.readBinFile wal).size == complete.size) "torn WAL suffix remains in the file"
  check ((← reopened.acquireAt 2).isNone) "reopen lost persisted retention floor"
  let some historical ← reopened.acquireAt 3 | throw (IO.userError "reopen lost historical snapshot")
  let latest ← reopened.acquire
  check (latest.sequence == 6) "reopen did not restore the acknowledged watermark"
  check ((← reopened.lookup historical.handle 7) == some (some 70)) "old value did not survive reopen"
  check ((← reopened.lookup latest.handle 4) == some (some 41)) "overwrite did not survive reopen"
  check ((← reopened.lookup latest.handle 7) == some none) "delete did not survive reopen"
  check ((← reopened.lookup latest.handle maxKey) == some (some 99)) "maximum key was not restored"
  check ((← reopened.lookup latest.handle 8) == some (some 80)) "complete WAL suffix was not replayed"
  check ((← reopened.lookup latest.handle 9) == some none) "torn WAL tail was applied"
  check ((← reopened.write 9 (some 91)) == 7) "could not append after torn-tail repair"
  reopened.close
  let final ← DiskTable.open dir
  let pin ← final.acquire
  check ((← final.range pin.handle 0 maxKey).map (List.map (·.key)) == some [4, 8, 9])
    "unexpected latest range after reopen and further append"
  final.close

private def checkInterruptedPublication (dir : FilePath) : IO Unit := do
  let db ← DiskTable.open dir
  let _ ← db.write 2 (some 20)
  db.checkpoint
  let _ ← db.write 2 (some 25)
  let staged := dir / "MANIFEST.next"
  IO.FS.createDir staged
  rejects db.checkpoint "checkpoint published through a blocked staging path"
  expectManifest dir 1 1 0 1
  check (← (dir / "run-2-1.v3").pathExists) "fixture did not reach the manifest write"
  rejects (db.write 3 (some 30)) "poisoned database accepted another write"
  rejects db.acquire "poisoned database accepted reads"
  db.close
  IO.FS.removeDir staged
  let reopened ← DiskTable.open dir
  let pin ← reopened.acquire
  check (pin.sequence == 2) "old manifest did not allow replay of the acknowledged suffix"
  check ((← reopened.lookup pin.handle 2) == some (some 25)) "reopen lost acknowledged data"
  reopened.checkpoint
  expectManifest dir 2 2 0 2
  reopened.close

private def checkMissingAndMalformedFiles (dir : FilePath) : IO Unit := do
  let db ← DiskTable.open dir
  let _ ← db.write 2 (some 20)
  db.checkpoint
  db.close
  let run := dir / "run-1-0.v3"
  let original ← IO.FS.readBinFile run
  IO.FS.removeFile run
  rejects (DiskTable.open dir) "open accepted a missing referenced run"
  IO.FS.writeBinFile run (original.extract 0 (original.size - 1))
  rejects (DiskTable.open dir) "open accepted a truncated referenced run"
  IO.FS.writeBinFile run original
  IO.FS.writeBinFile (dir / "MANIFEST") (Manifest.IntegrityCheckpoint.fromRuns ⟨1, 0, 0, 1⟩ [original]).encode
  rejects (DiskTable.open dir) "open accepted a run newer than the checkpoint watermark"
  IO.FS.writeBinFile (dir / "MANIFEST") (Manifest.IntegrityCheckpoint.fromRuns ⟨1, 1, 0, 1⟩ [original]).encode
  let wal := dir / "WAL"
  let frames ← IO.FS.readBinFile wal
  IO.FS.removeFile wal
  rejects (DiskTable.open dir) "open accepted a checkpoint without its WAL"
  IO.FS.writeBinFile wal frames
  let restored ← DiskTable.open dir
  let pin ← restored.acquire
  check ((← restored.lookup pin.handle 2) == some (some 20)) "failed opens kept the lock or changed the data"
  restored.close

private def checkCoveredWalDuplicate (dir : FilePath) : IO Unit := do
  let db ← DiskTable.open dir
  let _ ← db.write 1 (some 10)
  let _ ← db.write 2 (some 20)
  let _ ← db.write 3 (some 30)
  db.checkpoint
  db.close
  expectManifest dir 1 3 0 1
  let wal := dir / "WAL"
  let original ← IO.FS.readBinFile wal
  let duplicate := original.extract WAL.frameSize (2 * WAL.frameSize)
  let corrupted := original.extract 0 (2 * WAL.frameSize) ++ duplicate
  check (corrupted.size == original.size) "duplicate frame changed the selected byte count"
  let .ok events := WAL.decode corrupted | throw (IO.userError "duplicate frame was not checksum-valid")
  check (events.map (·.sequence) == [1, 2, 2]) "fixture did not duplicate a covered frame"
  IO.FS.writeBinFile wal corrupted
  rejects (do (← DiskTable.open dir).close) "open accepted a checksum-valid duplicate below the checkpoint watermark"
  IO.FS.writeBinFile wal original
  let reopened ← DiskTable.open dir
  let pin ← reopened.acquire
  check ((← reopened.lookup pin.handle 3) == some (some 30)) "valid checkpoint did not survive the fixture"
  reopened.close

private def checkBoundedRecovery (dir : FilePath) : IO Unit := do
  let wal := dir / "WAL"
  let marker := dir / "WAL.commit"
  let event : WAL.Write := ⟨1, 3, some 81⟩
  let durable := WAL.encodeFrame event
  -- A valid legacy log is migrated on open.
  IO.FS.writeBinFile wal (durable ++ (WAL.encodeFrame ⟨2, 3, some 82⟩).extract 0 7)
  (← DiskTable.open dir).close
  let committed ← IO.FS.readBinFile marker
  let .ok count := WAL.Boundary.decode committed | throw (IO.userError "invalid migrated boundary")
  check (count == WAL.frameSize.toUInt64)
    "legacy open did not install the recovered boundary"
  let fullTear := ByteArray.mk (Array.replicate WAL.frameSize 0)
  for tail in [fullTear, WAL.encodeFrame ⟨2, 3, some 82⟩, fullTear ++ fullTear] do
    IO.FS.writeBinFile wal (durable ++ tail)
    let reopened ← DiskTable.open dir
    try
      let pin ← reopened.acquire
      check (pin.sequence == 1 && (← reopened.lookup pin.handle 3) == some (some 81))
        "recovery exposed data past the durable boundary"
      check (decide ((← IO.FS.readBinFile wal) = durable)) "uncommitted tail was not removed"
    finally reopened.close
  IO.FS.writeBinFile wal (durable.extract 0 47)
  rejects (DiskTable.open dir) "open accepted a WAL shorter than the durable boundary"
  IO.FS.writeBinFile wal fullTear
  rejects (DiskTable.open dir) "open discarded corruption inside the durable boundary"
  IO.FS.writeBinFile wal durable
  IO.FS.writeBinFile marker (WAL.Boundary.encode 1)
  rejects (DiskTable.open dir) "open accepted a misaligned durable boundary"
  IO.FS.writeBinFile marker (committed.set! 16 (committed[16]! ^^^ 1))
  rejects (DiskTable.open dir) "open accepted a corrupted durable boundary"
  IO.FS.writeBinFile marker committed
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.write 3 (some 83)) == 2) "trimmed log did not resume at the next sequence"
  finally reopened.close

private def checkDirectoryIdentity (dir : FilePath) : IO Unit := do
  let first := dir / "first"
  let second := dir / "second"
  IO.FS.createDirAll (first / "db")
  IO.FS.createDirAll (second / "db")
  let original ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir first
    let a ← DiskTable.open "db"
    try
      rejects (DiskTable.open "./db") "a path alias bypassed the database lock"
      IO.Process.setCurrentDir second
      let b ← DiskTable.open "db"
      try
        check ((← a.write 7 (some 42)) == 1) "unexpected write sequence in the first database"
        a.checkpoint
        check ((← IO.FS.readBinFile (first / "db" / "WAL")).size == WAL.frameSize)
          "relative open lost its WAL after changing the working directory"
        expectManifest (first / "db") 1 1 0 1
        check ((← IO.FS.readBinFile (second / "db" / "WAL")).isEmpty)
          "write was redirected to another database after changing the working directory"
        let otherManifest ← (second / "db" / "MANIFEST").pathExists
        check (!otherManifest) "checkpoint was redirected to another database"
      finally b.close
    finally a.close
    let restored ← DiskTable.open (first / "db")
    try
      let pin ← restored.acquire
      check ((← restored.lookup pin.handle 7) == some (some 42))
        "original database lost its acknowledged value after reopen"
    finally restored.close
  finally IO.Process.setCurrentDir original

private def checkDanglingFiles (dir : FilePath) : IO Unit := do
  for name in ["MANIFEST", "WAL.commit", "WAL"] do
    let linked := dir / name
    let missing := dir / "missing"
    let result ← IO.Process.output {
      cmd := "ln", args := #["-s", "--", missing.toString, linked.toString] }
    check (result.exitCode == 0) "could not create dangling database file fixture"
    rejects (DiskTable.open dir) s!"open treated a dangling {name} as absent"
    let targetExists ← missing.pathExists
    check (!targetExists) s!"open created the target of a dangling {name}"
    IO.FS.removeFile linked

private def checkSnapshotSessions (root : FilePath) : IO Unit := do
  let firstDir := root / "first"
  let secondDir := root / "second"
  IO.FS.createDir firstDir
  IO.FS.createDir secondDir
  let original ← DiskTable.open firstDir
  let stale ← try
    let _ ← original.write 7 (some 70)
    original.acquire
  finally original.close
  let first ← DiskTable.open firstDir
  try
    let second ← DiskTable.open secondDir
    try
      let _ ← second.write 7 (some 71)
      -- Each acquisition is the first in its session, so the local IDs agree.
      let firstPin ← first.acquire
      let secondPin ← second.acquire
      for (db, valid, invalid, value, label) in
          [(first, firstPin.handle, stale.handle, 70, "stale"),
           (first, firstPin.handle, secondPin.handle, 70, "foreign"),
           (second, secondPin.handle, firstPin.handle, 71, "foreign")] do
        check ((← db.lookup invalid 7).isNone) s!"{label} handle resolved a point read"
        check ((← db.range invalid 0 8).isNone) s!"{label} handle resolved a range read"
        db.release invalid
        check ((← db.lookup valid 7) == some (some value)) s!"{label} release removed a live pin"
        check ((← db.range valid 0 8).map (List.map (·.payload)) == some [some value])
          s!"{label} release changed a live pin's range"
      rejects (original.lookup firstPin.handle 7) "closed database accepted a foreign lookup"
      rejects (original.range firstPin.handle 0 8) "closed database accepted a foreign range"
      rejects (original.release firstPin.handle) "closed database accepted a foreign release"
    finally second.close
  finally first.close

private def syncFixture : String := r#"#!/bin/sh
set -eu
mode=${ALVOKI_CHECK_SYNC_FAIL_MODE-before}
if [ "$mode" = second-only ] && [ "$#" -eq 3 ] && [ "$1" = -- ] &&
   [ "$3" = "${ALVOKI_CHECK_SYNC_FAIL-}" ]; then
  printf '%s\n' "$2" "$3" >> "$ALVOKI_CHECK_SYNC_LOG"
  command -p sync -- "$3"
  printf 'synced second target before error: %s\n' "$3" >> "$ALVOKI_CHECK_SYNC_LOG"
  printf 'injected sync failure: %s\n' "$3" >&2
  exit 1
fi
for path do
  [ "$path" = -- ] && continue
  printf '%s\n' "$path" >> "$ALVOKI_CHECK_SYNC_LOG"
  if [ "$mode" != second-only ] && [ "$path" = "${ALVOKI_CHECK_SYNC_FAIL-}" ]; then
    seen=$(grep -Fxc -- "$path" "$ALVOKI_CHECK_SYNC_LOG")
    skip=${ALVOKI_CHECK_SYNC_SKIP-0}
    if [ "$seen" -gt "$skip" ] && { [ "$mode" != before-once ] || [ "$seen" -eq "$((skip + 1))" ]; }; then
      if [ "$mode" = after ]; then
        [ "$#" -eq 2 ]
        [ "$1" = -- ]
        command -p sync -- "$path"
        printf 'synced before error: %s\n' "$path" >> "$ALVOKI_CHECK_SYNC_LOG"
      fi
      printf 'injected sync failure: %s\n' "$path" >&2
      exit 1
    fi
  fi
  command -p sync -- "$path"
done
"#

private inductive SyncFailureMode where
  | beforeSync
  | beforeOnce
  | afterSync
  | secondOnly

private def probeDisk (bin dir : FilePath) (failAt : Option FilePath) (operation := "--open-once")
    (skipFailures : Nat := 0) (failureMode : SyncFailureMode := .beforeSync)
    (extraArgs : Array String := #[]) :
    IO (Bool × List String) := do
  let log := bin / "sync.log"
  IO.FS.writeFile log ""
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let executable ← IO.appPath
  let mode := match failureMode with
    | .beforeSync => "before"
    | .beforeOnce => "before-once"
    | .afterSync => "after"
    | .secondOnly => "second-only"
  let result ← IO.Process.output {
    cmd := executable.toString
    args := #[operation, dir.toString] ++ extraArgs
    env := #[("PATH", some (bin.toString ++ ":" ++ path)),
      ("ALVOKI_CHECK_SYNC_LOG", some log.toString),
      ("ALVOKI_CHECK_SYNC_FAIL", failAt.map FilePath.toString),
      ("ALVOKI_CHECK_SYNC_SKIP", some (toString skipFailures)),
      ("ALVOKI_CHECK_SYNC_FAIL_MODE", some mode)] }
  let paths := (← IO.FS.readFile log).splitOn "\n" |>.filter (!·.isEmpty)
  return (result.exitCode == 0, paths)

private def syncFixtureBin (root : FilePath) : IO FilePath := do
  let bin := root / "bin"
  IO.FS.createDir bin
  let wrapper := bin / "sync"
  IO.FS.writeFile wrapper syncFixture
  let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", "--", wrapper.toString] }
  check (chmod.exitCode == 0) "could not make sync fault fixture executable"
  return bin

private def checkRetrySync (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let wal := dir / "WAL"
  let expected := [wal.toString, dir.toString]
  for _ in [:2] do
    let (opened, syncs) ← probeDisk bin dir (some dir)
    check (!opened && syncs == expected) "open accepted a WAL name after failed directory sync"
    check (← wal.pathExists) "sync failure did not leave a visible WAL to retry"
  let stagedBoundary := dir / "WAL.commit.next"
  let (opened, syncs) ← probeDisk bin dir none
  check (opened && syncs == expected ++ [stagedBoundary.toString, dir.toString])
    "successful retry did not settle the WAL and its initial boundary"
  let db ← DiskTable.open dir
  let _ ← db.write 7 (some 60)
  db.close
  let acknowledged ← IO.FS.readBinFile wal
  IO.FS.writeBinFile wal (acknowledged ++ (WAL.encodeFrame ⟨2, 7, some 99⟩).extract 0 11)
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [(dir / "WAL.next").toString, dir.toString])
    "fixture did not interrupt torn-tail repair after rename"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged)) "repair rename did not become visible"
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == expected) "repair retry skipped sync for an aligned WAL"
  let (opened, syncs) ← probeDisk bin dir none
  check (opened && syncs == expected) "successful repair retry skipped the recovery sync"
  let (written, syncs) ← probeDisk bin dir (some stagedBoundary) (operation := "--write-once")
  check (!written && syncs == expected ++ [wal.toString, stagedBoundary.toString])
    "fixture did not fail after WAL sync and before durable boundary publication"
  check ((← IO.FS.readBinFile wal).size == acknowledged.size + WAL.frameSize)
    "fixture did not leave a complete unacknowledged WAL frame"
  let recovered ← DiskTable.open dir
  try
    let pin ← recovered.acquire
    check (pin.sequence == 1 && (← recovered.lookup pin.handle 7) == some (some 60))
      "repair retry lost its acknowledged prefix"
    check ((← recovered.write 7 (some 61)) == 2) "append after repair retry used the wrong sequence"
  finally recovered.close
  let (written, syncs) ← probeDisk bin dir (some dir) (operation := "--write-once") (skipFailures := 1)
  check (!written && syncs == expected ++ [wal.toString, stagedBoundary.toString, dir.toString])
    "fixture did not fail after the boundary rename"
  let recovered ← DiskTable.open dir
  try
    let pin ← recovered.acquire
    check (pin.sequence == 3 && (← recovered.lookup pin.handle 7) == some (some 99))
      "reopen did not settle the visible boundary after failed directory sync"
  finally recovered.close

private def checkWritesAcrossReopens (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected initial write sequence"
    check ((← db.write 7 (some 70)) == 2) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 2) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 3) "unexpected overwrite sequence"
    check ((← db.write 7 none) == 4) "unexpected tombstone sequence"
    check ((← db.write 6 (some 60)) == 5) "unexpected insertion sequence"
  finally db.close
  let wal := dir / "WAL"
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.commit.next"
  let manifest := dir / "MANIFEST"
  let run := dir / "run-1-0.v3"
  expectManifest dir 1 2 2 1
  let manifestBytes ← IO.FS.readBinFile manifest
  let runBytes ← IO.FS.readBinFile run
  let expectCheckpoint := do
    check (decide ((← IO.FS.readBinFile manifest) = manifestBytes ∧ (← IO.FS.readBinFile run) = runBytes))
      "write and reopen trace changed the fixed checkpoint"
  let expectFiles := fun (events : List WAL.Write) => do
    let encoded := WAL.encode events
    check (decide ((← IO.FS.readBinFile wal) = encoded ∧
      (← IO.FS.readBinFile marker) = WAL.Boundary.encode encoded.size.toUInt64))
      "write and reopen trace changed the selected WAL history"
    expectCheckpoint
  let expectSnapshot := fun (db : DiskTable) (sequence : UInt64)
      (expected : List (UInt64 × Option UInt64)) => do
    let some pin ← db.acquireAt sequence
      | throw (IO.userError s!"missing retained snapshot at sequence {sequence}")
    try
      let rows := (← db.range pin.handle 0 8).map (List.map fun row => (row.key, row.payload))
      check (rows == some expected) s!"unexpected retained range at sequence {sequence}"
      for key in [:8] do
        let value := (expected.find? (·.1 == key.toUInt64)).bind (·.2)
        check ((← db.lookup pin.handle key.toUInt64) == some value)
          s!"unexpected point read of key {key} at sequence {sequence}"
    finally db.release pin.handle
  let acknowledged : List WAL.Write := [⟨1, 4, some 40⟩, ⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩,
    ⟨4, 7, none⟩, ⟨5, 6, some 60⟩]
  expectFiles acknowledged
  -- The first directory target belongs to the grouped sync during open.
  let (classified, syncs) ← probeDisk bin dir (some dir) (operation := "--check-write-outcome")
    (skipFailures := 1) (failureMode := .afterSync)
  let expectedSyncs := [wal.toString, dir.toString, wal.toString, staged.toString, dir.toString,
    s!"synced before error: {dir}"]
  check (classified && syncs == expectedSyncs)
    "write did not report an unknown commit after the final directory sync succeeded"
  let events := acknowledged ++ [⟨6, 7, some 99⟩]
  expectFiles events
  -- These failed reopen processes exercise the visible files around two sync
  -- outcomes. Power-loss choices for unsynced files belong to the model.
  let alignedSyncs := [wal.toString, dir.toString]
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == alignedSyncs) "reopen did not fail before syncing the directory"
  expectFiles events
  let (opened, syncs) ← probeDisk bin dir (some dir) (failureMode := .secondOnly)
  check (!opened && syncs == alignedSyncs ++ [s!"synced second target before error: {dir}"])
    "reopen did not fail after syncing only the directory"
  expectFiles events
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.acquireAt 1).isNone) "reopen lost the checkpoint floor"
    check ((← reopened.acquire).sequence == 6) "reopen lost the durable write with an unknown outcome"
    expectSnapshot reopened 2 [(4, some 40), (7, some 70)]
    expectSnapshot reopened 4 [(4, some 41)]
    expectSnapshot reopened 6 [(4, some 41), (6, some 60), (7, some 99)]
    expectFiles events
    check ((← reopened.write 4 none) == 7) "append reused the surviving write's sequence"
    check ((← reopened.write 7 none) == 8) "second append did not continue the selected history"
  finally reopened.close
  let continued := events ++ [⟨7, 4, none⟩, ⟨8, 7, none⟩]
  expectFiles continued
  -- This writer has reopened the same checkpoint. Its append would revive
  -- key 7, but the grouped sync fails before the staged marker is renamed.
  let (classified, syncs) ← probeDisk bin dir (some staged) (operation := "--check-write-outcome")
    (failureMode := .secondOnly)
  check (classified && syncs == alignedSyncs ++ [wal.toString, staged.toString,
    s!"synced second target before error: {staged}"])
    "the later session did not report an unknown commit before publishing its marker"
  let durable := WAL.encode continued
  let appended := durable ++ WAL.encodeFrame ⟨9, 7, some 99⟩
  check (decide ((← IO.FS.readBinFile wal) = appended ∧
    (← IO.FS.readBinFile staged) = WAL.Boundary.encode appended.size.toUInt64 ∧
    (← IO.FS.readBinFile marker) = WAL.Boundary.encode durable.size.toUInt64))
    "the later failed append did not leave its full frame outside the active marker"
  expectCheckpoint
  let reopened ← DiskTable.open dir
  try
    expectFiles continued
    check ((← reopened.acquire).sequence == 8) "later reopen selected the failed append"
    expectSnapshot reopened 6 [(4, some 41), (6, some 60), (7, some 99)]
    expectSnapshot reopened 8 [(6, some 60)]
    check ((← reopened.write 5 (some 50)) == 9) "reopen did not reuse the discarded write sequence"
  finally reopened.close
  let finalEvents := continued ++ [⟨9, 5, some 50⟩]
  let reopened ← DiskTable.open dir
  try
    expectFiles finalEvents
    check ((← reopened.acquire).sequence == 9) "final reopen lost the replacement append"
    expectSnapshot reopened 6 [(4, some 41), (6, some 60), (7, some 99)]
    expectSnapshot reopened 8 [(6, some 60)]
    expectSnapshot reopened 9 [(5, some 50), (6, some 60)]
  finally reopened.close

private def checkGroupedSyncPartialEffects (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    check ((← db.write 7 (some 70)) == 1) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 1) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 2) "unexpected acknowledged suffix sequence"
  finally db.close
  let wal := dir / "WAL"
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.commit.next"
  let acknowledged := WAL.encode [⟨1, 7, some 70⟩, ⟨2, 4, some 41⟩]
  let oldMarker := WAL.Boundary.encode acknowledged.size.toUInt64
  let (opened, syncs) ← probeDisk bin dir (some dir) (failureMode := .secondOnly)
  check (!opened && syncs == [wal.toString, dir.toString, s!"synced second target before error: {dir}"])
    "aligned reopen did not fail after syncing only the directory"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged ∧ (← IO.FS.readBinFile marker) = oldMarker))
    "failed aligned reopen changed the acknowledged WAL"
  let (classified, syncs) ← probeDisk bin dir (some staged) (operation := "--check-write-outcome")
    (failureMode := .secondOnly)
  check (classified && syncs == [wal.toString, dir.toString, wal.toString, staged.toString,
    s!"synced second target before error: {staged}"])
    "write did not report an unknown commit after syncing only the staged marker"
  let appended := acknowledged ++ WAL.encodeFrame ⟨3, 7, some 99⟩
  check (decide ((← IO.FS.readBinFile wal) = appended ∧
    (← IO.FS.readBinFile staged) = WAL.Boundary.encode appended.size.toUInt64))
    "failed staging sync did not leave the complete append and staged marker"
  check (decide ((← IO.FS.readBinFile marker) = oldMarker)) "failed staging sync published the new marker"
  let reopened ← DiskTable.open dir
  try
    expectManifest dir 1 1 1 1
    check (decide ((← IO.FS.readBinFile wal) = acknowledged)) "reopen did not trim the unacknowledged append"
    check ((← reopened.acquireAt 0).isNone) "reopen lost the checkpoint floor"
    let some historical ← reopened.acquireAt 1 | throw (IO.userError "reopen lost the checkpoint snapshot")
    let oldRows := (← reopened.range historical.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check (oldRows == some [(7, some 70)]) "reopen changed the retained snapshot range"
    let latest ← reopened.acquire
    check (latest.sequence == 2 && (← reopened.lookup latest.handle 4) == some (some 41) &&
      (← reopened.lookup latest.handle 7) == some (some 70)) "reopen changed the selected WAL history"
  finally reopened.close

private def checkCheckpointReadFailureBeforeWalRepair (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    check ((← db.write 7 (some 70)) == 1) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 1) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 2) "unexpected acknowledged suffix sequence"
  finally db.close
  let run := dir / "run-1-0.v3"
  let wal := dir / "WAL"
  let marker := dir / "WAL.commit"
  let manifest := dir / "MANIFEST"
  let stagedWal := dir / "WAL.next"
  let stagedMarker := dir / "WAL.commit.next"
  let runBytes ← IO.FS.readBinFile run
  let acknowledged ← IO.FS.readBinFile wal
  let markerBytes ← IO.FS.readBinFile marker
  let manifestBytes ← IO.FS.readBinFile manifest
  let untrimmed := acknowledged ++ WAL.encodeFrame ⟨3, 7, some 99⟩
  let expectNoWalEffects := fun expectedManifest => do
    let (opened, syncs) ← probeDisk bin dir none
    check (!opened && syncs.isEmpty) "failed checkpoint read reached the WAL sync protocol"
    check (decide ((← IO.FS.readBinFile wal) = untrimmed ∧
      (← IO.FS.readBinFile marker) = markerBytes ∧ (← IO.FS.readBinFile manifest) = expectedManifest))
      "failed checkpoint read changed WAL or metadata bytes"
    check (!(← stagedWal.pathExists) && !(← stagedMarker.pathExists))
      "failed checkpoint read created a WAL staging file"
  IO.FS.writeBinFile wal untrimmed
  IO.FS.removeFile run
  IO.FS.createDir run
  match ← (DiskTable.open dir).toBaseIO with
  | .error (.inappropriateType _ osCode _) =>
    check (osCode == 21) "installed run directory did not cause Linux EISDIR"
  | .error error => throw error
  | .ok opened =>
    opened.close
    throw (IO.userError "open accepted a directory as an installed run")
  expectNoWalEffects manifestBytes
  IO.FS.removeDir run
  let corrupt := Compaction.encodeV3 [⟨7, 1, (0, 71)⟩]
  check (corrupt.size == runBytes.size) "integrity fixture did not preserve the run length"
  IO.FS.writeBinFile run corrupt
  match ← (DiskTable.open dir).toBaseIO with
  | .error (.userError message) =>
    check (message == checkpointIntegrityMismatch) "same-length corruption bypassed the integrity check"
  | .error error => throw error
  | .ok opened =>
    opened.close
    throw (IO.userError "open accepted a different run with the same length")
  expectNoWalEffects manifestBytes
  IO.FS.writeBinFile run runBytes
  let legacyManifest := Manifest.encode ⟨1, 1, 1, 1⟩
  IO.FS.writeBinFile manifest legacyManifest
  expectNoWalEffects legacyManifest
  IO.FS.writeBinFile manifest manifestBytes
  let (opened, syncs) ← probeDisk bin dir none
  check (opened && syncs == [stagedWal.toString, dir.toString])
    "restored checkpoint did not allow the WAL repair syncs"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged ∧ (← IO.FS.readBinFile marker) = markerBytes))
    "retry did not trim exactly the unselected WAL tail"
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.acquireAt 0).isNone) "retry lost the checkpoint floor"
    let some historical ← reopened.acquireAt 1 | throw (IO.userError "retry lost the checkpoint snapshot")
    let oldRows := (← reopened.range historical.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check (oldRows == some [(7, some 70)]) "retry changed the retained snapshot range"
    let latest ← reopened.acquire
    check (latest.sequence == 2 && (← reopened.lookup latest.handle 4) == some (some 41) &&
      (← reopened.lookup latest.handle 7) == some (some 70)) "retry changed the acknowledged data"
  finally reopened.close

private def checkFirstCheckpointCuts (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected initial checkpoint sequence"
  finally db.close
  let run := dir / "run-1-0.v3"
  let staged := dir / "MANIFEST.next"
  let beforePublish := [(dir / "WAL").toString, dir.toString, run.toString, dir.toString]
  let (published, syncs) ← probeDisk bin dir (some dir) (operation := "--checkpoint-once") (skipFailures := 1)
  check (!published && syncs == beforePublish) "first checkpoint did not stop at the run directory sync"
  check (!(← (dir / "MANIFEST").pathExists)) "first checkpoint installed a manifest before its runs were synced"
  let (published, syncs) ← probeDisk bin dir (some dir) (operation := "--checkpoint-once") (skipFailures := 2)
  check (!published && syncs == beforePublish ++ [staged.toString, dir.toString])
    "first checkpoint did not reach the directory sync after manifest rename"
  expectManifest dir 1 1 0 1
  let reopened ← DiskTable.open dir
  try
    let pin ← reopened.acquire
    check (pin.sequence == 1 && (← reopened.lookup pin.handle 4) == some (some 40))
      "reopen lost the first checkpoint after its manifest rename"
  finally reopened.close
  expectManifest dir 1 1 0 1

private def checkCheckpointRetryWithFewerRuns (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    let _ ← db.write 4 (some 40)
    db.checkpoint
    let _ ← db.write 7 (some 70)
    db.checkpoint
    let _ ← db.write 4 (some 41)
    let _ ← db.write 7 none
  finally db.close
  let wal := dir / "WAL"
  let boundary := dir / "WAL.commit"
  let originalWal ← IO.FS.readBinFile wal
  let originalBoundary ← IO.FS.readBinFile boundary
  let manifest := dir / "MANIFEST"
  let stagedManifest := dir / "MANIFEST.next"
  let orphan := dir / "run-3-2.v3"
  let firstRun := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩]
  let secondRun := Compaction.encodeV3 [⟨7, 2, (0, 70)⟩]
  let suffixRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩, ⟨7, 4, (1, 0)⟩]
  let newRuns := [(dir / "run-3-0.v3", firstRun), (dir / "run-3-1.v3", secondRun), (orphan, suffixRun)]
  let alignedOpen := [wal.toString, dir.toString]
  -- All candidate run contents can be synced while the manifest still names
  -- generation 2. The wrapper completes the last file sync before returning an error.
  let (published, syncs) ← probeDisk bin dir (some orphan) (operation := "--checkpoint-once")
    (failureMode := .afterSync) (extraArgs := #["3"])
  let runSyncs := newRuns.map (fun (path, _) => path.toString)
  check (!published && syncs == alignedOpen ++ runSyncs ++ [s!"synced before error: {orphan}"])
    "checkpoint continued past a run sync that completed and reported failure"
  check (!(← stagedManifest.pathExists)) "run sync failure staged a manifest"
  let priorManifest := (Manifest.IntegrityCheckpoint.fromRuns ⟨2, 2, 0, 2⟩ [firstRun, secondRun]).encode
  check (decide ((← IO.FS.readBinFile manifest) = priorManifest ∧
    (← IO.FS.readBinFile wal) = originalWal ∧ (← IO.FS.readBinFile boundary) = originalBoundary))
    "run sync failure changed selected metadata or WAL bytes"
  for (path, bytes) in newRuns ++ [(dir / "run-2-0.v3", firstRun), (dir / "run-2-1.v3", secondRun)] do
    check (decide ((← IO.FS.readBinFile path) = bytes)) s!"unexpected checkpoint bytes in {path}"
  let recovered ← DiskTable.open dir
  try
    let some old ← recovered.acquireAt 2 | throw (IO.userError "run sync failure changed the selected floor")
    check ((← recovered.lookup old.handle 4) == some (some 40) &&
      (← recovered.lookup old.handle 7) == some (some 70)) "run sync failure changed the old snapshot"
    let latest ← recovered.acquire
    check (latest.sequence == 4 && (← recovered.lookup latest.handle 7) == some none)
      "reopen after the run sync failure lost the acknowledged WAL suffix"
  finally recovered.close
  let paths := newRuns.map Prod.fst ++ [dir, stagedManifest]
  for (target, cut) in paths.zipIdx do
    let skip := if target == dir then 1 else 0
    let (published, syncs) ← probeDisk bin dir (some target) (operation := "--checkpoint-once") (skipFailures := skip)
    let expected := alignedOpen ++ (paths.take (cut + 1)).map FilePath.toString
    check (!published && syncs == expected) s!"checkpoint did not stop at sync for {target}"
    expectManifest dir 2 2 0 2
  check (decide ((← IO.FS.readBinFile wal) = originalWal ∧ (← IO.FS.readBinFile boundary) = originalBoundary))
    "failed checkpoint changed the acknowledged WAL"
  check (← orphan.pathExists) "failed publication did not leave a third run in the orphan generation"
  let reopened ← DiskTable.open dir
  try
    let latest ← reopened.acquire
    check (latest.sequence == 4 && (← reopened.lookup latest.handle 4) == some (some 41))
      "old checkpoint did not replay its acknowledged suffix"
    check (← reopened.compact 0) "could not compact before reusing the orphan generation"
    reopened.checkpoint
    expectManifest dir 3 4 0 2
  finally reopened.close
  -- A stale file beyond the installed run count must not affect reopen.
  IO.FS.writeBinFile orphan ByteArray.empty
  let final ← DiskTable.open dir
  try
    let merged := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩, ⟨7, 2, (0, 70)⟩]
    let expectedManifest := (Manifest.IntegrityCheckpoint.fromRuns ⟨3, 4, 0, 2⟩ [merged, suffixRun]).encode
    check (decide ((← IO.FS.readBinFile manifest) = expectedManifest ∧
      (← IO.FS.readBinFile (dir / "run-3-0.v3")) = merged ∧
      (← IO.FS.readBinFile (dir / "run-3-1.v3")) = suffixRun))
      "retry did not select the exact shorter checkpoint"
    let some historical ← final.acquireAt 2 | throw (IO.userError "reopen lost the pre-compaction snapshot")
    check ((← final.lookup historical.handle 4) == some (some 40) &&
      (← final.lookup historical.handle 7) == some (some 70)) "retry changed historical values"
    let latest ← final.acquire
    check (latest.sequence == 4 && (← final.lookup latest.handle 4) == some (some 41) &&
      (← final.lookup latest.handle 7) == some none) "reopen with the shorter run set changed latest values"
    check ((← final.range latest.handle 0 8).map (List.map (·.key)) == some [4])
      "reopen with the shorter run set changed the latest range"
  finally final.close

private def checkObsoleteRunCollection (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let wal := dir / "WAL"
  let manifest := dir / "MANIFEST"
  let retired := dir / "run-1-0.v3"
  let selected := dir / "run-3-0.v3"
  let aliasPath := dir / "run-01-7.v3"
  let currentExtra := dir / "run-3-9.v3"
  let futureOrphan := dir / "run-4-0.v3"
  let linked := dir / "run-1-8.v3"
  let filler := ByteArray.mk #[17]
  let firstRun := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩, ⟨7, 2, (0, 70)⟩]
  let secondRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩]
  let thirdRun := Compaction.encodeV3 [⟨7, 4, (1, 0)⟩]
  let heldFiles := [(dir / "run-2-0.v3", firstRun), (dir / "run-2-1.v3", secondRun)]
  let expectFiles := fun (files : List (FilePath × ByteArray)) => do
    for (path, expected) in files do
      check (decide ((← IO.FS.readBinFile path) = expected)) s!"collection changed {path}"
    check ((← linked.symlinkMetadata).type == .symlink) "collection did not preserve the obsolete symlink"
  let expectReads := fun (db : DiskTable) (historical : DiskSnapshotPin) => do
    let rows := (← db.range historical.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check (historical.sequence == 2 && (← db.lookup historical.handle 7) == some (some 70) &&
      rows == some [(4, some 40), (7, some 70)]) "collection changed the retained snapshot"
    let latest ← db.acquire
    try
      let rows := (← db.range latest.handle 0 8).map (List.map fun row => (row.key, row.payload))
      check (latest.sequence == 5 && (← db.lookup latest.handle 7) == some none &&
        (← db.lookup latest.handle 6) == some (some 60) && rows == some [(4, some 41), (6, some 60)])
        "collection changed the current snapshot"
    finally db.release latest.handle
  let db ← DiskTable.open dir
  let protectedFiles ← try
    check ((← db.write 4 (some 40)) == 1) "unexpected first collection write sequence"
    check ((← db.write 7 (some 70)) == 2) "unexpected second collection write sequence"
    check (← db.advanceFloor 2) "could not set collection retention floor"
    db.checkpoint
    let historical ← db.acquire
    check ((← db.write 4 (some 41)) == 3) "unexpected collection overwrite sequence"
    db.checkpoint
    let previousManifest ← IO.FS.readBinFile manifest
    check ((← db.write 7 none) == 4) "unexpected collection tombstone sequence"
    db.checkpoint
    check ((← db.write 6 (some 60)) == 5) "unexpected collection WAL suffix"
    for path in [aliasPath, currentExtra, futureOrphan] do
      IO.FS.writeBinFile path filler
    let link ← IO.Process.output { cmd := "ln", args := #["-s", "--", selected.toString, linked.toString] }
    check (link.exitCode == 0) "could not create an obsolete run symlink"
    let history := WAL.encode [⟨1, 4, some 40⟩, ⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩,
      ⟨4, 7, none⟩, ⟨5, 6, some 60⟩]
    let header : Manifest.Checkpoint := ⟨3, 4, 2, 3⟩
    let checkpoint := Manifest.IntegrityCheckpoint.fromRuns header [firstRun, secondRun, thirdRun]
    let protectedFiles := [(manifest, checkpoint.encode), (wal, history),
      (dir / "WAL.commit", WAL.Boundary.encode history.size.toUInt64),
      (selected, firstRun), (dir / "run-3-1.v3", secondRun), (dir / "run-3-2.v3", thirdRun),
      (aliasPath, filler), (currentExtra, filler), (futureOrphan, filler)]
    check (← retired.pathExists) "fixture did not create an obsolete checkpoint run"
    expectFiles (protectedFiles ++ heldFiles)
    expectReads db historical
    -- Present the actual older, valid manifest without changing the ready writer.
    let savedManifest := dir / "MANIFEST.fixture-original"
    IO.FS.rename manifest savedManifest
    try
      IO.FS.writeBinFile manifest previousManifest
      let .error (.userError message) ← (db.collectObsoleteRuns [2]).toBaseIO
        | throw (IO.userError "collection accepted a different manifest generation")
      check (message == "checkpoint generation changed before run collection")
        "collection did not reject the generation mismatch"
      IO.FS.writeBinFile manifest (Manifest.encode header)
      rejects (db.collectObsoleteRuns [2]) "collection accepted a manifest without v2 run integrity"
      check (decide ((← IO.FS.readBinFile retired) = firstRun))
        "collection unlinked a run before rejecting the fixture manifest"
    finally IO.FS.rename savedManifest manifest
    let restored ← IO.Process.output { cmd := "sync", args := #["--", dir.toString] }
    check (restored.exitCode == 0) "could not settle the restored fixture manifest"
    db.collectObsoleteRuns [2]
    check (!(← retired.pathExists)) "collection did not unlink the obsolete run"
    expectFiles (protectedFiles ++ heldFiles)
    expectReads db historical
    pure protectedFiles
  finally db.close
  -- Fail the first collection barrier after open. The same handle retries the
  -- empty pass, so no reopen sync can hide a missing retry barrier.
  let expectedSyncs := [wal.toString, dir.toString, dir.toString, dir.toString]
  let (retried, syncs) ← probeDisk bin dir (some dir) (operation := "--collect-runs-and-retry")
    (skipFailures := 1) (failureMode := .beforeOnce)
  check (retried && syncs == expectedSyncs) "empty collection retry skipped its directory barrier"
  for (path, _) in heldFiles do
    check (!(← path.pathExists)) s!"collection retry kept the obsolete name {path}"
  expectFiles protectedFiles
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.acquireAt 1).isNone) "collection changed the recovered retention floor"
    let some historical ← reopened.acquireAt 2 | throw (IO.userError "collection lost the retained snapshot")
    expectReads reopened historical
  finally reopened.close

private def checkRecoveryAfterCheckpointAndWriteFailures (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected initial write sequence"
    check ((← db.write 7 (some 70)) == 2) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 2) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 3) "unexpected overwrite sequence"
    check ((← db.write 7 none) == 4) "unexpected tombstone sequence"
  finally db.close
  let wal := dir / "WAL"
  let marker := dir / "WAL.commit"
  let stagedManifest := dir / "MANIFEST.next"
  let stagedMarker := dir / "WAL.commit.next"
  let alignedOpen := [wal.toString, dir.toString]
  let runSyncs := [dir / "run-2-0.v3", dir / "run-2-1.v3", dir, stagedManifest]
  let (published, syncs) ← probeDisk bin dir (some stagedManifest) (operation := "--checkpoint-once")
  check (!published && syncs == alignedOpen ++ runSyncs.map FilePath.toString)
    "checkpoint fixture did not fail before the new manifest rename"
  expectManifest dir 1 2 2 1
  let events : List WAL.Write := [⟨1, 4, some 40⟩, ⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩, ⟨4, 7, none⟩]
  let acknowledged := WAL.encode events
  let boundary := WAL.Boundary.encode acknowledged.size.toUInt64
  let (written, syncs) ← probeDisk bin dir (some stagedMarker) (operation := "--write-once")
  check (!written && syncs == alignedOpen ++ [wal.toString, stagedMarker.toString])
    "write fixture did not fail before the new WAL marker rename"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged ++ WAL.encodeFrame ⟨5, 7, some 99⟩))
    "write fixture did not leave the complete unacknowledged append"
  check (decide ((← IO.FS.readBinFile marker) = boundary)) "failed write changed the selected WAL marker"
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [(dir / "WAL.next").toString, dir.toString])
    "reopen did not fail at the directory sync after repairing the WAL"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged)) "WAL repair rename did not trim the rejected append"
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == alignedOpen) "reopen retry did not sync the directory for the repaired WAL"
  let recovered ← DiskTable.open dir
  try
    expectManifest dir 1 2 2 1
    check ((← recovered.acquireAt 1).isNone) "reopen lost the checkpoint floor"
    let some historical ← recovered.acquireAt 2 | throw (IO.userError "reopen lost the checkpoint snapshot")
    check ((← recovered.lookup historical.handle 4) == some (some 40) &&
      (← recovered.lookup historical.handle 7) == some (some 70)) "reopen changed the checkpoint snapshot"
    let latest ← recovered.acquire
    check (latest.sequence == 4 && (← recovered.lookup latest.handle 4) == some (some 41) &&
      (← recovered.lookup latest.handle 7) == some none) "reopen changed the acknowledged WAL suffix"
    check ((← recovered.write 7 (some 71)) == 5) "reopen did not reuse the discarded write sequence"
  finally recovered.close
  let final ← DiskTable.open dir
  try
    let latest ← final.acquire
    check (latest.sequence == 5 && (← final.lookup latest.handle 7) == some (some 71))
      "another reopen lost the replacement for the discarded write"
  finally final.close

  -- The first directory sync belongs to open and the second protects the run
  -- entries. The third settles the replacement manifest before reporting error.
  let (published, syncs) ← probeDisk bin dir (some dir) (operation := "--checkpoint-once")
    (skipFailures := 2) (failureMode := .afterSync) (extraArgs := #["4"])
  check (!published && syncs == alignedOpen ++ runSyncs.map FilePath.toString ++
    [dir.toString, s!"synced before error: {dir}"])
    "checkpoint did not report failure after syncing the replacement manifest"
  let firstRun := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩, ⟨7, 2, (0, 70)⟩]
  let secondRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩, ⟨7, 5, (0, 71)⟩, ⟨7, 4, (1, 0)⟩]
  let expectFiles := fun (events : List WAL.Write) => do
    let walBytes := WAL.encode events
    check (decide ((← IO.FS.readBinFile wal) = walBytes ∧
      (← IO.FS.readBinFile marker) = WAL.Boundary.encode walBytes.size.toUInt64))
      "checkpoint recovery changed the selected WAL bytes"
    let expected := (Manifest.IntegrityCheckpoint.fromRuns ⟨2, 5, 4, 2⟩ [firstRun, secondRun]).encode
    check (decide ((← IO.FS.readBinFile (dir / "MANIFEST")) = expected))
      "checkpoint recovery changed the published manifest"
    for (path, bytes) in [(dir / "run-1-0.v3", firstRun),
        (dir / "run-2-0.v3", firstRun), (dir / "run-2-1.v3", secondRun)] do
      check (decide ((← IO.FS.readBinFile path) = bytes)) s!"unexpected checkpoint bytes in {path}"
  let throughCheckpoint := events ++ [⟨5, 7, some 71⟩]
  expectFiles throughCheckpoint
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.acquireAt 3).isNone) "reopen used the old manifest floor"
    let latest ← reopened.acquire
    check (latest.sequence == 5 && (← reopened.lookup latest.handle 7) == some (some 71))
      "reopen changed the published checkpoint snapshot"
    check ((← reopened.write 6 (some 60)) == 6) "write after checkpoint recovery used the wrong sequence"
  finally reopened.close
  let final ← DiskTable.open dir
  try
    expectFiles (throughCheckpoint ++ [⟨6, 6, some 60⟩])
    check ((← final.acquireAt 3).isNone) "later reopen lost the replacement floor"
    let some historical ← final.acquireAt 4 | throw (IO.userError "reopen lost the snapshot at the new floor")
    let historicalRows := (← final.range historical.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check ((← final.lookup historical.handle 7) == some none && historicalRows == some [(4, some 41)])
      "checkpoint replacement changed the historical tombstone or range"
    let latest ← final.acquire
    let latestRows := (← final.range latest.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check (latest.sequence == 6 && (← final.lookup latest.handle 6) == some (some 60) &&
      latestRows == some [(4, some 41), (6, some 60), (7, some 71)])
      "later reopen changed the acknowledged write or latest range"
  finally final.close

private def checkPublicationCuts : IO Unit := do
  let events : List WAL.Write := [⟨1, 7, some 60⟩]
  let complete := WAL.encode events
  let torn := complete ++ (WAL.encodeFrame ⟨2, 7, some 99⟩).extract 0 11
  let some replacement := WAL.repairPrefix torn
    | throw (IO.userError "expected a WAL repair at publication cuts")
  let initial := Publication.Image.settled (some torn)
  for cut in [:Publication.steps.length + 1] do
    let some image := initial.execute replacement (Publication.steps.take cut)
      | throw (IO.userError "publication plan failed in its model")
    let expected := if cut < 3 then [some torn]
      else if cut == 3 then [some complete, some torn] else [some complete]
    check (decide (image.crashImages = expected)) s!"unexpected directory outcome at publication cut {cut}"
    for candidate in image.crashImages do
      let some bytes := candidate | throw (IO.userError "crash lost the WAL name")
      let .ok decoded := WAL.decode bytes | throw (IO.userError "crash corrupted an acknowledged frame")
      check (decide (decoded = events)) s!"crash changed the WAL replay at cut {cut}"

def main (args : List String) : IO Unit := do
  match args with
  | ["--open-once", dir] => (← DiskTable.open ⟨dir⟩).close
  | ["--collect-runs-and-retry", path] =>
    let dir : FilePath := ⟨path⟩
    let db ← DiskTable.open dir
    try
      let latest ← db.acquire
      let .error (.userError message) ← (db.collectObsoleteRuns []).toBaseIO
        | throw (IO.userError "collection did not report its final sync error")
      check (message.startsWith "sync failed for " && message.endsWith s!"injected sync failure: {dir}\n")
        "collection did not preserve its sync error"
      for name in ["run-2-0.v3", "run-2-1.v3"] do
        check (!(← (dir / name).pathExists)) "collection sync did not follow the obsolete unlinks"
      check (latest.sequence == 5 && (← db.lookup latest.handle 6) == some (some 60))
        "collection sync error invalidated the active session"
      db.collectObsoleteRuns
    finally db.close
  | ["--write-once", dir] =>
    let db ← DiskTable.open ⟨dir⟩
    try
      let _ ← db.write 7 (some 99)
    finally db.close
  | ["--check-write-outcome", dir] =>
    let some target ← IO.getEnv "ALVOKI_CHECK_SYNC_FAIL"
      | throw (IO.userError "missing sync fault target")
    let db ← DiskTable.open ⟨dir⟩
    try
      let .error (.commitUnknown (.userError message)) ← (db.writeWithOutcome 7 (some 99)).toBaseIO
        | throw (IO.userError "sync error did not report an unknown commit outcome")
      check (message.startsWith "sync failed for " && message.endsWith s!"injected sync failure: {target}\n")
        "unknown commit outcome changed the sync error"
      expectRejectedWrite db "publication failed; reopen the database"
    finally db.close
  | "--checkpoint-once" :: dir :: floorArg =>
    let db ← DiskTable.open ⟨dir⟩
    try
      match floorArg with
      | [] => pure ()
      | [arg] =>
        let some floor := arg.toNat? | throw (IO.userError "invalid fixture floor")
        check (floor < UInt64.size && (← db.advanceFloor floor.toUInt64)) "could not set fixture floor"
      | _ => throw (IO.userError "unexpected checkpoint fixture arguments")
      db.checkpoint
    finally db.close
  | [] =>
    checkCodecs
    checkPublicationCuts
    IO.FS.withTempDir checkReopen
    IO.FS.withTempDir checkInterruptedPublication
    IO.FS.withTempDir checkMissingAndMalformedFiles
    IO.FS.withTempDir checkCoveredWalDuplicate
    IO.FS.withTempDir checkBoundedRecovery
    IO.FS.withTempDir checkDirectoryIdentity
    IO.FS.withTempDir checkDanglingFiles
    IO.FS.withTempDir checkSnapshotSessions
    IO.FS.withTempDir checkRetrySync
    IO.FS.withTempDir checkWritesAcrossReopens
    IO.FS.withTempDir checkGroupedSyncPartialEffects
    IO.FS.withTempDir checkCheckpointReadFailureBeforeWalRepair
    IO.FS.withTempDir checkFirstCheckpointCuts
    IO.FS.withTempDir checkCheckpointRetryWithFewerRuns
    IO.FS.withTempDir checkObsoleteRunCollection
    IO.FS.withTempDir checkRecoveryAfterCheckpointAndWriteFailures
    IO.println "Passed disk identity, WAL boundaries and ordinals, checkpoint cuts, and sync retry checks."
  | _ => throw (IO.userError "unexpected disk fixture arguments")
