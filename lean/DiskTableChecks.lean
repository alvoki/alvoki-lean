import DiskTable
import DiskPublicationModel

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

private def expectManifest (dir : FilePath) (generation watermark floor runCount : UInt64) :
    IO Unit := do
  let header ← IO.FS.readBinFile (dir / "MANIFEST")
  let .ok manifest := Manifest.decode header | throw (IO.userError "cannot decode installed manifest")
  check (decide (manifest = ⟨generation, watermark, floor, runCount⟩)) "unexpected manifest"

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
  let valid := Manifest.encode ⟨5, 3, 2, 4⟩
  for offset in [:valid.size] do
    check (failed (Manifest.decode (valid.set! offset (valid[offset]! ^^^ 1))))
      s!"manifest accepted corrupted byte {offset}"
  check (failed (Manifest.decode (Manifest.encode ⟨5, 3, 4, 1⟩)))
    "manifest accepted a floor above its watermark"

private def checkReopen (dir : FilePath) : IO Unit := do
  let maxKey := UInt64.ofNat (UInt64.size - 1)
  let db ← DiskTable.open dir
  rejects (DiskTable.open dir) "two handles opened one database for writes"
  check ((← db.write 4 (some 40)) == 1) "first write sequence"
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
  IO.FS.writeBinFile (dir / "MANIFEST") (Manifest.encode ⟨1, 0, 0, 1⟩)
  rejects (DiskTable.open dir) "open accepted a run newer than the checkpoint watermark"
  IO.FS.writeBinFile (dir / "MANIFEST") (Manifest.encode ⟨1, 1, 0, 1⟩)
  let wal := dir / "WAL"
  let frames ← IO.FS.readBinFile wal
  IO.FS.removeFile wal
  rejects (DiskTable.open dir) "open accepted a checkpoint without its WAL"
  IO.FS.writeBinFile wal frames
  let restored ← DiskTable.open dir
  let pin ← restored.acquire
  check ((← restored.lookup pin.handle 2) == some (some 20)) "failed opens kept the lock or changed the data"
  restored.close

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
  for name in ["MANIFEST", "WAL"] do
    let linked := dir / name
    let missing := dir / "missing"
    let result ← IO.Process.output {
      cmd := "ln", args := #["-s", "--", missing.toString, linked.toString] }
    check (result.exitCode == 0) "could not create dangling database file fixture"
    rejects (DiskTable.open dir) s!"open treated a dangling {name} as absent"
    let targetExists ← missing.pathExists
    check (!targetExists) s!"open created the target of a dangling {name}"
    IO.FS.removeFile linked

private def syncFixture : String := r#"#!/bin/sh
set -eu
for path do
  [ "$path" = -- ] && continue
  printf '%s\n' "$path" >> "$ALVOKI_CHECK_SYNC_LOG"
  if [ "$path" = "${ALVOKI_CHECK_SYNC_FAIL-}" ]; then
    seen=$(grep -Fxc -- "$path" "$ALVOKI_CHECK_SYNC_LOG")
    if [ "$seen" -gt "${ALVOKI_CHECK_SYNC_SKIP-0}" ]; then exit 1; fi
  fi
  command -p sync -- "$path"
done
"#

private def probeDisk (bin dir : FilePath) (failAt : Option FilePath) (operation := "--open-once")
    (skipFailures : Nat := 0) : IO (Bool × List String) := do
  let log := bin / "sync.log"
  IO.FS.writeFile log ""
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let executable ← IO.appPath
  let result ← IO.Process.output {
    cmd := executable.toString
    args := #[operation, dir.toString]
    env := #[("PATH", some (bin.toString ++ ":" ++ path)),
      ("ALVOKI_CHECK_SYNC_LOG", some log.toString),
      ("ALVOKI_CHECK_SYNC_FAIL", failAt.map FilePath.toString),
      ("ALVOKI_CHECK_SYNC_SKIP", some (toString skipFailures))] }
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
  let paths := [dir / "run-3-0.v3", dir / "run-3-1.v3", dir / "run-3-2.v3", dir, dir / "MANIFEST.next"]
  for (target, cut) in paths.zipIdx do
    let skip := if target == dir then 1 else 0
    let (published, syncs) ← probeDisk bin dir (some target) (operation := "--checkpoint-once") (skipFailures := skip)
    let expected := [wal.toString, dir.toString] ++ (paths.take (cut + 1)).map FilePath.toString
    check (!published && syncs == expected) s!"checkpoint did not stop at sync for {target}"
    expectManifest dir 2 2 0 2
  check (decide ((← IO.FS.readBinFile wal) = originalWal ∧ (← IO.FS.readBinFile boundary) = originalBoundary))
    "failed checkpoint changed the acknowledged WAL"
  let orphan := dir / "run-3-2.v3"
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
    let some historical ← final.acquireAt 2 | throw (IO.userError "reopen lost the pre-compaction snapshot")
    check ((← final.lookup historical.handle 4) == some (some 40) &&
      (← final.lookup historical.handle 7) == some (some 70)) "retry changed historical values"
    let latest ← final.acquire
    check (latest.sequence == 4 && (← final.lookup latest.handle 4) == some (some 41) &&
      (← final.lookup latest.handle 7) == some none) "reopen with the shorter run set changed latest values"
    check ((← final.range latest.handle 0 8).map (List.map (·.key)) == some [4])
      "reopen with the shorter run set changed the latest range"
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
  | ["--write-once", dir] =>
    let db ← DiskTable.open ⟨dir⟩
    try
      let _ ← db.write 7 (some 99)
    finally db.close
  | ["--checkpoint-once", dir] =>
    let db ← DiskTable.open ⟨dir⟩
    try db.checkpoint finally db.close
  | [] =>
    checkCodecs
    checkPublicationCuts
    IO.FS.withTempDir checkReopen
    IO.FS.withTempDir checkInterruptedPublication
    IO.FS.withTempDir checkMissingAndMalformedFiles
    IO.FS.withTempDir checkBoundedRecovery
    IO.FS.withTempDir checkDirectoryIdentity
    IO.FS.withTempDir checkDanglingFiles
    IO.FS.withTempDir checkRetrySync
    IO.FS.withTempDir checkFirstCheckpointCuts
    IO.FS.withTempDir checkCheckpointRetryWithFewerRuns
    IO.println "Passed disk identity, WAL boundaries, checkpoint cuts, and sync retry checks."
  | _ => throw (IO.userError "unexpected disk fixture arguments")
