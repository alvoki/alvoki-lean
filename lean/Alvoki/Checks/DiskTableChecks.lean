import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.StagingFile
import Alvoki.Storage.Disk.WalSegmentReadIO
import Alvoki.Storage.Disk.WalSegmentRepair
import Alvoki.Storage.Disk.WalSegmentRepairIO
import Alvoki.Storage.Disk.WalSegmentRepairOpen
import Alvoki.Storage.Disk.WalSegmentRotationIO
import Alvoki.Storage.Disk.LegacyManifest
import Alvoki.Storage.Publication.DiskPublicationModel

open System Alvoki Alvoki.Storage

private def firstWalSegment := "WAL-segment-0"

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

private def expectSnapshot (db : DiskTable) (sequence : UInt64)
    (expected : List (UInt64 × Option UInt64)) : IO Unit := do
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

/-- Use a v2 checkpoint published by the current adapter to exercise the
segmented reopen worker with real files and the same exclusive lock. -/
private def checkSegmentedCheckpointOpen (root : FilePath) : IO Unit := do
  let db ← DiskTable.open root
  try
    let _ ← db.write 7 (some 70)
    let _ ← db.write 8 (some 80)
    db.checkpoint
  finally db.close
  let dir ← DiskDirectory.open root
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  check (← lock.tryLock) "could not lock segmented checkpoint fixture"
  try
    let sealed := dir.file (.walSegment 0)
    let covered ← IO.FS.readBinFile sealed
    let keeper := dir.file (.walSegment 2)
    let newer := dir.file (.walSegment 4)
    let committed := WAL.encodeFrame ⟨3, 7, some 71⟩
    let extra := WAL.encodeFrame ⟨4, 8, none⟩
    let marker := WAL.Boundary.encode (3 * WAL.frameSize).toUInt64
    IO.FS.writeBinFile keeper (committed ++ extra)
    IO.FS.writeBinFile newer (ByteArray.mk #[0xff])
    IO.FS.writeBinFile (dir.file .walBoundary) marker
    let touched ← IO.mkRef false
    let readOptional := fun path => readOptionalDatabaseFile path.symlinkMetadata.toBaseIO
      (fun _ => IO.FS.readBinFile path) (fun _ => IO.userError "expected a regular fixture file") throw
    let sync := fun paths => do
      touched.set true
      let result ← IO.Process.output {cmd := "sync", args := #["--"] ++ paths.map FilePath.toString}
      check (result.exitCode == 0) "could not sync segmented checkpoint fixture"
    let openMarked := WalSegmentRepair.reopenMarkedWith dir readOptional FilePath.readDir
      (fun path => path.symlinkMetadata.toBaseIO)
      (fun path => do
        check (path != sealed && path != newer) "segmented reopen read an unselected WAL payload"
        IO.FS.readBinFile path)
      (fun path => do touched.set true; (IO.FS.removeFile path).toBaseIO)
      (fun path bytes => do touched.set true; writeFreshStagedFile path bytes) sync
      (fun source target => do touched.set true; IO.FS.rename source target)
    let runFile := dir.file (.run 1 0)
    let runBytes ← IO.FS.readBinFile runFile
    IO.FS.writeBinFile runFile (runBytes.set! 0 (runBytes[0]! ^^^ 1))
    let .error (.userError cause) ← openMarked.toBaseIO
      | throw (IO.userError "segmented open did not reject the wrong checkpoint bytes")
    check (cause == checkpointIntegrityMismatch) "segmented open skipped v2 checkpoint integrity"
    check (!(← touched.get) && (← newer.pathExists))
      "segmented open performed repair effects before checkpoint validation"
    IO.FS.writeBinFile runFile runBytes
    IO.FS.writeBinFile keeper (committed.set! 0 (committed[0]! ^^^ 1) ++ extra)
    rejects openMarked "segmented open accepted the wrong selected WAL bytes"
    check (!(← touched.get) && (← newer.pathExists))
      "segmented open performed repair effects before replay validation"
    IO.FS.writeBinFile keeper (committed ++ extra)
    sync #[runFile, sealed, keeper, newer, dir.file .walBoundary, dir.path]
    let first ← openMarked
    let again ← openMarked
    for opened in [first, again] do
      check (opened.generation == 1 && opened.keeper == 2 && opened.table.committed == 3 &&
        opened.walBytes == (3 * WAL.frameSize).toUInt64) "segmented reopen returned the wrong installation"
      let some (pin, table) := opened.table.acquireAt 3
        | throw (IO.userError "segmented reopen could not acquire its committed snapshot")
      check (table.lookup pin.handle 7 == some (some 71) && table.lookup pin.handle 8 == some (some 80))
        "segmented reopen failed to replay exactly to the marker"
    check (decide ((← IO.FS.readBinFile sealed) = covered) &&
      decide ((← IO.FS.readBinFile keeper) = committed) && !(← newer.pathExists) &&
      !(← (dir.file .stagedWal).pathExists) &&
      decide ((← IO.FS.readBinFile (dir.file .walBoundary)) = marker))
      "segmented reopen settled the wrong WAL files"
  finally lock.unlock

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
  let wal := dir / firstWalSegment
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
  let wal := dir / firstWalSegment
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
  let wal := dir / firstWalSegment
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
  let wal := dir / firstWalSegment
  let marker := dir / "WAL.commit"
  let event : WAL.Write := ⟨1, 3, some 81⟩
  let durable := WAL.encodeFrame event
  let db ← DiskTable.open dir
  try
    check ((← db.write event.key event.value) == event.sequence) "incorrect initial WAL sequence"
  finally db.close
  let committed ← IO.FS.readBinFile marker
  let .ok count := WAL.Boundary.decode committed | throw (IO.userError "invalid published boundary")
  check (count == WAL.frameSize.toUInt64)
    "write did not publish the expected boundary"
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
        check ((← IO.FS.readBinFile (first / "db" / firstWalSegment)).size == WAL.frameSize)
          "relative open lost its WAL after changing the working directory"
        expectManifest (first / "db") 1 1 0 1
        check ((← IO.FS.readBinFile (second / "db" / firstWalSegment)).isEmpty)
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

private def makeFixtureLink (target name : FilePath) (symbolic : Bool) : IO Unit := do
  let flags := if symbolic then #["-s"] else #[]
  let result ← IO.Process.output {cmd := "ln", args := flags ++ #["--", target.toString, name.toString]}
  check (result.exitCode == 0) s!"could not create fixture link at {name}"

private def checkDanglingFiles (dir : FilePath) : IO Unit := do
  for name in ["MANIFEST", "WAL.commit", "WAL", firstWalSegment] do
    let linked := dir / name
    let missing := dir / "missing"
    makeFixtureLink missing linked true
    rejects (DiskTable.open dir) s!"open treated a dangling {name} as absent"
    let targetExists ← missing.pathExists
    check (!targetExists) s!"open created the target of a dangling {name}"
    IO.FS.removeFile linked

private def checkLockBindingGuards (root : FilePath) : IO Unit := do
  let dir := (← DiskDirectory.open root).path
  let lock := dir / "LOCK"
  let target := dir / "lock-target"
  let sentinel := ByteArray.mk #[4, 8, 15, 16, 23, 42]
  IO.FS.writeBinFile target sentinel
  let expectRefusal := do
    let .error (.userError cause) ← (DiskTable.open dir).toBaseIO
      | throw (IO.userError "open accepted an aliased or nonregular LOCK")
    check (cause == s!"expected a regular database file with one link: '{lock}'")
      "open did not report the LOCK binding guard"
    let names := (← dir.readDir).toList.map (·.fileName)
    check (names.length == 2 && names.contains "LOCK" && names.contains "lock-target" &&
      (← IO.FS.readBinFile target) == sentinel) "LOCK rejection changed its target or started bootstrap"
  for symbolic in [true, false] do
    makeFixtureLink target lock symbolic
    expectRefusal
    IO.FS.removeFile lock
  IO.FS.createDir lock
  expectRefusal

private def checkStaleWalStaging (dir : FilePath) : IO Unit := do
  let dir := (← DiskDirectory.open dir).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 7 (some 70)) == 1) "unexpected initial staging fixture sequence"
  finally db.close
  let wal := dir / firstWalSegment
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.next"
  let other := dir / "unrelated-file"
  let selected ← IO.FS.readBinFile wal
  let boundary ← IO.FS.readBinFile marker
  let torn := selected ++ (WAL.encodeFrame ⟨2, 7, some 99⟩).extract 0 11
  let unrelated := ByteArray.mk (Array.replicate 100 120)
  IO.FS.writeBinFile wal torn
  IO.FS.writeBinFile other unrelated
  makeFixtureLink other staged true
  let .error (.userError cause) ← (DiskTable.open dir).toBaseIO
    | throw (IO.userError "recovery accepted a symlink at the WAL staging path")
  check (cause == s!"expected a regular database staging file: '{staged}'")
    "recovery reported the wrong staging error"
  check (decide ((← IO.FS.readBinFile wal) = torn ∧ (← IO.FS.readBinFile marker) = boundary ∧
    (← IO.FS.readBinFile other) = unrelated)) "staging symlink refusal changed selected files or its target"
  IO.FS.removeFile staged

  -- A stale regular link may share an inode. Detach the inactive name before writing.
  makeFixtureLink other staged false
  let reopened ← DiskTable.open dir
  try
    let pin ← reopened.acquire
    check (pin.sequence == 1 && (← reopened.lookup pin.handle 7) == some (some 70))
      "staging retry returned a different committed table"
    check (decide ((← IO.FS.readBinFile wal) = selected ∧ (← IO.FS.readBinFile marker) = boundary ∧
      (← IO.FS.readBinFile other) = unrelated) && !(← staged.pathExists))
      "staging retry reused the stale inode or changed selected files"
  finally reopened.close

private def checkActiveWalGuard (root : FilePath) : IO Unit := do
  let dir := (← DiskDirectory.open root).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected active guard fixture sequence"
    db.rotateWal
    let sealed := dir / firstWalSegment
    let active := dir / "WAL-segment-1"
    let marker := dir / "WAL.commit"
    let boundary := WAL.Boundary.encode WAL.frameSize.toUInt64
    let committed := WAL.encodeFrame ⟨1, 4, some 40⟩
    let expectNoEffects := do
      check ((← IO.FS.readBinFile sealed) == committed && (← IO.FS.readBinFile marker) == boundary &&
        !(← (dir / "WAL.commit.next").pathExists)) "rejected append changed publication files"
    -- Exercise each active-path guard under the fixture's own held lock.
    let stray := ByteArray.mk #[42]
    IO.FS.writeBinFile active stray
    let .error (.rejected (.userError cause)) ← (db.writeWithOutcome 7 (some 70)).toBaseIO
      | throw (IO.userError "append did not reject an inconsistent active segment length")
    check (cause == s!"active WAL segment size disagrees with its durable marker: '{active}'" &&
      (← IO.FS.readBinFile active) == stray) "length guard changed the active file"
    expectNoEffects
    IO.FS.removeFile active
    let .error (.rejected (.noFileOrDirectory _ 2 _)) ← (db.writeWithOutcome 7 (some 70)).toBaseIO
      | throw (IO.userError "missing active file did not preserve Linux ENOENT")
    check (!(← active.pathExists)) "append recreated the missing active segment"
    expectNoEffects
    let target := dir / "active-target"
    IO.FS.writeBinFile target ByteArray.empty
    makeFixtureLink target active false
    let .error (.rejected (.userError cause)) ← (db.writeWithOutcome 7 (some 70)).toBaseIO
      | throw (IO.userError "append did not reject a hardlinked active segment")
    check (cause == s!"expected a regular database file with one link: '{active}'" &&
      (← IO.FS.readBinFile target).isEmpty) "active alias guard wrote to its target"
    expectNoEffects
    IO.FS.removeFile active
    IO.FS.writeBinFile active ByteArray.empty
    let .ok sequence ← (db.writeWithOutcome 7 (some 70)).toBaseIO
      | throw (IO.userError "active segment rejection invalidated the ready session")
    check (sequence == 2 && (← IO.FS.readBinFile active) == WAL.encodeFrame ⟨2, 7, some 70⟩ &&
      (← IO.FS.readBinFile marker) == WAL.Boundary.encode (2 * WAL.frameSize).toUInt64)
      "append resumed at the wrong ordinal or in the wrong segment"
  finally db.close

private def checkCheckpointRunAliases (root : FilePath) : IO Unit := do
  let dir := (← DiskDirectory.open root).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected checkpoint alias fixture sequence"
    db.checkpoint
    check ((← db.write 7 (some 70)) == 2) "unexpected checkpoint alias fixture suffix"
  finally db.close
  let installed := dir / "run-1-0.v3"
  let orphan := dir / "run-2-1.v3"
  let paths := [dir / "MANIFEST", installed, dir / firstWalSegment, dir / "WAL.commit"]
  let original ← paths.mapM IO.FS.readBinFile
  for symbolic in [true, false] do
    let db ← DiskTable.open dir
    try
      makeFixtureLink installed orphan symbolic
      let .error (.userError cause) ← db.checkpoint.toBaseIO
        | throw (IO.userError "checkpoint accepted an aliased future run target")
      check (cause == s!"expected a regular database file with one link: '{orphan}'")
        "checkpoint did not report the orphan run guard"
      expectRejectedWrite db "publication failed; reopen the database"
    finally db.close
    check (decide ((← paths.mapM IO.FS.readBinFile) = original))
      "checkpoint alias failure changed selected files"
    IO.FS.removeFile orphan
  let recovered ← DiskTable.open dir
  try
    let pin ← recovered.acquire
    check (pin.sequence == 2 && (← recovered.lookup pin.handle 4) == some (some 40) &&
      (← recovered.lookup pin.handle 7) == some (some 70))
      "checkpoint alias failure changed the recovered table"
    recovered.checkpoint
    expectManifest dir 2 2 0 2
  finally recovered.close

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

private def syncFixtureSource : String :=
  include_str ".." / ".." / ".." / "scripts" / "disk-sync-fixture.c"

private initialize syncFixtureLibrary : IO.Ref (Option FilePath) ← IO.mkRef none

private def withSyncFixture (action : IO Unit) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let source := dir / "disk-sync-fixture.c"
    let library := dir / "disk-sync-fixture.so"
    IO.FS.writeFile source syncFixtureSource
    let result ← IO.Process.output {
      cmd := "cc"
      args := #["-Wall", "-Wextra", "-Werror", "-shared", "-fPIC", source.toString,
        "-o", library.toString, "-ldl"] }
    check (result.exitCode == 0) s!"could not compile sync fault fixture: {result.stderr}"
    syncFixtureLibrary.set (some library)
    try action finally syncFixtureLibrary.set none

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
  let some library ← syncFixtureLibrary.get
    | throw (IO.userError "missing compiled sync fault fixture")
  let executable ← IO.appPath
  let mode := match failureMode with
    | .beforeSync => "before"
    | .beforeOnce => "before-once"
    | .afterSync => "after"
    | .secondOnly => "second-only"
  let result ← IO.Process.output {
    cmd := executable.toString
    args := #[operation, dir.toString] ++ extraArgs
    env := #[("LD_PRELOAD", some library.toString),
      ("ALVOKI_CHECK_SYNC_LOG", some log.toString),
      ("ALVOKI_CHECK_SYNC_FAIL", failAt.map FilePath.toString),
      ("ALVOKI_CHECK_SYNC_SKIP", some (toString skipFailures)),
      ("ALVOKI_CHECK_SYNC_FAIL_MODE", some mode)] }
  let paths := (← IO.FS.readFile log).splitOn "\n" |>.filter (!·.isEmpty)
  return (result.exitCode == 0, paths)

private def syncFixtureBin (root : FilePath) : IO FilePath := do
  let bin := root / "bin"
  IO.FS.createDir bin
  return bin

private def walReplacementSyncs (dir : FilePath) : List String :=
  [dir.toString, dir.toString, (dir / "WAL.next").toString, dir.toString]

private def alignedWalSyncs (dir active : FilePath) : List String :=
  [dir.toString, active.toString]

private def checkMarkerlessRefusal (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let wal := dir / firstWalSegment
  let manifest := dir / "MANIFEST"
  let marker := dir / "WAL.commit"
  let checkRefusal := do
    match ← (DiskTable.open dir).toBaseIO with
    | .error (.userError message) =>
      check (message == WAL.Boundary.missingOpenMarker) "unexpected markerless open error"
    | .error error => throw error
    | .ok db =>
      db.close
      throw (IO.userError "open accepted installed data without a WAL marker")
    let (opened, syncs) ← probeDisk bin dir none
    check (!opened && syncs.isEmpty) "markerless refusal reached durability operations"
    for name in ["WAL.next", "WAL.commit.next", "WAL.commit", "MANIFEST.next"] do
      check (!(← (dir / name).pathExists)) s!"markerless refusal created {name}"
  let nonempty := WAL.encodeFrame ⟨1, 7, some 60⟩ ++ (WAL.encodeFrame ⟨2, 7, none⟩).extract 0 9
  IO.FS.writeBinFile wal nonempty
  checkRefusal
  check (decide ((← IO.FS.readBinFile wal) = nonempty) && !(← manifest.pathExists))
    "markerless refusal changed an unmarked WAL or created a manifest"

  IO.FS.removeFile wal
  let db ← DiskTable.open dir
  try db.checkpoint finally db.close
  expectManifest dir 1 0 0 0
  let checkpoint ← IO.FS.readBinFile manifest
  IO.FS.removeFile marker
  checkRefusal
  check (← (IO.FS.readBinFile wal).map ByteArray.isEmpty) "markerless refusal changed the empty WAL"
  IO.FS.removeFile wal
  checkRefusal
  check (!(← wal.pathExists) && decide ((← IO.FS.readBinFile manifest) = checkpoint))
    "markerless refusal created an absent WAL or changed the installed checkpoint"

/-- Use the future rotation path dispatcher only in a locked scratch
directory. Each injected error retains the effects of completed calls. -/
private def checkWalSegmentRotation (root : FilePath) : IO Unit := do
  let withLocked := fun path (action : DiskDirectory → IO Unit) => do
    IO.FS.createDir path
    let dir ← DiskDirectory.open path
    let lock ← IO.FS.Handle.mk (dir.file .lock) .append
    check (← lock.tryLock) "could not lock rotation fixture"
    try action dir finally lock.unlock
  let readOptional : FilePath → IO (Option ByteArray) := fun path =>
    readOptionalDatabaseFile path.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile path)
      (fun _ => IO.userError s!"expected a regular WAL segment: '{path}'") throw
  let syncPath := fun (path : FilePath) => do
    let result ← IO.Process.output {cmd := "sync", args := #["--", path.toString]}
    check (result.exitCode == 0) s!"rotation fixture sync failed: {result.stderr}"
  let creation : List WalSegmentRotation.Step := [.createEmpty, .syncFile, .syncDirectory]
  for (step, index) in creation.zipIdx do
    for afterEffect in [false, true] do
      withLocked (root / s!"rotation-{index}-{afterEffect}") fun dir => do
        let previous := dir.file (.walSegment 0)
        let successor := dir.file (.walSegment 1)
        let previousBytes := WAL.encodeFrame ⟨1, 7, some 60⟩
        IO.FS.writeBinFile previous previousBytes
        let seen ← IO.mkRef ([] : List WalSegmentRotation.Step)
        let attempt := fun (failure : Option (WalSegmentRotation.Step × Bool)) => do
          let report := fun operation (effect : IO Unit) => do
            seen.modify (· ++ [operation])
            if failure = some (operation, false) then throw (IO.userError "rotation failed before effect")
            effect
            if failure = some (operation, true) then throw (IO.userError "rotation failed after effect")
          WalSegmentRotation.runAt dir 1 (fun path => do
              check (path == successor) "rotation looked up the wrong successor path"
              readOptional path)
            (fun path => do
              check (path == successor) "rotation created the wrong successor path"
              report .createEmpty (WalSegmentRotation.createEmptyExclusive path))
            (fun path => do
              check (path == successor || path == dir.path) "rotation synced a path outside its plan"
              report (if path == successor then .syncFile else .syncDirectory) (syncPath path))
        rejects (attempt (some (step, afterEffect))) "rotation ignored its injected error"
        check (decide ((← seen.get) = creation.take (index + 1))) "rotation ran beyond its reported cut"
        let present := index > 0 || afterEffect
        check ((← successor.pathExists) == present) "rotation failure exposed the wrong successor binding"
        seen.set []
        attempt none
        let expected := if present then [.syncFile, .syncDirectory] else creation
        check (decide ((← seen.get) = expected)) "rotation retry skipped its file or directory sync"
        check (← (IO.FS.readBinFile successor).map ByteArray.isEmpty) "rotation successor was not empty"
        check (decide ((← IO.FS.readBinFile previous) = previousBytes)) "rotation changed the previous WAL segment"
  withLocked (root / "rotation-existing") fun dir => do
    let successor := dir.file (.walSegment 1)
    let bytes := WAL.encodeFrame ⟨2, 7, some 61⟩
    IO.FS.writeBinFile successor bytes
    rejects (WalSegmentRotation.createEmptyExclusive successor) "exclusive creation overwrote an existing successor"
    let touched ← IO.mkRef false
    let unexpected := fun (_ : FilePath) => touched.set true
    rejects (WalSegmentRotation.runAt dir 1 readOptional unexpected unexpected) "rotation accepted a nonempty successor"
    check (!(← touched.get) && decide ((← IO.FS.readBinFile successor) = bytes)) "rotation changed a nonempty successor"
    IO.FS.removeFile successor
    let target := dir.path / "empty-target"
    IO.FS.writeBinFile target ByteArray.empty
    let linked ← IO.Process.output {cmd := "ln", args := #["-s", "--", target.toString, successor.toString]}
    check (linked.exitCode == 0) "could not create rotation symlink fixture"
    rejects (WalSegmentRotation.runAt dir 1 readOptional unexpected unexpected) "rotation followed a successor symlink"
    check (!(← touched.get)) "rotation attempted durability operations on a successor symlink"

private def checkWalSegmentReads (root : FilePath) : IO Unit := do
  let dir ← DiskDirectory.open root
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  check (← lock.tryLock) "could not lock segment read fixture"
  try
    let history : List WAL.Write := (List.range 12).map fun index =>
      ⟨(index + 1).toUInt64, index.toUInt64, some (index + 1).toUInt64⟩
    let active := WAL.encode (history.drop 10) ++ ByteArray.mk #[4, 5, 6]
    let middle := WAL.encode ((history.drop 2).take 8)
    IO.FS.writeBinFile (dir.file (.walSegment 10)) active
    IO.FS.writeBinFile (dir.file (.walSegment 2)) middle
    IO.FS.writeBinFile (dir.file (.walSegment 0)) (WAL.encode (history.take 2))
    IO.FS.writeBinFile (dir.path / "WAL-segment-2.tmp") ByteArray.empty
    let makeLink := fun (name : FilePath) => do
      let target := (dir.file (.walSegment 2)).toString
      let created ← IO.Process.output {cmd := "ln", args := #["-s", "--", target, name.toString]}
      check (created.exitCode == 0) "could not create segment read symlink fixture"
    makeLink (dir.path / "WAL-segment-02")
    let expected := (2, [2, 10], [middle, active])
    check (decide ((← readWalSegments dir 2) = expected)) "native segment read returned the wrong payload vector"

    let calls ← IO.mkRef ([] : List (String × FilePath))
    let record := fun kind path => calls.modify (· ++ [(kind, path)])
    let read : IO (Nat × List Nat × List ByteArray) := readWalSegmentsWith dir 2
      (fun path => do
        record "list" path
        path.readDir)
      (fun path => do
        record "lstat" path
        path.symlinkMetadata.toBaseIO)
      (fun path => do
        record "read" path
        IO.FS.readBinFile path)
    check (decide ((← read) = expected)) "observed segment read returned the wrong payload vector"
    let log ← calls.get
    let checked := (log.drop 1).take 3
    let expectedStats := [0, 2, 10].map fun first => ("lstat", dir.file (.walSegment first))
    check (log.head? == some ("list", dir.path) && checked.length == 3 && expectedStats.all checked.contains)
      "segment inventory probed an unexpected name or path"
    check (log.drop 4 == [("read", dir.file (.walSegment 2)), ("read", dir.file (.walSegment 10))])
      "segment payload reads did not follow all lookups in planned order"

    let unexpected := dir.file (.walSegment 9)
    let rejectKind := do
      calls.set []
      rejects read "segment inventory accepted a canonical nonregular name"
      check (!(← calls.get).any (fun (kind, _) => kind == "read"))
        "segment inventory read payloads before finishing metadata checks"
    makeLink unexpected
    rejectKind
    IO.FS.removeFile unexpected
    IO.FS.createDir unexpected
    rejectKind
  finally lock.unlock

private inductive WalRepairFixtureCall where
  | prepare
  | remove (path : FilePath)
  | write (path : FilePath)
  | sync (paths : Array FilePath)
  | rename (source target : FilePath)
  deriving BEq

/-- Inspect process-visible effects of each reported callback cut, then
rebuild the plan from the same marker and the remaining canonical files. -/
private def checkWalSegmentRepair (root : FilePath) : IO Unit := do
  let history : List WAL.Write := (List.range 7).map fun n =>
    ⟨(n + 1).toUInt64, n.toUInt64, some (n + 10).toUInt64⟩
  let frame := fun n => WAL.encode ((history.drop n).take 1)
  let keptBytes := WAL.encode (history.take 2)
  let keeperBytes := frame 2 ++ frame 3
  let replacement := frame 2
  let newer := [(4, frame 4), (5, frame 5), (6, frame 6 ++ ByteArray.mk #[1, 2, 3])]
  let markerBytes := WAL.Boundary.encode (3 * WAL.frameSize).toUInt64
  let syncPaths := fun (paths : Array FilePath) => do
    let result ← IO.Process.output {cmd := "sync", args := #["--"] ++ paths.map FilePath.toString}
    check (result.exitCode == 0) s!"WAL repair fixture sync failed: {result.stderr}"
  let schedule := fun (dir : DiskDirectory) =>
    let staged := dir.file .stagedWal
    [WalRepairFixtureCall.prepare, .sync #[dir.path]] ++
      newer.map (fun file => .remove (dir.file (.walSegment file.1))) ++
      [.sync #[dir.path], .write staged, .sync #[staged], .rename staged (dir.file (.walSegment 2)), .sync #[dir.path]]
  let base ← DiskDirectory.open root
  for cut in [1:(schedule base).length] do
    for afterEffect in [false, true] do
      let path := root / s!"repair-{cut}-{afterEffect}"
      IO.FS.createDir path
      let dir ← DiskDirectory.open path
      let lock ← IO.FS.Handle.mk (dir.file .lock) .append
      check (← lock.tryLock) "could not lock WAL repair fixture"
      try
        let kept := dir.file (.walSegment 0)
        let keeper := dir.file (.walSegment 2)
        let staged := dir.file .stagedWal
        let marker := dir.file .walBoundary
        IO.FS.writeBinFile kept keptBytes
        IO.FS.writeBinFile keeper keeperBytes
        IO.FS.writeBinFile marker markerBytes
        for (first, bytes) in newer do
          IO.FS.writeBinFile (dir.file (.walSegment first)) bytes
        syncPaths #[kept, keeper, marker]

        let seen ← IO.mkRef ([] : List WalRepairFixtureCall)
        let record := fun (operation : WalRepairFixtureCall) => do
          let calls ← seen.get
          seen.set (calls ++ [operation])
          pure calls.length
        let prepare : IO WalSegmentRepair.Plan := do
          let _ ← record .prepare
          let .ok length := WAL.Boundary.decode (← IO.FS.readBinFile marker)
            | throw (IO.userError "WAL repair fixture lost the marker")
          let through := length.toNat / WAL.frameSize
          let observed ← readWalSegmentsThrough dir 0 length
          check (checkWalSegmentSpans through observed.files) "WAL repair observed invalid selected spans"
          let [(0, priorBytes), (2, active)] := observed.files
            | throw (IO.userError "WAL repair selected the wrong files")
          let retained := (priorBytes ++ active).extract 0 length.toNat
          check (decide (retained = keptBytes ++ replacement)) "WAL repair read the wrong retained history"
          let existing ← newer.filterM fun file => (dir.file (.walSegment file.1)).pathExists
          check (observed.newer == existing.map Prod.fst) "WAL repair omitted surviving discardable files"
          pure ⟨through, 2, observed.newer, active⟩
        let injected := s!"injected WAL repair failure at callback {cut} after effect {afterEffect}"
        let attempt := fun (plan : IO WalSegmentRepair.Plan) (fail : Bool) => do
          let report : {α : Type} → WalRepairFixtureCall → IO α → IO α → IO α := fun operation effect failure => do
            let index ← record operation
            if fail && index == cut && !afterEffect then failure
            else
              let value ← effect
              if fail && index == cut && afterEffect then failure else pure value
          let run := fun operation (effect : IO Unit) => report operation effect (throw (IO.userError injected))
          WalSegmentRepair.runAt dir plan
            (fun file => report (.remove file) (IO.FS.removeFile file).toBaseIO (pure (.error (IO.userError injected))))
            (fun file bytes => run (.write file) do
              check (decide (bytes = replacement)) "WAL repair staged the wrong prefix"
              writeFreshStagedFile file bytes)
            (fun paths => run (.sync paths) (syncPaths paths))
            (fun source target => run (.rename source target) (IO.FS.rename source target))

        if cut == 1 && !afterEffect then
          rejects (attempt (pure ⟨3, 2, [2], keeperBytes⟩) false) "WAL repair accepted an invalid prune plan"
          check ((← seen.get).isEmpty) "invalid WAL repair preparation reached effect callbacks"
        match ← (attempt prepare true).toBaseIO with
        | .ok _ => throw (IO.userError "WAL repair ignored the injected callback error")
        | .error (.userError message) => check (message == injected) message
        | .error error => throw error
        let expected := schedule dir
        check ((← seen.get) == expected.take (cut + 1)) "WAL repair did not stop at its reported cut"
        let completed := expected.take (if afterEffect then cut + 1 else cut)
        let renamed := completed.contains (.rename staged keeper)
        let assertLayout := fun (calls : List WalRepairFixtureCall) (replaced : Bool) => do
          check (decide ((← IO.FS.readBinFile kept) = keptBytes)) "WAL repair changed an earlier segment"
          check (decide ((← IO.FS.readBinFile keeper) = (if replaced then replacement else keeperBytes)))
            "WAL repair left the wrong keeper bytes"
          check (decide ((← IO.FS.readBinFile marker) = markerBytes)) "WAL repair changed the marker"
          let stagedPresent := calls.contains (.write staged) && !replaced
          check ((← staged.pathExists) == stagedPresent) "WAL repair exposed the wrong staging binding"
          if stagedPresent then
            check (decide ((← IO.FS.readBinFile staged) = replacement)) "WAL repair changed the staged prefix"
          for (first, bytes) in newer do
            let file := dir.file (.walSegment first)
            let removed := calls.contains (.remove file)
            check ((← file.pathExists) == !removed) s!"WAL repair exposed the wrong binding at {first}"
            unless removed do
              check (decide ((← IO.FS.readBinFile file) = bytes)) s!"WAL repair changed newer bytes at {first}"
        assertLayout completed renamed

        seen.set []
        attempt prepare false
        let pending := newer.filter fun file => !completed.contains (.remove (dir.file (.walSegment file.1)))
        let expectedRetry := [WalRepairFixtureCall.prepare, .sync #[dir.path]] ++
          pending.map (fun file => .remove (dir.file (.walSegment file.1))) ++ [.sync #[dir.path]] ++
          (if renamed then [.sync #[keeper]]
            else [.write staged, .sync #[staged], .rename staged keeper, .sync #[dir.path]])
        check ((← seen.get) == expectedRetry) "WAL repair retry used stale addresses or skipped a durability barrier"
        assertLayout expected true
      finally lock.unlock

private def checkProductionWalRotation (root : FilePath) (failDirectory : Bool) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let dir := (← DiskDirectory.open dir).path
  let first := dir / firstWalSegment
  let second := dir / "WAL-segment-1"
  let successor := dir / "WAL-segment-2"
  let marker := dir / "WAL.commit"
  let expectFiles := fun (last : ByteArray) (count : Nat) => do
    let names := ((← dir.readDir).toList.map (·.fileName)).filter (·.startsWith "WAL-segment-")
    check (names.length == 3 && names.contains firstWalSegment &&
      names.contains "WAL-segment-1" && names.contains "WAL-segment-2")
      "rotation or reopen changed the WAL segment names"
    check (decide ((← IO.FS.readBinFile first) = WAL.encodeFrame ⟨1, 4, some 40⟩ ∧
      (← IO.FS.readBinFile second) = WAL.encodeFrame ⟨2, 7, some 70⟩ ∧
      (← IO.FS.readBinFile successor) = last ∧
      (← IO.FS.readBinFile marker) = WAL.Boundary.encode (count * WAL.frameSize).toUInt64))
      "rotation or reopen changed exact segment bytes or the absolute marker"

  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected first rotation fixture sequence"
    db.checkpoint
    db.rotateWal
    check (← (IO.FS.readBinFile second).map ByteArray.isEmpty)
      "rotation did not install the empty successor"
    check ((← db.write 7 (some 70)) == 2) "append after rotation changed the absolute sequence"
  finally db.close
  expectManifest dir 1 1 0 1
  check (!(← successor.pathExists) && !(← (dir / "WAL").pathExists))
    "segmented write created an unexpected WAL binding"

  let target := if failDirectory then dir else successor
  let rotationSyncs := if failDirectory then [successor.toString, dir.toString] else [successor.toString]
  let (reported, syncs) ← probeDisk bin dir (some target) (operation := "--check-rotation-outcome")
    (skipFailures := if failDirectory then 1 else 0) (failureMode := .afterSync)
  check (reported && syncs == alignedWalSyncs dir second ++ rotationSyncs ++ [s!"synced before error: {target}"])
    s!"rotation did not report the error after syncing {target}"
  expectFiles ByteArray.empty 2
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [dir.toString])
    "rotation-cut reopen did not stop before syncing the successor binding"
  expectFiles ByteArray.empty 2
  let (opened, syncs) ← probeDisk bin dir (some dir) (failureMode := .afterSync)
  check (!opened && syncs == [dir.toString, s!"synced before error: {dir}"])
    "rotation-cut reopen did not report the error after syncing the successor binding"
  expectFiles ByteArray.empty 2

  let reopened ← DiskTable.open dir
  try
    let latest ← reopened.acquire
    check (latest.sequence == 2 && (← reopened.lookup latest.handle 7) == some (some 70))
      "reopen did not recover the second segment"
    check ((← reopened.write 4 (some 41)) == 3) "append after failed rotation used the wrong sequence"
  finally reopened.close
  let finalFrame := WAL.encodeFrame ⟨3, 4, some 41⟩
  expectFiles finalFrame 3

  let bare := dir / "WAL"
  let other := WAL.encodeFrame ⟨1, 4, some 99⟩
  IO.FS.writeBinFile bare other
  let .error (.userError cause) ← (DiskTable.open dir).toBaseIO
    | throw (IO.userError "open accepted mixed flat and segmented WAL bindings")
  check (cause == s!"unsupported flat WAL binding: '{bare}'") "open reported the wrong mixed-layout refusal"
  let (opened, syncs) ← probeDisk bin dir none
  check (!opened && syncs.isEmpty && decide ((← IO.FS.readBinFile bare) = other))
    "mixed-layout refusal performed a WAL durability effect"
  expectFiles finalFrame 3
  IO.FS.removeFile bare
  let final ← DiskTable.open dir
  try
    let some older ← final.acquireAt 1 | throw (IO.userError "rotation lost the checkpoint snapshot")
    let latest ← final.acquire
    let rows := (← final.range latest.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check ((← final.lookup older.handle 4) == some (some 40) &&
      latest.sequence == 3 && rows == some [(4, some 41), (7, some 70)])
      "segmented reopen changed the historical or current table"
  finally final.close
  expectFiles finalFrame 3

private def checkPublicSparsePruneRetry (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let dir := (← DiskDirectory.open dir).path
  let sealed := dir / firstWalSegment
  let keeper := dir / "WAL-segment-1"
  let later := [dir / "WAL-segment-3", dir / "WAL-segment-5"]
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.next"
  let first : WAL.Write := ⟨1, 4, some 40⟩
  let second : WAL.Write := ⟨2, 7, some 70⟩
  let replacement : WAL.Write := ⟨3, 4, some 41⟩
  let db ← DiskTable.open dir
  try
    check ((← db.write first.key first.value) == first.sequence) "unexpected sparse fixture first ordinal"
    db.checkpoint
    db.rotateWal
    check ((← db.write second.key second.value) == second.sequence) "unexpected sparse fixture second ordinal"
  finally db.close
  expectManifest dir 1 1 0 1
  let fixedPaths := [sealed, dir / "MANIFEST", dir / "run-1-0.v3"]
  let fixedBytes ← fixedPaths.mapM IO.FS.readBinFile
  check (fixedBytes.head? == some (WAL.encodeFrame first)) "sparse fixture sealed the wrong first frame"
  let acknowledged := WAL.encodeFrame second
  let excess := acknowledged ++ WAL.encodeFrame ⟨3, 4, none⟩
  let oldMarker := WAL.Boundary.encode (2 * WAL.frameSize).toUInt64
  let expectFiles := fun (activeBytes : ByteArray) (boundary : ByteArray) => do
    check (decide ((← fixedPaths.mapM IO.FS.readBinFile) = fixedBytes) &&
      (← IO.FS.readBinFile keeper) == activeBytes && (← IO.FS.readBinFile marker) == boundary &&
      !(← staged.pathExists)) "sparse prune retry changed a selected file or staging binding"
    for path in later do
      check (!(← path.pathExists)) s!"sparse prune kept the later name {path}"
  IO.FS.writeBinFile keeper excess
  for path in later do
    -- Discardable files need valid names and regular bindings, with unchecked payloads.
    IO.FS.writeBinFile path (ByteArray.mk #[255])
  let (opened, syncs) ← probeDisk bin dir (some dir) (skipFailures := 1)
  check (!opened && syncs == [dir.toString, dir.toString])
    "public reopen did not stop at the directory sync after pruning the sparse suffix"
  expectFiles excess oldMarker
  let recovered ← DiskTable.open dir
  try
    expectFiles acknowledged oldMarker
    let some historical ← recovered.acquireAt 1 | throw (IO.userError "sparse prune lost the checkpoint snapshot")
    let latest ← recovered.acquire
    let rows := (← recovered.range latest.handle 0 8).map (List.map fun row => (row.key, row.payload))
    check ((← recovered.lookup historical.handle 4) == some (some 40) &&
      latest.sequence == 2 && rows == some [(4, some 40), (7, some 70)])
      "sparse prune retry returned the wrong table"
    check ((← recovered.write replacement.key replacement.value) == replacement.sequence)
      "sparse prune retry did not resume at the next ordinal"
  finally recovered.close
  expectFiles (WAL.encode [second, replacement]) (WAL.Boundary.encode (3 * WAL.frameSize).toUInt64)

private def checkFirstBoundedCheckpointOpen (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let dir := (← DiskDirectory.open dir).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected first checkpoint ordinal"
    db.checkpoint
    db.rotateWal
    check ((← db.write 7 (some 70)) == 2) "unexpected second checkpoint ordinal"
    check (← db.advanceFloor 1) "could not set the retained checkpoint floor"
    db.checkpoint
    -- The checkpoint covers one frame in the first selected sealed span.
    check ((← db.write 4 (some 41)) == 3) "unexpected first replay ordinal"
    db.rotateWal
    check ((← db.write 7 none) == 4) "unexpected second replay ordinal"
    db.rotateWal
    check ((← db.write 6 (some 60)) == 5) "unexpected keeper ordinal"
  finally db.close
  let runFirst := dir / "run-2-0.v3"
  let runSecond := dir / "run-2-1.v3"
  let firstRun := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩]
  let secondRun := Compaction.encodeV3 [⟨7, 2, (0, 70)⟩]
  check (firstRun.size == secondRun.size && firstRun != secondRun)
    "reordered run fixture requires distinct equal-length payloads"
  let manifest := dir / "MANIFEST"
  let checkpoint := (Manifest.IntegrityCheckpoint.fromRuns ⟨2, 2, 1, 2⟩ [firstRun, secondRun]).encode
  let sealed := dir / "WAL-segment-1"
  let sealedBytes := WAL.encode [⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩]
  let keeper := dir / "WAL-segment-4"
  let keeperWrite : WAL.Write := ⟨5, 6, some 60⟩
  let retained := WAL.encodeFrame keeperWrite
  let excess := retained ++ WAL.encodeFrame ⟨6, 4, none⟩ ++ ByteArray.mk #[12, 34]
  let later := dir / "WAL-segment-6"
  let laterBytes := ByteArray.mk #[255]
  let marker := dir / "WAL.commit"
  let boundary := fun (sequence : Nat) => WAL.Boundary.encode (sequence * WAL.frameSize).toUInt64
  let fixed := [(dir / firstWalSegment, WAL.encodeFrame ⟨1, 4, some 40⟩),
    (dir / "WAL-segment-3", WAL.encodeFrame ⟨4, 7, none⟩)]
  let expectFiles := fun (files : List (FilePath × ByteArray)) => do
    for (path, bytes) in fixed ++ files do
      check ((← IO.FS.readBinFile path) == bytes) s!"unexpected bounded reopen bytes in {path}"
    check (!(← (dir / "WAL.next").pathExists) && !(← (dir / "WAL.commit.next").pathExists))
      "bounded reopen left a WAL staging file"
  let selected := [(manifest, checkpoint), (runFirst, firstRun), (runSecond, secondRun), (sealed, sealedBytes)]
  expectFiles (selected ++ [(keeper, retained), (marker, boundary 5)])
  IO.FS.writeBinFile keeper excess
  IO.FS.writeBinFile later laterBytes
  let expectInvalidOpen := fun (cause : String) (files : List (FilePath × ByteArray)) => do
    match ← (DiskTable.open dir).toBaseIO with
    | .error (.userError message) => check (message == cause) s!"unexpected bounded open error {message}"
    | .error error => throw error
    | .ok opened =>
      opened.close
      throw (IO.userError s!"bounded open accepted invalid data expected to report {cause}")
    let (opened, syncs) ← probeDisk bin dir none
    check (!opened && syncs.isEmpty) "invalid bounded open reached the WAL sync protocol"
    expectFiles (files ++ [(manifest, checkpoint), (keeper, excess), (later, laterBytes), (marker, boundary 5)])
  IO.FS.writeBinFile runFirst secondRun
  IO.FS.writeBinFile runSecond firstRun
  expectInvalidOpen checkpointIntegrityMismatch
    [(runFirst, secondRun), (runSecond, firstRun), (sealed, sealedBytes)]
  IO.FS.writeBinFile runFirst firstRun
  IO.FS.writeBinFile runSecond secondRun
  let corrupt := sealedBytes.set! 40 (sealedBytes[40]! ^^^ 1)
  IO.FS.writeBinFile sealed corrupt
  expectInvalidOpen "WAL checksum mismatch" [(runFirst, firstRun), (runSecond, secondRun), (sealed, corrupt)]
  IO.FS.writeBinFile sealed sealedBytes

  let recovered ← DiskTable.open dir
  try
    expectFiles (selected ++ [(keeper, retained), (marker, boundary 5)])
    check (!(← later.pathExists)) "bounded reopen kept an unselected later segment"
    check ((← recovered.acquireAt 0).isNone) "bounded reopen lost the checkpoint floor"
    expectSnapshot recovered 1 [(4, some 40)]
    expectSnapshot recovered 2 [(4, some 40), (7, some 70)]
    expectSnapshot recovered 3 [(4, some 41), (7, some 70)]
    expectSnapshot recovered 4 [(4, some 41)]
    expectSnapshot recovered 5 [(4, some 41), (6, some 60)]
    let latest ← recovered.acquire
    check (latest.sequence == 5) "bounded reopen installed the wrong last sequence"
    recovered.release latest.handle
    let appended : WAL.Write := ⟨6, 7, some 71⟩
    check ((← recovered.write appended.key appended.value) == appended.sequence)
      "bounded reopen appended at the wrong ordinal"
    let activeBytes := WAL.encode [keeperWrite, appended]
    expectFiles (selected ++ [(keeper, activeBytes), (marker, boundary 6)])
    expectSnapshot recovered 6 [(4, some 41), (6, some 60), (7, some 71)]
    recovered.checkpoint
    expectManifest dir 3 6 1 3
    let suffixRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩, ⟨6, 5, (0, 60)⟩,
      ⟨7, 6, (0, 71)⟩, ⟨7, 4, (1, 0)⟩]
    expectFiles [(runFirst, firstRun), (runSecond, secondRun), (sealed, sealedBytes),
      (keeper, activeBytes), (marker, boundary 6), (dir / "run-3-0.v3", firstRun),
      (dir / "run-3-1.v3", secondRun), (dir / "run-3-2.v3", suffixRun)]
  finally recovered.close

private def checkRetrySync (root : FilePath) : IO Unit := do
  let bin ← syncFixtureBin root
  let dir := root / "db"
  IO.FS.createDir dir
  let wal := dir / firstWalSegment
  let freshSyncs := [wal.toString, dir.toString]
  let alignedSyncs := alignedWalSyncs dir wal
  let stagedBoundary := dir / "WAL.commit.next"
  let publishedBoundary := dir / "WAL.commit"
  let zero := WAL.Boundary.encode 0
  IO.FS.writeBinFile stagedBoundary zero
  let (opened, syncs) ← probeDisk bin dir none
  check (!opened && syncs.isEmpty && !(← wal.pathExists) && !(← publishedBoundary.pathExists))
    "bootstrap accepted a staged marker with no empty segment"
  IO.FS.removeFile stagedBoundary
  for _ in [:2] do
    let (opened, syncs) ← probeDisk bin dir (some dir)
    check (!opened && syncs == freshSyncs) "open accepted a WAL name after failed directory sync"
    check (← wal.pathExists) "sync failure did not leave a visible WAL to retry"
  let (opened, syncs) ← probeDisk bin dir (some stagedBoundary) (failureMode := .afterSync)
  check (!opened && syncs == freshSyncs ++ [stagedBoundary.toString, s!"synced before error: {stagedBoundary}"] &&
    decide ((← IO.FS.readBinFile stagedBoundary) = zero) && !(← publishedBoundary.pathExists))
    "bootstrap did not stop at the synced staging marker with its zero segment intact"
  let (opened, syncs) ← probeDisk bin dir (some dir) (skipFailures := 1) (failureMode := .afterSync)
  check (!opened && syncs == freshSyncs ++ [stagedBoundary.toString, dir.toString, s!"synced before error: {dir}"] &&
    (← IO.FS.readBinFile publishedBoundary) == zero && !(← stagedBoundary.pathExists))
    "bootstrap did not report failure after publishing the exact zero marker"
  let (opened, syncs) ← probeDisk bin dir none
  check (opened && syncs == alignedSyncs) "bootstrap retry did not recover through the marked aligned route"
  let marker ← IO.FS.readBinFile publishedBoundary
  let .ok 0 := WAL.Boundary.decode marker | throw (IO.userError "fresh retry did not publish an empty boundary")
  check (← (IO.FS.readBinFile wal).map ByteArray.isEmpty) "fresh retry changed the empty WAL"
  let db ← DiskTable.open dir
  let _ ← db.write 7 (some 60)
  db.close
  let acknowledged ← IO.FS.readBinFile wal
  IO.FS.writeBinFile wal (acknowledged ++ (WAL.encodeFrame ⟨2, 7, some 99⟩).extract 0 11)
  let (opened, syncs) ← probeDisk bin dir (some dir) (skipFailures := 2)
  check (!opened && syncs == walReplacementSyncs dir)
    "fixture did not interrupt torn-tail repair after rename"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged)) "repair rename did not become visible"
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [dir.toString]) "repair retry skipped the directory sync for an aligned WAL"
  let (opened, syncs) ← probeDisk bin dir none
  check (opened && syncs == alignedSyncs) "successful repair retry skipped the recovery sync"
  let (written, syncs) ← probeDisk bin dir (some stagedBoundary) (operation := "--write-once")
  check (!written && syncs == alignedSyncs ++ [wal.toString, stagedBoundary.toString])
    "fixture did not fail at the grouped WAL and staged boundary sync"
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
  check (!written && syncs == alignedSyncs ++ [wal.toString, stagedBoundary.toString, dir.toString])
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
  let dir := (← DiskDirectory.open dir).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected initial write sequence"
    check ((← db.write 7 (some 70)) == 2) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 2) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 3) "unexpected overwrite sequence"
    db.rotateWal
    check ((← db.write 7 none) == 4) "unexpected tombstone sequence"
    db.rotateWal
    check ((← db.write 6 (some 60)) == 5) "unexpected insertion sequence"
  finally db.close
  let keeper := dir / "WAL-segment-4"
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.commit.next"
  let manifest := dir / "MANIFEST"
  let run := dir / "run-1-0.v3"
  let runBytes := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩, ⟨7, 2, (0, 70)⟩]
  let manifestBytes := (Manifest.IntegrityCheckpoint.fromRuns ⟨1, 2, 2, 1⟩ [runBytes]).encode
  let firstSpan := WAL.encode [⟨1, 4, some 40⟩, ⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩]
  let secondSpan := WAL.encodeFrame ⟨4, 7, none⟩
  let boundary := fun (active : ByteArray) =>
    WAL.Boundary.encode (firstSpan.size + secondSpan.size + active.size).toUInt64
  let expectFixedFiles := do
    for (path, bytes) in [(manifest, manifestBytes), (run, runBytes),
        (dir / firstWalSegment, firstSpan), (dir / "WAL-segment-3", secondSpan)] do
      check ((← IO.FS.readBinFile path) == bytes) s!"write and reopen trace changed {path}"
  let expectFiles := fun (events : List WAL.Write) => do
    let encoded := WAL.encode events
    check ((← IO.FS.readBinFile keeper) == encoded && (← IO.FS.readBinFile marker) == boundary encoded)
      "write and reopen trace changed the keeper or absolute WAL marker"
    expectFixedFiles
  let acknowledged : List WAL.Write := [⟨5, 6, some 60⟩]
  expectFiles acknowledged
  -- The first directory sync belongs to open.
  let (classified, syncs) ← probeDisk bin dir (some dir) (operation := "--check-write-outcome")
    (skipFailures := 1) (failureMode := .afterSync)
  let alignedSyncs := alignedWalSyncs dir keeper
  let expectedSyncs := alignedSyncs ++ [keeper.toString, staged.toString, dir.toString,
    s!"synced before error: {dir}"]
  check (classified && syncs == expectedSyncs)
    "write did not report an unknown commit after the final directory sync succeeded"
  let events := acknowledged ++ [⟨6, 7, some 99⟩]
  expectFiles events
  check (!(← staged.pathExists)) "durable append left a staged marker"
  -- These failed reopen processes exercise the visible files around two sync
  -- outcomes. Power-loss choices for unsynced files belong to the model.
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [dir.toString]) "reopen did not fail before syncing the directory"
  expectFiles events
  let (opened, syncs) ← probeDisk bin dir (some dir) (failureMode := .afterSync)
  check (!opened && syncs == [dir.toString, s!"synced before error: {dir}"])
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
  check (classified && syncs == alignedSyncs ++ [keeper.toString, staged.toString,
    s!"synced second target before error: {staged}"])
    "the later session did not report an unknown commit before publishing its marker"
  let durable := WAL.encode continued
  let appended := durable ++ WAL.encodeFrame ⟨9, 7, some 99⟩
  check ((← IO.FS.readBinFile keeper) == appended && (← IO.FS.readBinFile staged) == boundary appended &&
    (← IO.FS.readBinFile marker) == boundary durable)
    "the later failed append did not leave its full frame outside the active marker"
  expectFixedFiles
  let (opened, syncs) ← probeDisk bin dir (some dir) (skipFailures := 2) (failureMode := .afterSync)
  check (!opened && syncs == walReplacementSyncs dir ++ [s!"synced before error: {dir}"])
    "reopen did not report failure after settling the replacement keeper"
  expectFiles continued
  check (!(← (dir / "WAL.next").pathExists)) "settled keeper replacement left its staging file"
  -- The next opener sees an aligned keeper after the replacement.
  let (opened, syncs) ← probeDisk bin dir (some keeper) (failureMode := .afterSync)
  check (!opened && syncs == alignedSyncs ++ [s!"synced before error: {keeper}"])
    "retry did not take the aligned route and report the completed keeper sync error"
  expectFiles continued
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

private def checkGroupedSyncPartialEffects (root : FilePath) (failWal : Bool) : IO Unit := do
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
  let wal := dir / firstWalSegment
  let marker := dir / "WAL.commit"
  let staged := dir / "WAL.commit.next"
  let acknowledged := WAL.encode [⟨1, 7, some 70⟩, ⟨2, 4, some 41⟩]
  let oldMarker := WAL.Boundary.encode acknowledged.size.toUInt64
  let (opened, syncs) ← probeDisk bin dir (some dir) (failureMode := .afterSync)
  check (!opened && syncs == [dir.toString, s!"synced before error: {dir}"])
    "aligned reopen did not fail after syncing only the directory"
  check (decide ((← IO.FS.readBinFile wal) = acknowledged ∧ (← IO.FS.readBinFile marker) = oldMarker))
    "failed aligned reopen changed the acknowledged WAL"
  let bothTargets := alignedWalSyncs dir wal ++ [wal.toString, staged.toString]
  if failWal then
    let (classified, syncs) ← probeDisk bin dir (some wal) (operation := "--check-write-outcome")
      (skipFailures := 1)
    check (classified && syncs == bothTargets)
      "the grouped barrier skipped the staged marker after the WAL sync failed"
  else
    let (classified, syncs) ← probeDisk bin dir (some staged) (operation := "--check-write-outcome")
      (failureMode := .secondOnly)
    check (classified && syncs == bothTargets ++ [s!"synced second target before error: {staged}"])
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
  let wal := dir / firstWalSegment
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
  | .error (.userError message) =>
    check (message == s!"expected a regular database file: '{run}'") "installed run directory bypassed the file guard"
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
  check (opened && syncs == walReplacementSyncs dir)
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
  let beforePublish := alignedWalSyncs dir (dir / firstWalSegment) ++ [run.toString, dir.toString]
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
  let wal := dir / firstWalSegment
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
  let alignedOpen := alignedWalSyncs dir wal
  -- All candidate run contents can be synced while the manifest still names
  -- generation 2. The fixture completes the last file sync before returning an error.
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
  let wal := dir / firstWalSegment
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
  let expectedSyncs := alignedWalSyncs dir wal ++ [dir.toString, dir.toString]
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
  let dir := (← DiskDirectory.open dir).path
  let db ← DiskTable.open dir
  try
    check ((← db.write 4 (some 40)) == 1) "unexpected initial write sequence"
    check ((← db.write 7 (some 70)) == 2) "unexpected checkpoint write sequence"
    check (← db.advanceFloor 2) "could not advance the checkpoint floor"
    db.checkpoint
    check ((← db.write 4 (some 41)) == 3) "unexpected overwrite sequence"
    db.rotateWal
    check ((← db.write 7 none) == 4) "unexpected tombstone sequence"
    db.rotateWal
  finally db.close
  let keeper := dir / "WAL-segment-4"
  let marker := dir / "WAL.commit"
  let manifest := dir / "MANIFEST"
  let stagedManifest := dir / "MANIFEST.next"
  let stagedMarker := dir / "WAL.commit.next"
  let alignedOpen := alignedWalSyncs dir keeper
  let runSyncs := [dir / "run-2-0.v3", dir / "run-2-1.v3", dir, stagedManifest]
  let expectFiles := fun (files : List (FilePath × ByteArray)) => do
    for (path, expected) in files do
      check ((← IO.FS.readBinFile path) == expected) s!"unexpected checkpoint recovery bytes in {path}"
  let boundary := fun (through : Nat) => WAL.Boundary.encode (through * WAL.frameSize).toUInt64
  let firstSpan := WAL.encode [⟨1, 4, some 40⟩, ⟨2, 7, some 70⟩, ⟨3, 4, some 41⟩]
  let secondSpan := WAL.encodeFrame ⟨4, 7, none⟩
  let expectWal := fun (events : List WAL.Write) (through : Nat) =>
    expectFiles [(dir / firstWalSegment, firstSpan), (dir / "WAL-segment-3", secondSpan),
      (keeper, WAL.encode events), (marker, boundary through)]
  let expectFailedAlignedOpens := fun (expectUnchanged : IO Unit) => do
    let (opened, syncs) ← probeDisk bin dir (some dir)
    check (!opened && syncs == [dir.toString])
      "checkpoint-cut reopen did not stop before its first directory sync"
    expectUnchanged
    let (opened, syncs) ← probeDisk bin dir (some keeper) (failureMode := .afterSync)
    check (!opened && syncs == alignedOpen ++ [s!"synced before error: {keeper}"])
      "checkpoint-cut reopen did not report the error after syncing the aligned keeper"
    expectUnchanged
  let firstRun := Compaction.encodeV3 [⟨4, 1, (0, 40)⟩, ⟨7, 2, (0, 70)⟩]
  let oldBytes := (Manifest.IntegrityCheckpoint.fromRuns ⟨1, 2, 2, 1⟩ [firstRun]).encode
  let oldRun := (dir / "run-1-0.v3", firstRun)
  let newRuns := fun secondRun => [(dir / "run-2-0.v3", firstRun), (dir / "run-2-1.v3", secondRun)]
  let pendingRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩, ⟨7, 4, (1, 0)⟩]
  let pendingBytes := (Manifest.IntegrityCheckpoint.fromRuns ⟨2, 4, 4, 2⟩ [firstRun, pendingRun]).encode
  let (published, syncs) ← probeDisk bin dir (some stagedManifest) (operation := "--checkpoint-once")
    (extraArgs := #["4"])
  check (!published && syncs == alignedOpen ++ runSyncs.map FilePath.toString)
    "checkpoint fixture did not fail before the new manifest rename"
  let expectUnpublished :=
    expectFiles ([(manifest, oldBytes), oldRun, (stagedManifest, pendingBytes)] ++ newRuns pendingRun)
  expectUnpublished
  expectWal [] 4
  expectFailedAlignedOpens do
    expectUnpublished
    expectWal [] 4
  -- The old checkpoint replays both sealed spans and resumes from an empty keeper.
  let (written, syncs) ← probeDisk bin dir (some stagedMarker) (operation := "--write-once")
  check (!written && syncs == alignedOpen ++ [keeper.toString, stagedMarker.toString])
    "write fixture did not fail before the new WAL marker rename"
  expectWal [⟨5, 7, some 99⟩] 4
  expectFiles [(stagedMarker, boundary 5)]
  let (opened, syncs) ← probeDisk bin dir (some dir) (skipFailures := 2)
  check (!opened && syncs == walReplacementSyncs dir)
    "reopen did not fail at the directory sync after repairing the WAL"
  expectWal [] 4
  let (opened, syncs) ← probeDisk bin dir (some dir)
  check (!opened && syncs == [dir.toString]) "reopen retry did not sync the directory for the repaired WAL"
  let replacement : WAL.Write := ⟨5, 7, some 71⟩
  let throughFive : List (UInt64 × Option UInt64) := [(4, some 41), (7, some 71)]
  let recovered ← DiskTable.open dir
  try
    expectUnpublished
    check ((← recovered.acquireAt 1).isNone) "reopen lost the checkpoint floor"
    expectSnapshot recovered 2 [(4, some 40), (7, some 70)]
    expectSnapshot recovered 3 [(4, some 41), (7, some 70)]
    expectSnapshot recovered 4 [(4, some 41)]
    check ((← recovered.write replacement.key replacement.value) == replacement.sequence)
      "reopen did not reuse the discarded write sequence"
  finally recovered.close
  let final ← DiskTable.open dir
  try
    expectWal [replacement] 5
    expectSnapshot final 5 throughFive
  finally final.close

  -- The first directory sync belongs to open and the second protects the run
  -- entries. The third settles the replacement manifest before reporting error.
  let (published, syncs) ← probeDisk bin dir (some dir) (operation := "--checkpoint-once")
    (skipFailures := 2) (failureMode := .afterSync) (extraArgs := #["4"])
  check (!published && syncs == alignedOpen ++ runSyncs.map FilePath.toString ++
    [dir.toString, s!"synced before error: {dir}"])
    "checkpoint did not report failure after syncing the replacement manifest"
  let secondRun := Compaction.encodeV3 [⟨4, 3, (0, 41)⟩, ⟨7, 5, (0, 71)⟩, ⟨7, 4, (1, 0)⟩]
  let newBytes := (Manifest.IntegrityCheckpoint.fromRuns ⟨2, 5, 4, 2⟩ [firstRun, secondRun]).encode
  let expectPublished := do
    expectFiles ([(manifest, newBytes), oldRun] ++ newRuns secondRun)
    check (!(← stagedManifest.pathExists)) "synced publication left a staged manifest"
  expectPublished
  expectWal [replacement] 5
  expectFailedAlignedOpens do
    expectPublished
    expectWal [replacement] 5
  let appended : WAL.Write := ⟨6, 6, some 60⟩
  let reopened ← DiskTable.open dir
  try
    check ((← reopened.acquireAt 3).isNone) "reopen used the old manifest floor"
    expectSnapshot reopened 4 [(4, some 41)]
    expectSnapshot reopened 5 throughFive
    check ((← reopened.write appended.key appended.value) == appended.sequence)
      "write after checkpoint recovery used the wrong sequence"
  finally reopened.close
  let final ← DiskTable.open dir
  try
    expectPublished
    expectWal [replacement, appended] 6
    check ((← final.acquireAt 3).isNone) "later reopen lost the replacement floor"
    let latest ← final.acquire
    check (latest.sequence == appended.sequence) "later reopen installed the wrong latest sequence"
    final.release latest.handle
    expectSnapshot final 4 [(4, some 41)]
    expectSnapshot final 5 throughFive
    expectSnapshot final 6 [(4, some 41), (6, some 60), (7, some 71)]
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

private def probeWord (input : String) : IO UInt64 := do
  let some word := input.toNat? | throw (IO.userError "expected an unsigned fixture integer")
  unless word < UInt64.size do throw (IO.userError "fixture integer exceeds UInt64")
  return word.toUInt64

private def checkRecoveredProbe (path : FilePath) (sequence value : UInt64) (resume : Bool) : IO Unit := do
  let db ← DiskTable.open path
  try
    let latest ← db.acquire
    check (latest.sequence == sequence && (← db.lookup latest.handle 7) == some (some value))
      "reopen did not return the expected sequence and value"
    if resume then
      check ((← db.write 7 (some 101)) == sequence + 1) "reopen did not permit the next append"
      let next ← db.acquire
      check (next.sequence == sequence + 1 && (← db.lookup next.handle 7) == some (some 101))
        "next append returned the wrong value or sequence"
  finally db.close

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
      check (message.startsWith s!"sync failed for '{dir}':")
        "collection did not preserve its sync error"
      for name in ["run-2-0.v3", "run-2-1.v3"] do
        check (!(← (dir / name).pathExists)) "collection sync did not follow the obsolete unlinks"
      check (latest.sequence == 5 && (← db.lookup latest.handle 6) == some (some 60))
        "collection sync error invalidated the active session"
      db.collectObsoleteRuns
    finally db.close
  | "--write-once" :: dir :: values =>
    let value ← match values with
      | [] => pure 99
      | [input] => probeWord input
      | _ => throw (IO.userError "unexpected write fixture arguments")
    let db ← DiskTable.open ⟨dir⟩
    try
      let _ ← db.write 7 (some value)
    finally db.close
  | ["--check-recovered-table", dir, sequence, value] =>
    checkRecoveredProbe ⟨dir⟩ (← probeWord sequence) (← probeWord value) false
  | ["--resume-recovered", dir, sequence, value] =>
    checkRecoveredProbe ⟨dir⟩ (← probeWord sequence) (← probeWord value) true
  | ["--rotate-wal-once", dir] =>
    let db ← DiskTable.open ⟨dir⟩
    try db.rotateWal finally db.close
  | ["--check-rotation-outcome", dir] =>
    let some target ← IO.getEnv "ALVOKI_CHECK_SYNC_FAIL"
      | throw (IO.userError "missing rotation sync fault target")
    let db ← DiskTable.open ⟨dir⟩
    try
      let .error (.userError message) ← db.rotateWal.toBaseIO
        | throw (IO.userError "rotation did not report its sync error")
      check (message.startsWith s!"sync failed for '{target}':")
        "rotation did not preserve its sync error"
      expectRejectedWrite db "publication failed; reopen the database"
    finally db.close
  | ["--check-write-outcome", dir] =>
    let some target ← IO.getEnv "ALVOKI_CHECK_SYNC_FAIL"
      | throw (IO.userError "missing sync fault target")
    let db ← DiskTable.open ⟨dir⟩
    try
      let .error (.commitUnknown (.userError message)) ← (db.writeWithOutcome 7 (some 99)).toBaseIO
        | throw (IO.userError "sync error did not report an unknown commit outcome")
      check (message.startsWith s!"sync failed for '{target}':")
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
  | [] => withSyncFixture do
    checkCodecs
    checkPublicationCuts
    IO.FS.withTempDir checkSegmentedCheckpointOpen
    IO.FS.withTempDir checkReopen
    IO.FS.withTempDir checkInterruptedPublication
    IO.FS.withTempDir checkMissingAndMalformedFiles
    IO.FS.withTempDir checkCoveredWalDuplicate
    IO.FS.withTempDir checkBoundedRecovery
    IO.FS.withTempDir checkDirectoryIdentity
    IO.FS.withTempDir checkDanglingFiles
    IO.FS.withTempDir checkLockBindingGuards
    IO.FS.withTempDir checkStaleWalStaging
    IO.FS.withTempDir checkActiveWalGuard
    IO.FS.withTempDir checkCheckpointRunAliases
    IO.FS.withTempDir checkSnapshotSessions
    IO.FS.withTempDir checkMarkerlessRefusal
    IO.FS.withTempDir checkWalSegmentRotation
    IO.FS.withTempDir checkWalSegmentReads
    IO.FS.withTempDir checkWalSegmentRepair
    for failDirectory in [false, true] do
      IO.FS.withTempDir (checkProductionWalRotation · failDirectory)
    IO.FS.withTempDir checkPublicSparsePruneRetry
    IO.FS.withTempDir checkFirstBoundedCheckpointOpen
    IO.FS.withTempDir checkRetrySync
    IO.FS.withTempDir checkWritesAcrossReopens
    for failWal in [false, true] do
      IO.FS.withTempDir (checkGroupedSyncPartialEffects · failWal)
    IO.FS.withTempDir checkCheckpointReadFailureBeforeWalRepair
    IO.FS.withTempDir checkFirstCheckpointCuts
    IO.FS.withTempDir checkCheckpointRetryWithFewerRuns
    IO.FS.withTempDir checkObsoleteRunCollection
    IO.FS.withTempDir checkRecoveryAfterCheckpointAndWriteFailures
    IO.println "Passed disk identity, segmented WAL rotation and replay, checkpoint cuts, and sync retry checks."
  | _ => throw (IO.userError "unexpected disk fixture arguments")
