import Alvoki.Storage.Disk.DiskTable

open System Alvoki Alvoki.Storage
open Alvoki.Storage.WalSegmentRepair (Plan Reopened KeeperPrefix)
open WAL (frameSize)

private def optionalRead (path : FilePath) : IO (Option ByteArray) :=
  readOptionalDatabaseFile path.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile path)
    (fun _ => IO.userError "expected regular optional file") throw

private def ensurePrivateFile (metadata : IO.FS.Metadata) : IO Unit :=
  unless metadata.type == .file && metadata.numLinks == 1 do
    throw (IO.userError "expected singly linked regular segment")

private def inspectSegment (path : FilePath) : IO (Except IO.Error IO.FS.Metadata) := do
  let result ← path.symlinkMetadata.toBaseIO
  if let .ok metadata := result then ensurePrivateFile metadata
  pure result

private def readRegular (path : FilePath) : IO ByteArray := do
  let metadata ← path.symlinkMetadata
  unless metadata.type == .file do throw (IO.userError "expected regular read file")
  IO.FS.readBinFile path

private def readExact (file : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  if remaining = 0 then return bytes
  let chunk ← file.read remaining.toUSize
  if _guard : 0 < chunk.size ∧ chunk.size ≤ remaining then
    readExact file (remaining - chunk.size) (if bytes.isEmpty then chunk else bytes ++ chunk)
  else throw (IO.userError "short or oversized WAL keeper read")
termination_by remaining

private def readPrefix (path : FilePath) (count : Nat) : IO KeeperPrefix := do
  let metadata ← path.symlinkMetadata
  ensurePrivateFile metadata
  unless count ≤ metadata.byteSize.toNat ∧ count < USize.size do
    throw (IO.userError "WAL keeper does not cover its selected prefix")
  let file ← IO.FS.Handle.mk path .read
  return ⟨← readExact file count ByteArray.empty, metadata.byteSize.toNat⟩

private def serialReplay (dir : DiskDirectory) (through : Nat) (base : PackedTable)
    (first : Nat) (rest : List Nat) : IO (PackedTable × Nat × KeeperPrefix) := do
  let path := dir.file (.walSegment first)
  match rest with
  | [] =>
    let count := (through - first) * frameSize
    let keeper ← readPrefix path count
    unless keeper.bytes.size = count ∧ count ≤ keeper.fileSize do
      throw (IO.userError "invalid WAL keeper prefix or physical size")
    let table ← IO.ofExcept (recoverRetainedFrom base first keeper.bytes)
    return (table, first, keeper)
  | next :: remaining =>
    let bytes ← readRegular path
    unless first < next ∧ bytes.size = (next - first) * frameSize do
      throw (IO.userError "invalid selected WAL segment spans")
    let table ← IO.ofExcept (recoverRetainedFrom base first bytes)
    serialReplay dir through table next remaining

private structure SegmentFoldState where
  table : PackedTable
  spansValid : Bool := true
  decodeError : Option String := none
  replayError : Option String := none

private def SegmentFoldState.consume (state : SegmentFoldState) (first : Nat)
    (bytes : ByteArray) (validSpan : Bool) : SegmentFoldState :=
  if !validSpan then { state with spansValid := false }
  else if !state.spansValid || state.decodeError.isSome then state
  else
    match WAL.decodeOrdinalsFrom (first + 1) bytes with
    | .error message => { state with decodeError := some message }
    | .ok events =>
      if state.replayError.isSome then state
      else match replay state.table (events.drop (state.table.committed.toNat - first)) with
      | .error message => { state with replayError := some message }
      | .ok table => { state with table }

private def replayDeferred (dir : DiskDirectory) (through : Nat) (state : SegmentFoldState)
    (first : Nat) (rest : List Nat) : IO (PackedTable × Nat × KeeperPrefix) := do
  let path := dir.file (.walSegment first)
  match rest with
  | [] =>
    let count := (through - first) * frameSize
    let keeper ← readPrefix path count
    unless keeper.bytes.size = count ∧ count ≤ keeper.fileSize do
      throw (IO.userError "invalid WAL keeper prefix or physical size")
    let state := state.consume first keeper.bytes (decide (first ≤ through))
    unless state.spansValid do throw (IO.userError "invalid selected WAL segment spans")
    if let some message := state.decodeError then throw (IO.userError message)
    if let some message := state.replayError then throw (IO.userError message)
    unless state.table.committed.toNat == through do
      throw (IO.userError "selected WAL frame count disagrees with the recovered sequence")
    return (state.table, first, keeper)
  | next :: remaining =>
    let bytes ← readRegular path
    let state := state.consume first bytes (decide (first ≤ through ∧ first < next ∧
      bytes.size = (next - first) * frameSize))
    replayDeferred dir through state next remaining

private def prepareSerial (dir : DiskDirectory) (deferErrors : Bool) : IO (Plan × Reopened × Nat) := do
  let checkpoint ← readIntegrityCheckpoint (optionalRead (dir.file .manifest))
    (fun generation index => readRegular (dir.file (.run generation index))) IO.ofExcept
  let (base, generation) := checkpoint.getD (.empty, 0)
  let some marker ← optionalRead (dir.file .walBoundary)
    | throw (IO.userError "segmented WAL is missing its commit marker")
  let length ← IO.ofExcept (WAL.Boundary.decode marker)
  let through := length.toNat / frameSize
  unless length.toNat % frameSize = 0 ∧ base.committed.toNat ≤ through do
    throw (IO.userError "invalid absolute WAL segment marker")
  let entries ← dir.path.readDir
  let offsets ← scanWalSegmentOffsets (probeWalSegmentWith dir inspectSegment)
    (entries.toList.map (·.fileName))
  let some (first :: remaining, newer) := selectWalSegmentReadsThrough offsets base.committed.toNat through
    | throw (IO.userError "no WAL segment covers the checkpoint watermark")
  let (table, keeper, kept) ←
    if deferErrors then replayDeferred dir through { table := base } first remaining
    else serialReplay dir through base first remaining
  return (⟨through, keeper, newer, kept.bytes⟩, ⟨table, generation, length, keeper⟩, kept.fileSize)

def prepareVectorEarly [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (Plan × Reopened × Nat) := do
  let checkpoint ← readIntegrityCheckpoint (readOptional (dir.file .manifest))
    (fun generation index => readBin (dir.file (.run generation index)))
    (fun report => liftExcept (report.mapError IO.userError))
  let (base, generation) := checkpoint.getD (.empty, 0)
  let some marker ← readOptional (dir.file .walBoundary)
    | throw (IO.userError "segmented WAL is missing its commit marker")
  let length ← liftExcept ((WAL.Boundary.decode marker).mapError IO.userError)
  let (⟨files, newer⟩, keeperFileSize) ← WalSegmentRepair.readSelectedWithPrefix dir base.committed.toNat length list lstat readBin readPrefix
  let some (keeper, keeperBytes) := files.getLast?
    | throw (IO.userError "no WAL segment covers the commit marker")
  let (_, table) ← liftExcept ((recoverMarkedWalSegments base length files).mapError IO.userError)
  return (⟨length.toNat / frameSize, keeper, newer, keeperBytes⟩,
    ⟨table, generation, length, keeper⟩, keeperFileSize)

def main (args : List String) : IO Unit := do
  match args with
  | ["manifest", dir, watermark] =>
    let some sequence := watermark.toNat? | throw (IO.userError "invalid watermark")
    let manifest := Manifest.IntegrityCheckpoint.fromRuns ⟨1, sequence.toUInt64, sequence.toUInt64, 0⟩ []
    IO.FS.writeBinFile ((⟨dir⟩ : FilePath) / "MANIFEST") manifest.encode
  | mode :: dir :: options =>
    let deep := options == ["--deep"]
    unless options.isEmpty || deep do throw (IO.userError "expected optional --deep")
    let dir ← DiskDirectory.open ⟨dir⟩
    let lock ← IO.FS.Handle.mk (dir.file .lock) .append
    unless ← lock.tryLock do throw (IO.userError "experiment could not hold the directory lock")
    try
      let start ← IO.monoNanosNow
      let (plan, result, size) ←
        if mode == "vector" then
          WalSegmentRepair.prepareBoundedMarkedWith dir optionalRead FilePath.readDir inspectSegment readRegular readPrefix
        else if mode == "early" then
          prepareVectorEarly dir optionalRead FilePath.readDir inspectSegment readRegular readPrefix
        else if mode == "deferred" then prepareSerial dir true
        else if mode == "serial" then prepareSerial dir false
        else throw (IO.userError "expected vector, early, serial, or deferred mode")
      let elapsed := (← IO.monoNanosNow) - start
      let table := result.table
      let selected := table.committed.toNat
      let rows := table.memory.rows.length
      let lowest := table.lookupAt 0 table.committed
      IO.println s!"{elapsed},{selected},{result.generation},{rows},{lowest},{plan.keeper},{plan.keeperBytes.size},{size}"
      if deep then
        let (path, count) := (dir.file (.walSegment plan.keeper), plan.keeperBytes.size)
        let actual ← IO.FS.readBinFile path
        unless plan.keeperBytes == actual.extract 0 count do
          throw (IO.userError "experiment returned a different keeper prefix")
        let rows := table.rangeAt 0 selected.toUInt64 table.committed
        IO.println <| String.intercalate "," <| rows.map (fun row => s!"{row.key}:{row.payload.getD 0}")
        IO.println s!"{table.pins.floor},{plan.newer}"
    finally lock.unlock
  | _ => throw (IO.userError "invalid experiment arguments")
