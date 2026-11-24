import Alvoki.Storage.Disk.CheckpointHistory
import Alvoki.Storage.Disk.MarkedSessionTrace

namespace Alvoki.WAL.Boundary
open Storage

/-- The live names and every admitted crash image of the owned, durable
directory lack a manifest, WAL and WAL marker. -/
def ReopenImage.Fresh (image : ReopenImage) : Prop :=
  image.directory.active = ⟨none, none⟩ ∧
    image.directory.crashImages = [image.directory.active] ∧
    image.wal.active = none ∧ image.wal.crashImages = [none]

/-- The locked Linux callbacks report their outcomes. A successful create
exposes an empty WAL, a successful grouped sync settles its bytes and name,
and the marker callbacks obey the ordinary replacement step contract. An
error has no result image here, since it may have applied partial effects. -/
structure FreshOpenReports where
  createWal : Except String Unit
  syncWalDirectory : Except String Unit
  marker : Publication.Step → Except String Unit

private abbrev FreshOpenM := StateT ReopenImage (Except String)

private def observed (result : Except String α) : FreshOpenM α :=
  fun image => result.map (·, image)

private def visibleEmptyWal (image : ReopenImage) : ReopenImage :=
  { image with wal := { image.wal with
      active := some ByteArray.empty
      crashImages := some ByteArray.empty :: image.wal.crashImages } }

private def createEmptyWal (report : Except String Unit) : FreshOpenM ByteArray :=
  fun image => report.map fun () => (ByteArray.empty, visibleEmptyWal image)

private def syncNewWal (report : Except String Unit) : FreshOpenM Unit :=
  fun image => report.map fun () => ((), image.syncDirectory)

private def publishMarker (report : Publication.Step → Except String Unit)
    (bytes : ByteArray) (step : Publication.Step) : FreshOpenM Unit := fun image => do
  report step
  let some directory := image.directory.step .walBoundary bytes step |
    throw "fresh WAL marker replacement was not ready"
  return ((), { image with directory })

/-- Model the fresh branch of `DiskTable.openLocked`. Opening the checkpoint and
the optional WAL files uses the shared read protocols. An absent WAL with
absent metadata triggers creation, then the aligned reopen durability action
and the full marker replacement precede returning the installed data. -/
def runFreshMarkedOpen (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) (reports : FreshOpenReports) :
    StateT ReopenImage (Except String) (PackedTable × UInt64 × Nat) := do
  let checkpoint ← observed checkpoint
  let (base, generation) := checkpoint.getD (.empty, 0)
  withOpenWal (observed marker) (observed wal) observed (fun boundary => do
    if checkpoint.isSome || boundary.isSome then observed (.error missingOpenWal)
    else createEmptyWal reports.createWal) fun boundary bytes => do
    if boundary.isSome then observed (.error "expected a fresh unmarked WAL")
    else
      let selected := (WAL.repairPrefix bytes).getD bytes
      let table ← observed (recoverSelected base selected)
      let table ← Publication.finishReopen bytes.size selected.size
        (fun _ => observed (.error "unexpected repair of a new empty WAL"))
        (fun _ => syncNewWal reports.syncWalDirectory) table
      unless selected.size < UInt64.size do observed (.error "WAL byte count is too large")
      Publication.run (publishMarker reports.marker (encode selected.size.toUInt64))
      return (table, generation, selected.size)

private theorem emptyReplay : recoverSelected .empty ByteArray.empty = .ok .empty := by
  exact recoverSelected_encoded .empty [] [] trivial rfl

private def afterFreshOpen (before : ReopenImage) : ReopenImage :=
  ⟨{ before.directory with
      active := before.directory.active.replace .walBoundary (encode 0)
      crashImages := [before.directory.active.replace .walBoundary (encode 0)]
      staged := fun entry => if entry = .walBoundary then none else before.directory.staged entry },
    { before.wal with active := some ByteArray.empty, crashImages := [some ByteArray.empty] }⟩

private theorem runFreshMarkedOpen_absent
    (before : ReopenImage) (reports : FreshOpenReports)
    (created : reports.createWal = .ok ()) (synced : reports.syncWalDirectory = .ok ())
    (published : ∀ step, reports.marker step = .ok ()) :
    (runFreshMarkedOpen (.ok none) (.ok none) (.ok none) reports).run before =
      .ok ((.empty, 0, 0), afterFreshOpen before) := by
  simp [runFreshMarkedOpen, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, Except.map,
    observed, withOpenWal, Option.mapM,
    createEmptyWal, created, WAL.repairPrefix,
    emptyReplay, Publication.finishReopen, Publication.runReopen, syncNewWal, synced, published,
    Publication.run, Publication.steps, publishMarker, visibleEmptyWal, ReopenImage.syncDirectory,
    DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.step]
  change Except.ok ((PackedTable.empty, (0 : UInt64), (0 : Nat)),
    (⟨{ before.directory with
      active := before.directory.active.replace .walBoundary (encode 0),
      crashImages := [before.directory.active.replace .walBoundary (encode 0)],
      staged := fun entry => if entry = .walBoundary then none else
        if entry = .walBoundary then some (encode 0, true) else
        if entry = .walBoundary then some (encode 0, false) else before.directory.staged entry },
      { before.wal with active := some ByteArray.empty, crashImages := [some ByteArray.empty] }⟩ :
      ReopenImage)) = _
  unfold afterFreshOpen
  congr 4
  funext entry
  cases entry <;> rfl

/-- Successful locked file operations on a fresh directory give the first
marked writer and its absent checkpoint. The observed reads determine the
branch, and the effect trace determines the actual installed table and
settled file image. The session starts with generation and byte count zero. -/
theorem freshMarkedOpen_ready {before : ReopenImage} (fresh : before.Fresh)
    {checkpointImage : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations checkpointImage before.directory.active.manifest)
    (walReads : MarkedWalReads before) {observedManifest observedMarker observedWal : Option ByteArray}
    (readManifest : checkpointReads.readManifest = .ok observedManifest)
    (readMarker : walReads.marker = .ok observedMarker) (readWal : walReads.wal = .ok observedWal)
    (reports : FreshOpenReports)
    (created : reports.createWal = .ok ()) (synced : reports.syncWalDirectory = .ok ())
    (published : ∀ step, reports.marker step = .ok ()) :
    ∃ (after : ReopenImage) (fixed : FixedMarkedCheckpoint),
      let writer : MarkedWriterState := ⟨.empty, 0, after, []⟩
      (runFreshMarkedOpen checkpointReads.result walReads.marker walReads.wal reports).run before =
          .ok ((writer.table, 0, writer.walBytes), writer.image) ∧
      writer.ReadyFor fixed.manifest ∧ fixed.manifest = none ∧ fixed.covered = [] ∧
      fixed.image.manifest = writer.image.directory.project .manifest ∧
      writer.table.Refines fixed.model ∧ RepresentsWalHistory writer.history fixed.model := by
  have active := fresh.1
  have absentManifest : observedManifest = none :=
    (checkpointReads.manifestVisible _ readManifest).trans
      (congrArg DirectoryPublication.Bindings.manifest active)
  have absentMarker : observedMarker = none := (walReads.markerVisible _ readMarker).symm.trans
    (congrArg DirectoryPublication.Bindings.walBoundary active)
  have absentWal : observedWal = none := (walReads.walVisible _ readWal).symm.trans fresh.2.2.1
  have load : checkpointReads.result = .ok none := by
    rw [CheckpointReadObservations.result, readManifest, absentManifest]
    rfl
  let after := afterFreshOpen before
  let fixed : FixedMarkedCheckpoint := {
    manifest := none
    files := []
    image := { checkpointImage with manifest := after.directory.project .manifest }
    walSequence := 0
    table := .empty
    model := .empty
    covered := []
    written := .absent
    accepted := trivial
    represents := PackedTable.empty_refines
    watermark := rfl
  }
  refine ⟨after, fixed, ?_, ?_, rfl, rfl, rfl, PackedTable.empty_refines, RepresentsWalHistory.empty⟩
  · rw [load, readMarker, absentMarker, readWal, absentWal]
    exact runFreshMarkedOpen_absent before reports created synced published
  · have fits : 0 < UInt64.size := by decide
    refine ⟨?_, trivial, rfl, rfl, fits, PackedTable.empty_rowBounds⟩
    refine ⟨?_, rfl, rfl, rfl⟩
    change before.directory.active.replace .walBoundary (encode 0) = ⟨none, some (encode 0)⟩
    rw [active]
    rfl

end Alvoki.WAL.Boundary
