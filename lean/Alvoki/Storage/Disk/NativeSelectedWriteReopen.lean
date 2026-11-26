import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.NativeWriteCrashReads
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The file bindings selected by the marked opener. This footprint
contains exactly the chosen runs and WAL files, even if another
directory entry with a staging name survived. -/
def CanonicalKeeperLayout.selectedFilePath {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.file .manifest ∨ path = directory.file .walBoundary ∨
    (∃ segment ∈ layout.sealed ++ [layout.keeper], path = directory.file (.walSegment segment.first)) ∨
    ∃ bytes metadata index, image.directory.active.manifest = some bytes ∧
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata ∧ index < metadata.header.runCount.toNat ∧
      path = directory.file (.run metadata.header.generation index)

/-- The same admission also observes the enclosing directory and lock. -/
def CanonicalKeeperLayout.reopenPath {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ path = directory.file .lock ∨ layout.selectedFilePath directory path

section

variable {heap stream : Type} {state : NativeReadyState} {crash : WriteCrashView} {input : FilePath}
  {retry : LockedFileState FileImage} {vacant : TryLockObserves retry.owners state.session.directory (.ok true)}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    retry.image.directory.active.manifest state.writer.checkpoint}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {rebooted entry : heap} {returns : List (FilePath × IO.Error)}
  {release : IO.FS.Handle → heap → heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

local notation "dir" => state.session.directory
local notation "selection" => layout.selectedFilePath state.session.directory
local notation "footprint" => layout.reopenPath state.session.directory

/-- A selected crash image supplies the same canonical inodes and
bytes after the actual failed opens. The next measured keeper repair
and reference allocations return the table of that same replay. -/
theorem NativeWriteCrashReads.reopensAfterReadOnlyAttempts
    (reader : NativeWriteCrashReads crash input vacant layout selected)
    (raw : RawHealthyMarkedOpenEffects reader.opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (attempts : RawFinalizedOpenAttempts view dir calls init release rebooted returns entry)
    (files : heap → CheckpointSurvivingFiles)
    (rebootNames : ∀ path, footprint path → (files rebooted).names path = crash.names path)
    (rebootBytes : ∀ path, selection path → ∀ inode, crash.names path = some inode →
      (files rebooted).bytes inode = [crash.contents inode])
    (beforeFlockFrame : ∀ path before (failed : RawBeforeFlockRejection view calls path before),
      (files before).Frames footprint (files failed.reached))
    (flockErrorFrame : ∀ path before (failed : RawFlockRejection view calls dir release path before),
      (files before).Frames footprint (files failed.reached))
    (heldFrame : ∀ path before (failed : RawFinalizedOpenAttempt view dir calls init release path before),
      (files before).Frames footprint (files failed.reached))
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : state.writer.published.AcceptsVersioned history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix history) retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {wal : WalSegmentImage} (walLayout : wal.ReadLayout history) (walValid : wal.Valid history)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize)
    (active : wal.directory.active = layout.target.pair) (keeper : layout.target.first = wal.active.first)
    (kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept)
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (pending : PendingClientReplay log reads history) (bounded : ∀ read ∈ reads, read.BoundedBy history.length)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache
      (assemble resolved lock cache))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    (view.files rebooted).image = retry.image ∧
    (files entry).names (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description) ∧
    (files entry).names ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description) ∧
    (∀ path, selection path → (files entry).names path = crash.names path) ∧
    (∀ path payload, selection path → reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        (files entry).names path = some read.object ∧ (files entry).bytes read.object = [payload]) ∧
    reader.opening.finish.UsesMeasuredRepair ∧
    ∃ (next : NativeReadPosition history log)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      raw.openTable bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨history, log, next⟩ ∧ next.reads = reads ∧ next.initial = next.state ∧
      next.state.writer.target = layout.target ∧ next.state.files.image.Ready layout.target ∧
      next.state.writer.checkpoint = state.writer.checkpoint ∧
      next.state.writer.published.durable = state.writer.published.durable ∧
      handle.lock = raw.raw.lock ∧ handle.files.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef
        raw.seed.directoryRef ∧ handle.files.AtDirectory (dir).path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef = next.state.cache := by
  have frame := attempts.frames (frame := fun a b => (files a).Frames footprint (files b))
    (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) CheckpointSurvivingFiles.Frames.trans
    beforeFlockFrame flockErrorFrame heldFrame
  have fileImage := attempts.preserves.2
  rw [raw.raw.entryFiles] at fileImage
  have root := (frame _ (.inl rfl)).1.trans (rebootNames _ (.inl rfl))
  have lock := (frame _ (.inr (.inl rfl))).1.trans (rebootNames _ (.inr (.inl rfl)))
  rw [raw.seed.sameHandle, raw.seed.openedHandle]
  rw [raw.raw.sameLock, raw.raw.appendHandle]
  refine ⟨fileImage.symm, root.trans (reader.directory.symm.trans reader.opening.reads.sameObjects.1),
    lock.trans (reader.lock.symm.trans reader.opening.reads.sameObjects.2.1), ?_, ?_, ?_⟩
  · intro path selectedFile
    have selectedScope : footprint path := .inr (.inr selectedFile)
    exact (frame path selectedScope).1.trans (rebootNames path selectedScope)
  · intro path payload selectedFile ⟨read, bound, bytes⟩
    obtain ⟨nameFrame, byteFrame⟩ := frame path (.inr (.inr selectedFile))
    have before := (rebootNames _ (.inr (.inr selectedFile))).trans bound
    exact ⟨read, nameFrame.trans before, (byteFrame _ before).trans
      ((rebootBytes path selectedFile _ bound).trans (congrArg (fun payload => [payload]) bytes))⟩
  let marked : MarkedOpenSuccessReports input dir history log reads := {
    inventory := crash.reboot
    retry := retry
    layout := layout
    published := state.writer.published
    checkpoint := state.writer.checkpoint
    selected := selected
    vacant := vacant
    opening := reader.opening
    prepared := prepared
    following := following
    accepted := accepted
    ordered := ordered
    wal := wal
    walLayout := walLayout
    walValid := walValid
    spans := spans
    active := active
    keeper := keeper
    kept := kept
    pending := pending
    bounded := bounded
  }
  obtain ⟨next, seeded, cache, _, owner, slot, _, durable, checkpoint, _, target, _, _⟩ :=
    reader.opening.finish.startsNativeReadPrefix reader.opening.chronology reader.opening.markerFound
      prepared following accepted ordered walLayout walValid spans active keeper kept pending bounded
  let position : NativeReadPosition history log :=
    ⟨reader.opening.finish.run reader.opening.chronology, next, next, reads, seeded⟩
  obtain ⟨measured, installed, _, makeCache, _, _, ran⟩ :=
    marked.opensHealthyFromAdmission raw.raw raw.seed raw.checkpoint raw.listing raw.extents raw.seals raw.keeper
      raw.sameLookup raw.flat raw.marked bootstrap assemble constructs raw.allocations
  obtain ⟨handle, start, positionEq, table, sameLock, sameCache, contents, sameGet, sameSet, sameCompare,
    token, reached, pins, sameFiles, sameCensus, cached⟩ :=
    installed.startsAtCheckpointReopen rfl position rfl seeded.frames.1 cache owner slot phase ptrEq
  refine ⟨measured, position, makeCache, handle, start, ?_, positionEq, rfl, rfl, target,
    target ▸ seeded.refines.1.retained.resumed.ready, checkpoint, durable, sameLock,
    sameCache.symm ▸ installed.cacheReferences, sameCache.symm ▸ installed.cacheDirectory,
    contents, sameGet, sameSet, sameCompare, token, pins, sameFiles, sameCensus, cached⟩
  rw [table, reached]
  exact ran

end

end Alvoki.Storage.DiskSession
