import Alvoki.Storage.Disk.NativeCheckpointFinalManifest
import Alvoki.Storage.Disk.NativeCheckpointSourceReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}

local notation "dbDir" => current.current.ready.state.session.directory
local notation "ready" => current.current.ready

variable {view : OpenCloseHeapView heap FileImage}
  {entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

/-- From the one selected final checkpoint image, the healthy aligned
source open acquires the same directory and LOCK, reads the sampled
manifest, runs and WAL, and returns the exact replayed table. Each
local filesystem observation refers to its reached callback heap. -/
theorem NativeCheckpointSourceStop.reopensSampledFinalCheckpoint
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : FinalCheckpointStorageEffects stop inodes runs observe)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    (namesAt : heap → FilePath → Option Nat)
    (entryKeeps : ∀ path, path = (dbDir).path ∨ path = (dbDir).file .lock → namesAt entry path = names path)
    (effects : OpenPhaseCellEffects view.phase get set) :
    let dir := dbDir
    let state := (ready).state
    let pair : DirectoryPublication.Bindings :=
      ⟨(names (dir.file .manifest)).map contents, (names (dir.file .walBoundary)).map contents⟩
    let wal : WalSegmentImage := { state.writer.wal with directory := .settled pair }
    let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
    let retry : LockedFileState FileImage :=
      ⟨wal.checkpointReopenFiles wal.directory none, state.files.owners.set (dir.file .lock) none⟩
    let vacant : TryLockObserves retry.owners dir (.ok true) := fun _ => by simp [retry, LockOwners.set]
    (∀ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history),
      Prepared retry.image layout.target layout.plan →
      ∀ {checkpoint}, ∀ selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
          retry.image.directory.active.manifest checkpoint,
      ∃ (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
          { published with durable := actual } vacant selected names)
        (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
        (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
          phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
        raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧
        raw.callbacks = source.keeperCallbacks ∧
        ∀ path, path = dir.path ∨ path = dir.file .lock → opening.reads.bindings path = namesAt entry path) →
    ∃ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history)
      (checkpoint : Option (PackedTable × UInt64))
      (selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
        retry.image.directory.active.manifest checkpoint)
      (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
        { published with durable := actual } vacant selected names)
      (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
      (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
        phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream)
      (next : NativeReadPosition current.current.history current.current.submissions)
      (returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
        RawMarkedOpenInterpreter.assemble get set ptrEq),
      view.files entry = retry ∧
      source.openTable input entry = .ok returned.handle.table returned.start.reached ∧
      (view.handle raw.seed.afterPending raw.seed.handle).1.inode
        (view.handle raw.seed.afterPending raw.seed.handle).2.1.description =
        state.census.inode state.directorySlot.description ∧
      (view.handle raw.raw.afterFlock raw.raw.lock).1.inode
        (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description = state.census.inode state.owner.description ∧
      (pair.manifest = none → names (dir.file .manifest) = none ∧
        ∃ filename message, opening.reads.reads.stat (dir.file .manifest) =
          .error (.noFileOrDirectory filename 2 message)) ∧
      (∀ bytes, pair.manifest = some bytes → opening.ReadsSample contents (dir.file .manifest) bytes) ∧
      opening.ReadsSample contents (dir.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
      (∀ bytes metadata, pair.manifest = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat, ∀ payload, actual metadata.header.generation index = some payload →
        opening.ReadsSample contents (dir.file (.run metadata.header.generation index)) payload) ∧
      (∀ segment ∈ layout.sealed ++ [layout.keeper],
        opening.ReadsSample contents (dir.file (.walSegment segment.first)) segment.bytes) ∧
      returned.start.current.ready.state.writer.checkpoint = checkpoint ∧
      returned.start.current.ready.reads = (ready).reads ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode current.current.history) =
        .ok returned.start.current.ready.state.writer.installed.table ∧
      InstalledClientReplay current.current.submissions (ready).reads current.current.history
        returned.start.current.ready.state.writer.installed returned.start.current.ready.state.session := by
  intro dir state pair wal actual retry vacant observeReads
  obtain ⟨authority, marker, segments, published, layout, _, walLayout, walValid, keeper, aligned,
    descriptors, offsets, prepared, _, accepted, _, _, _, checkpoint, _, _, selected, _, _, _, _, _⟩ :=
    stop.replaysSampledFinalCheckpoint inodes runs observe storage names chosen contents sampled
  obtain ⟨opening, chronology, raw, sameFiles, sameDirectory, sameKeeper, readsAtEntry⟩ :=
    observeReads published layout prepared selected
  have captures := raw.capturesRebootAuthority rfl namesAt names authority entryKeeps readsAtEntry
  have markerSelected : retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, payload⟩ := marker
    change names (dir.file .walBoundary) = some inode at bound
    change [contents inode] = _ at payload
    change (names (dir.file .walBoundary)).map contents = _
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  have readSegments : ∀ segment ∈ layout.sealed ++ [layout.keeper],
      (names (dir.file (.walSegment segment.first))).map contents = some segment.bytes := by
    intro segment included
    have member : segment ∈ state.writer.wal.segments := by
      rw [descriptors, WalSegmentImage.readDescriptors] at included
      split at included
      · exact (List.mem_filter.mp included).1
      · exact List.mem_append_right _ included
    obtain ⟨inode, bound, payload⟩ := segments segment member
    change names (dir.file (.walSegment segment.first)) = some inode at bound
    change [contents inode] = _ at payload
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  obtain ⟨missing, manifestRead, markerRead, runRead, walReads⟩ :=
    opening.readsSelectedSamples contents rfl rfl markerSelected (fun _ _ _ _ _ _ _ stored => stored) aligned readSegments
  have following := opening.reads.walReads.selectedAfterWatermark offsets descriptors
  obtain ⟨prior, history, pending⟩ := (ready).readPrefix.refines
  have first : layout.target.first = wal.active.first := congrArg WalSegment.first keeper
  obtain ⟨next, returned, opened, selectedAgain, priorReads, replay, ledger⟩ :=
    raw.returnsSelectedFromFixedInterpreter sameFiles sameDirectory sameKeeper prepared following accepted
      prior.retained.resumed.ordered walLayout walValid prior.retained.spans rfl first rfl
      history pending (ready).readPrefix.readsBounded write effects ptrEq
  exact ⟨published, layout, checkpoint, selected, opening, chronology, raw, next, returned,
    raw.raw.entryFiles, opened, captures.1, captures.2, missing, manifestRead, markerRead, runRead, walReads,
    selectedAgain, priorReads, replay, ledger⟩

end Alvoki.Storage.DiskSession
