import Alvoki.Storage.Disk.Proofs.Native.Open.NativeContendedOpen
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {state : NativeReadyState} {input : FilePath}

/-- The raw contender opens the checked canonical lock and tries flock
on that exact handle. The old writer's file state remains held. This
report stops at the returned flock before the temporary handle drops. -/
structure RawContendedOpen (report : NativeContendedOpen state input)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap) (entry : heap) where
  lock : IO.FS.Handle
  afterAppend : heap
  reached : heap
  stat : FilePath → EStateM IO.Error heap (Except IO.Error (IO.FS.Metadata × DeviceInode))
  lookup : ∀ path, calls.lookup path = (do
    let result ← stat path
    pure (result.map Prod.fst))
  entryFiles : view.files entry = state.files
  entryCensus : view.descriptors entry = state.census
  resolved : calls.realPath input entry = .ok state.session.directory.path entry
  flatAbsent : stat (state.session.directory.file .wal) entry =
    .ok (.error (.noFileOrDirectory report.flatName 2 report.flatMessage)) entry
  probed : stat (state.session.directory.file .lock) entry = .ok (.ok (report.metadata, report.statLookup.child)) entry
  appended : calls.openAppend (state.session.directory.file .lock) entry = .ok lock afterAppend
  appendHandle : view.handle afterAppend lock = (state.census.insert report.slot report.free, report.slot, 0)
  appendCensus : view.descriptors afterAppend = (view.handle afterAppend lock).1
  appendFiles : view.files afterAppend = view.files entry
  flockFalse : calls.flock lock afterAppend = .ok false reached
  sameLock : view.handle reached lock = view.handle afterAppend lock
  flockCensus : view.descriptors reached = view.descriptors afterAppend
  flockFiles : view.files reached = view.files afterAppend

namespace RawContendedOpen

variable {report : NativeContendedOpen state input} {view : OpenCloseHeapView heap FileImage}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}

/-- The ordinary contention return follows the guarded append and
flock, prior to cache initialization or recovery. The reached contender
description is distinct and points to the original writer's lock inode. -/
theorem returns
    (seen : RawContendedOpen report view calls entry) (valid : state.Valid)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    let census := state.census.insert report.slot report.free
    calls.runOpen input init makeCache recover entry = .error report.diagnostic seen.reached ∧
    view.handle seen.reached seen.lock = (census, report.slot, 0) ∧
    view.descriptors seen.reached = census ∧ view.files seen.reached = state.files ∧
    (view.descriptors seen.reached).slots = report.slot :: (view.descriptors entry).slots ∧
    (view.handle seen.reached seen.lock).2.1.description ≠ state.session.descriptor ∧
    (view.descriptors seen.reached).inode (view.handle seen.reached seen.lock).2.1.description =
      (view.descriptors seen.reached).inode state.owner.description ∧
    report.statLookup.child = report.appendLookup.child ∧
    report.view.modelObject report.root = (view.descriptors seen.reached).inode state.directorySlot.description ∧
    state.owner ∈ (view.descriptors seen.reached).slots ∧ state.directorySlot ∈ (view.descriptors seen.reached).slots ∧
    (view.files seen.reached).owners.Owns state.session.directory state.session.descriptor := by
  intro census
  have flat : optionalMetadataWith (calls.lookup (state.session.directory.file .wal)) entry = .ok none entry := by
    simp [seen.lookup, optionalMetadataWith, Bind.bind, EStateM.bind, seen.flatAbsent, Pure.pure, EStateM.pure, Except.map]
  have guarded : optionalMetadataWith (calls.lookup (state.session.directory.file .lock)) entry =
      .ok (some report.metadata) entry := by
    simp [seen.lookup, optionalMetadataWith, Bind.bind, EStateM.bind, seen.probed, Pure.pure, EStateM.pure, Except.map]
  have returned : calls.runOpen input init makeCache recover entry = .error report.diagnostic seen.reached := by
    unfold RawOpenAdmissionCallbacks.runOpen
    rw [DiskTable.withOpenAdmission_lockOpen _ _ _ _ seen.resolved flat guarded
      (fun _ same => Option.some.inj same ▸ report.privateLock), seen.appended]
    simp [openWithLock, Bind.bind, EStateM.bind, seen.flockFalse, NativeContendedOpen.diagnostic,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  obtain ⟨distinct, child, inode, root, owner, cached, held⟩ := report.keepsAuthority valid
  have handle := seen.sameLock.trans seen.appendHandle
  have descriptors : view.descriptors seen.reached = census :=
    seen.flockCensus.trans (seen.appendCensus.trans (congrArg Prod.fst seen.appendHandle))
  have files := seen.flockFiles.trans (seen.appendFiles.trans seen.entryFiles)
  refine ⟨returned, handle, descriptors, files, ?_, ?_, ?_, child, ?_, descriptors.symm ▸ owner,
    descriptors.symm ▸ cached, files.symm ▸ held⟩
  · rw [descriptors, seen.entryCensus]
    rfl
  · rw [handle]
    exact distinct
  · rw [descriptors, handle]
    exact inode
  · rw [descriptors]
    exact root

end RawContendedOpen

end Alvoki.Storage.DiskSession
