import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawCheckpointDigestError

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- Every earlier run supplies its selected bytes and closes its
temporary descriptor. The next no-follow stat reaches the selected child. -/
structure RawSelectedCheckpointRunStat
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  index : Nat
  reads : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls (fun _ => index)
  within : index < reads.manifest.header.runCount.toNat
  stamp : RunIntegrity
  stamped : reads.manifest.runs[index]? = some stamp
  child : RunChildLookup admission.root (renderRunFileName reads.manifest.header.generation index) admission.view
  metadata : IO.FS.Metadata
  regular : metadata.type = .file
  stat : reads.reads.stat (directory.file (.run reads.manifest.header.generation index)) =
    .ok (metadata, admission.view.modelObject child.child)
  statRaw : let path := directory.file (.run reads.manifest.header.generation index)
    calls.lookup path (reads.atRun index) = .ok ((reads.reads.stat path).map Prod.fst) (reads.atRun index)
namespace RawSelectedCheckpointRunStat

/-- The stat is read-only. The selected run's size is measured at the
heap reached by the earlier reads and releases. -/
theorem measures (seen : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) :
    fileCalls.runSize (directory.file (.run seen.reads.manifest.header.generation seen.index))
      (seen.reads.atRun seen.index) = .ok seen.metadata.byteSize.toNat (seen.reads.atRun seen.index) := by
  have stat := seen.statRaw
  change calls.lookup (directory.file (.run seen.reads.manifest.header.generation seen.index))
    (seen.reads.atRun seen.index) =
      .ok ((seen.reads.reads.stat (directory.file (.run seen.reads.manifest.header.generation seen.index))).map Prod.fst)
        (seen.reads.atRun seen.index) at stat
  rw [seen.stat] at stat
  simp [MarkedTemporaryReadCalls.runSize, seen.reads.sameLookup, stat, seen.regular, liftExcept, Except.map,
    show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem readsEarlier (seen : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) :
    readIntegrityRunBytesSized directory
      { seen.reads.manifest with header := { seen.reads.manifest.header with runCount := seen.index.toUInt64 } }
      fileCalls.runSize fileCalls.runPrefix (seen.reads.atRun 0) =
      .ok ((List.range seen.index).map seen.reads.payload) (seen.reads.atRun seen.index) := by
  have fits := Nat.lt_trans seen.within seen.reads.manifest.header.runCount.toNat_lt_size
  exact seen.reads.readsPrefix rfl rfl (UInt64.toNat_ofNat_of_lt' fits)

end RawSelectedCheckpointRunStat

/-- A bad extent rejects the selected run before opening its payload. -/
structure RawCheckpointExtentRead
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap)
    extends RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls where
  wrong : metadata.byteSize.toNat ≠ stamp.byteCount.toNat

namespace RawCheckpointExtentRead

theorem measures (seen : RawCheckpointExtentRead (admitted := admitted) seed fileCalls) :
    fileCalls.runSize (directory.file (.run seen.reads.manifest.header.generation seen.index))
      (seen.reads.atRun seen.index) = .ok seen.metadata.byteSize.toNat (seen.reads.atRun seen.index) :=
  seen.toRawSelectedCheckpointRunStat.measures

/-- The exact production reader returns before reading the bad run's
payload, visiting a later run or loading the checkpoint table. -/
theorem rejects (seen : RawCheckpointExtentRead (admitted := admitted) seed fileCalls) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending =
        .error (IO.userError checkpointIntegrityMismatch) (seen.reads.atRun seen.index) ∧
    MarkedReadCacheFrame seed seed.afterPending (seen.reads.atRun seen.index) ∧
    (view.descriptors (seen.reads.atRun seen.index)).inode = admission.reached.inode := by
  refine ⟨?_, seen.reads.frames (Nat.le_refl _)⟩
  exact readIntegrityCheckpointSized_rejectsExtent directory _ _ _ seen.reads.readsManifest seen.reads.decoded
    seen.within seen.stamped seen.toRawSelectedCheckpointRunStat.readsEarlier seen.measures (fun accepted => seen.wrong accepted.1)

end RawCheckpointExtentRead

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- The actual held worker stops after the wrong stat result and the
observed local cleanup returns the selected diagnostic to the caller. -/
noncomputable def RawCheckpointExtentRead.finalizedAttempt
    (seen : RawCheckpointExtentRead (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed (seen.reads.atRun seen.index))
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  seen.reads.finalizedAttempt seen.rejects.1 seen.rejects.2.1 seen.rejects.2.2 disposal
    directoryCalls callbacks remove write rename bootstrap install finalized

end

end Alvoki.Storage.DiskSession
