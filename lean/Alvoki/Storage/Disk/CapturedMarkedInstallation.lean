import Alvoki.Storage.Disk.CapturedLongKeeperInstallation
import Alvoki.Storage.Disk.CapturedPrunedAlignedInstallation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

/-- Each successful marked repair has the same admitted read chronology
and session allocator. An aligned keeper can retain its inode with or
without pruning. A longer keeper uses replacement after its suffix pass. -/
inductive CapturedKeeperFinish (calls : CapturedAlignedCallbacks admission)
    (reads : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  | aligned (finish : CapturedAlignedFinish calls reads vacant selected)
  | prunedAligned (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
  | longer (finish : CapturedLongKeeperFinish calls reads vacant selected)

namespace CapturedKeeperFinish

variable {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

def reader : CapturedKeeperFinish calls reads vacant selected → CapturedKeeperOpenReports reads
  | .aligned finish => finish.readCustody
  | .prunedAligned finish => finish.reader
  | .longer finish => finish.reader

noncomputable def run (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession := by
  cases finish with
  | aligned finish => exact finish.runFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
  | prunedAligned finish => exact finish.runFromCensus chronology
  | longer finish => exact finish.runFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease

/-- The marked worker consumed by the successful native installer. Its
successful result returns the repaired census and file state before the
phase and session references are allocated. -/
noncomputable def markedWorker (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader) :
    DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened := by
  cases finish with
  | aligned finish => exact finish.recoverFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
  | prunedAligned finish => exact finish.recoverFromCensus chronology
  | longer finish => exact finish.recoverFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease

theorem run_eq_markedWorker (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader) :
    finish.run chronology = calls.runWithMarked (finish.markedWorker chronology) := by
  cases finish <;> rfl

theorem reachesInstaller (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    {session : SegmentedSession} {final : CensusOpenState}
    (returned : finish.run chronology = .ok session final) :
    ∃ opened, finish.markedWorker chronology directory admission.cache (admission.reached, admission.held) =
      .ok opened final ∧
      session = ⟨directory, admission.owner.description, .ready opened.installed, calls.nextRef, calls.nextRef + 1⟩ :=
  calls.runWithMarked_reachedRepair _ marker ((finish.run_eq_markedWorker chronology).symm ▸ returned)

noncomputable def census : CapturedKeeperFinish calls reads vacant selected → DescriptorInventory
  | .aligned finish => finish.census
  | .prunedAligned finish => finish.census
  | .longer finish => finish.census

theorem installsFromCensus (finish : CapturedKeeperFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ session final, finish.run chronology = .ok session (finish.census, final) ∧
      final.image.directory.active = retry.image.directory.active ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      CachedRetryInstalled (before := retry) reads.walReads admission.reached admission.owner reads.bindings
        published calls.liveRefs (.ok session final) := by
  cases finish with
  | aligned finish =>
    exact finish.installsFromCensus chronology.manifest chronology.runs chronology.marker chronology.beforeListing
      chronology.seals chronology.offsets chronology.retained marker prepared.keeperPrefix prepared.newer
      following accepted ordered
  | prunedAligned finish =>
    obtain ⟨session, returned, pair, _, owner, directory, _, installed⟩ :=
      finish.installsFromCensus chronology marker prepared.keeperPrefix prepared.newer following accepted ordered
    exact ⟨session, finish.settled, returned, pair, owner, directory, installed⟩
  | longer finish =>
    obtain ⟨session, returned, pair, owner, directory, installed⟩ :=
      finish.installsFromCensus chronology.manifest chronology.runs chronology.marker chronology.beforeListing
        chronology.seals chronology.offsets chronology.retained marker prepared.keeperPrefix prepared.newer
        following accepted ordered
    exact ⟨session, finish.settled, returned, pair, owner, directory, installed⟩

end CapturedKeeperFinish

end Alvoki.Storage.DiskSession
