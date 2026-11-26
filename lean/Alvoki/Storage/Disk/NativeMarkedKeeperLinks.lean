import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

/-- A name in the framed scope that aliases the inode at the later heap
already named it at the original heap. -/
theorem CheckpointSurvivingFiles.Frames.privateBindingOn
    {scope : FilePath → Prop} {before after : CheckpointSurvivingFiles} {canonical : FilePath} {inode : Nat}
    (frame : before.Frames scope after)
    (privateAtEntry : ∀ path, before.names path = some inode → path = canonical) :
    ∀ path, scope path → after.names path = some inode → path = canonical :=
  fun path selected bound => privateAtEntry path (((frame path selected).1).symm.trans bound)

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}

section RawGuard

variable {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}
  {calls : RawOpenAdmissionCallbacks heap} {phaseIdentity : IO.Ref (Phase Installed) → Nat}
  {tokenIdentity : IO.Ref Unit → Nat} {stream : Type}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The actual selected extent probe checked this keeper's one-link
metadata at the listing's reached heap. The link census counts precisely
the live names of the inode identified by the matching keeper read. -/
theorem RawHealthyMarkedOpenEffects.keeperPrivateBinding
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    {names : heap → FilePath → Option Nat}
    (links : RunOpenLinkCensus (path := directory.file (.walSegment layout.keeper.first))
      (before := raw.listing.reached) raw.fileCalls.stat (names raw.listing.reached) opening.reads.wal.keeper.observesFile.object) :
    ∀ path, names raw.listing.reached path = some opening.reads.wal.keeper.observesFile.object →
      path = directory.file (.walSegment layout.keeper.first) := by
  let reads := opening.reads
  have catalog := (reads.catalog.present layout.keeper.first).mpr (by simp)
  have checked := (CheckedDirectoryReadReport.scan_complete directory.path reads.listing.eof reads.listing.closed
    reads.listing.complete).1
  have listing := Except.ok.inj (reads.catalog.listed.symm.trans (reads.listed.trans checked))
  have listed : renderWalSegmentName layout.keeper.first ∈ (reads.listing.scan.entries directory.path).toList.map (·.fileName) := by
    rw [← listing, reads.catalog.names]
    exact catalog
  have keeperStat := raw.extents.stat (renderWalSegmentName layout.keeper.first) listed
    layout.keeper.first (parseWalSegmentName_render layout.keeper.first)
  change raw.fileCalls.stat (directory.file (.walSegment layout.keeper.first)) raw.listing.reached =
    .ok (reads.catalog.inventory.reports.lstat (directory.file (.walSegment layout.keeper.first))) raw.listing.reached at keeperStat
  rw [reads.stat, reads.wal.keeper.calls.stat] at keeperStat
  exact links.privateBinding (.inr ⟨_, keeperStat, reads.wal.keeper.calls.regular, reads.wal.keeper.oneLink⟩)

end RawGuard

end Alvoki.Storage.DiskSession
