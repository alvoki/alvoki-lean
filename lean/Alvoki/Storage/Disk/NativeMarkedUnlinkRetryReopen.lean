import Alvoki.Storage.Disk.NativeMarkedFirstUnlinkError
import Alvoki.Storage.Disk.NativeMarkedBarrierRetryReopen

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {seen : NativeMarkedFirstUnlinkError reads keeper} {checkpoint : Option (PackedTable × UInt64)}

namespace NativeMarkedFirstUnlinkError

/-- The checked suffix is strictly increasing. An effective first
unlink therefore removes just its head from the live retry's plan. -/
theorem remainingNames (seen : NativeMarkedFirstUnlinkError reads keeper) :
    seen.reachedFiles.image.later.visible = if seen.effective then seen.rest else seen.first :: seen.rest := by
  have increasing := (List.pairwise_append.mp reads.catalog.ordered).2.1
  rw [seen.order] at increasing
  have distinct := (List.pairwise_cons.mp increasing).1
  have kept : seen.rest.filter (fun first => decide (first ≠ seen.first)) = seen.rest :=
    List.filter_eq_self.mpr fun first member => decide_eq_true (Nat.ne_of_gt (distinct first member))
  cases effect : seen.effective
  · change ((if seen.effective then retry.image.syncDirectory.unlinkLater seen.first
      else retry.image.syncDirectory).later.visible) = _
    rw [effect]
    exact seen.order
  · change ((if seen.effective then retry.image.syncDirectory.unlinkLater seen.first
      else retry.image.syncDirectory).later.visible) = _
    simp only [effect, ite_true, FileImage.unlinkLater, FileImage.syncDirectory, LaterNames.syncDirectory,
      LaterNames.settled, LaterNames.unlink]
    rw [seen.order]
    change (seen.first :: seen.rest).filter (fun first => decide (first ≠ seen.first)) = seen.rest
    simp only [List.filter_cons, ne_self_iff_false, decide_false, Bool.false_eq_true, ite_false]
    exact kept

end NativeMarkedFirstUnlinkError

/-- The former open's reported error path, including the same local
unlock issued after the returned unlink. The starting layout determines
what a later admitted repair may preserve. -/
structure NativeMarkedUnlinkReturn (seen : NativeMarkedFirstUnlinkError reads keeper)
    (seed : NativeMarkedBarrierSeed (inventory, retry) history published checkpoint) where
  original : seed.layout = layout
  chronology : CapturedMarkedReadCensus reads keeper
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  marker : IO.FS.Metadata
  found : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) (admission.reached, admission.held) =
    .ok (some marker) (admission.reached, admission.held)
  unlock : Except IO.Error Unit
  unlocked : admission.unlock admission.owner () (seen.census, seen.reachedFiles) = match unlock with
    | .ok () => .ok () (seen.census, seen.afterUnlock unlock)
    | .error cause => .error cause (seen.census, seen.afterUnlock unlock)
  bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
    EStateM IO.Error CensusOpenState SegmentedSession

namespace NativeMarkedUnlinkReturn

variable {seed : NativeMarkedBarrierSeed (inventory, retry) history published checkpoint}
  (previous : NativeMarkedUnlinkReturn seen seed)

include previous in
theorem prepared : Prepared retry.image layout.target layout.plan :=
  previous.original ▸ seed.prepared

include previous in
theorem following :
    ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1, layout.range.watermark < start :=
  previous.original ▸ seed.following

def run : EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.run previous.chronology previous.bootstrap previous.install

theorem returned :
    previous.run = .error (seen.diagnostic previous.unlock) (seen.census, seen.afterUnlock previous.unlock) :=
  (seen.returns previous.chronology seed.selected previous.prepared previous.following seed.accepted seed.ordered
    previous.flat previous.found previous.unlock previous.unlocked previous.bootstrap previous.install).1

/-- Only the observed drops occur after the return. A failed unlock can
still release the same flock when its last reference is dropped. -/
def afterDrops (drops : List LockReferenceDrop) : CensusOpenState :=
  (seen.census.afterDrops drops, match previous.unlock with
    | .ok () => seen.afterUnlock previous.unlock
    | .error _ => seen.census.dropLockState admission.owner.description drops directory (seen.afterUnlock previous.unlock))

theorem disposes (drops : List LockReferenceDrop) :
    (previous.afterDrops drops).2.image = seen.reachedFiles.image ∧
    (TryLockObserves (previous.afterDrops drops).2.owners directory (.ok true) ↔
      previous.unlock = .ok () ∨ (previous.afterDrops drops).1.references admission.owner.description = []) := by
  cases reported : previous.unlock with
  | ok result =>
    cases result
    simp [afterDrops, reported, NativeMarkedFirstUnlinkError.afterUnlock, LockOwners.set, TryLockObserves]
  | error cause =>
    have held : (seen.afterUnlock (.error cause)).owners.Owns directory admission.owner.description :=
      admission.opened.held
    have live : seen.census.references admission.owner.description ≠ [] :=
      List.ne_nil_of_mem (seen.census.mem_references.mpr ⟨admission.owner, seen.ownerLive, rfl, rfl⟩)
    have disposed := (LockCensusTrace.start held live).drops drops
    have files := congrArg LockedFileState.image disposed.reached.2.2
    simp only [afterDrops, reported, reduceCtorEq, false_or]
    refine ⟨?_, disposed.freshFlockAllowed⟩
    split at files <;> exact files

theorem vacant {drops : List LockReferenceDrop}
    (released : previous.unlock = .ok () ∨ (previous.afterDrops drops).1.references admission.owner.description = []) :
    TryLockObserves (previous.afterDrops drops).2.owners directory (.ok true) :=
  (previous.disposes drops).2.mpr released

theorem valid (drops : List LockReferenceDrop) :
    (previous.afterDrops drops).2.image.Valid layout.target := by
  rw [(previous.disposes drops).1]
  exact (seen.fileEffects previous.prepared).1.valid previous.prepared.pair
    previous.prepared.keeperPrefix previous.prepared.newer

/-- Re-index the known keeper with the exact reached selected image. -/
def retryLayout (drops : List LockReferenceDrop) : CanonicalKeeperLayout (previous.afterDrops drops).2.image history where
  range := layout.range
  decoded := (congrArg DirectoryPublication.Bindings.walRange (previous.valid drops).selected).trans layout.decoded
  through := layout.through
  first := layout.first
  sealed := layout.sealed
  keeper := layout.keeper
  chain := layout.chain
  covers := layout.covers
  tail := layout.tail
  visible := by
    rw [(previous.disposes drops).1, (seen.fileEffects previous.prepared).2.2.2.1]
    exact layout.visible

theorem sameTarget (drops : List LockReferenceDrop) : (previous.retryLayout drops).target = layout.target := by
  have pair := (previous.valid drops).selected
  cases target : layout.target with
  | mk bindings range firstDecoded first firstCovered trimmed trimmedSize =>
    have start : first = layout.keeper.first := (congrArg Target.first target).symm
    have coordinates : range = layout.range := (congrArg Target.range target).symm
    have bytes : trimmed = layout.keeper.bytes := (congrArg Target.trimmed target).symm
    have sameBindings : bindings = (previous.afterDrops drops).2.image.directory.active :=
      (congrArg Target.pair target).symm.trans pair.symm
    subst first range trimmed bindings
    rfl

theorem retryPrepared (drops : List LockReferenceDrop) :
    Prepared (previous.afterDrops drops).2.image (previous.retryLayout drops).target (previous.retryLayout drops).plan := by
  have valid := previous.valid drops
  refine ⟨rfl, ?_, valid.later, rfl, rfl, rfl, (previous.retryLayout drops).visible⟩
  rw [previous.sameTarget drops]
  exact valid.keeper

theorem retrySelected (drops : List LockReferenceDrop) :
    SelectedIntegrityCheckpoint published.durable (previous.afterDrops drops).2.image.directory.active.manifest checkpoint := by
  rw [(previous.valid drops).selected]
  exact seed.selected

theorem retryAccepted (drops : List LockReferenceDrop) :
    published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      (previous.afterDrops drops).2.image.directory.active.manifest := by
  rw [(previous.valid drops).selected]
  exact seed.accepted

theorem remaining (drops : List LockReferenceDrop) :
    (previous.afterDrops drops).2.image.later.visible = if seen.effective then seen.rest else seen.first :: seen.rest := by
  rw [(previous.disposes drops).1]
  exact seen.remainingNames

theorem keepsSealed (drops : List LockReferenceDrop) :
    (previous.afterDrops drops).2.image.kept = retry.image.kept := by
  rw [(previous.disposes drops).1, (seen.fileEffects previous.prepared).2.2.1]

end NativeMarkedUnlinkReturn

/-- The next issued open starts with the previous error's exact files
and complete census after the reported drop events. Local observations
link its held raw reads to the surviving namespace at that return. -/
structure NativeMarkedUnlinkReopenReads {seed : NativeMarkedBarrierSeed (inventory, retry) history published checkpoint}
    (previous : NativeMarkedUnlinkReturn seen seed) (drops : List LockReferenceDrop)
    (released : previous.unlock = .ok () ∨ (previous.afterDrops drops).1.references admission.owner.description = [])
    (nextInput : FilePath) where
  opening : MarkedReadyOpenObservations nextInput directory (previous.afterDrops drops).1 (previous.afterDrops drops).2
    (previous.retryLayout drops) published (previous.vacant released) (previous.retrySelected drops)
  root : opening.admission.root = admission.root
  names : ∀ name object, seen.afterUnlink.child admission.root name = some object →
    opening.admission.view.child opening.admission.root name = some object
  failedName : opening.admission.view.child opening.admission.root (renderWalSegmentName seen.first) =
    seen.afterUnlink.child admission.root (renderWalSegmentName seen.first)
  objects : opening.admission.view.modelObject = admission.view.modelObject
  payload : ∀ inode bytes, seen.afterBytes inode = some bytes → opening.reads.reads.objectBytes inode = some bytes

namespace NativeMarkedUnlinkReopenReads

variable {seed : NativeMarkedBarrierSeed (inventory, retry) history published checkpoint}
  {previous : NativeMarkedUnlinkReturn seen seed} {drops : List LockReferenceDrop}
  {released : previous.unlock = .ok () ∨ (previous.afterDrops drops).1.references admission.owner.description = []}
  {nextInput : FilePath} (opened : NativeMarkedUnlinkReopenReads previous drops released nextInput)

/-- The new no-follow stat and payload open see the same child and
bytes originally selected before the previous unlink call. -/
def ReadsOriginal (path : FilePath) (name : String) (bytes : ByteArray) : Prop :=
  ∃ object, admission.view.child admission.root name = some object ∧ seen.retains name object bytes ∧
    ∃ read : opened.opening.reads.reads.ObservesFile path bytes, read.object = admission.view.modelObject object

private theorem readsOriginal {path : FilePath} {name : String} {object : DeviceInode} {bytes : ByteArray}
    (original : admission.view.child admission.root name = some object)
    (retained : seen.retains name object bytes)
    (calls : RunChunkPathReport opened.opening.reads.reads path name opened.opening.admission.root opened.opening.admission.view) :
    opened.ReadsOriginal path name bytes := by
  have bound := opened.names name object retained.1
  have contents : opened.opening.reads.reads.objectBytes (opened.opening.admission.view.modelObject object) = some bytes := by
    rw [opened.objects]
    exact opened.payload _ _ retained.2
  let read := calls.observesFile bound contents
  have same := (congrArg opened.opening.admission.view.modelObject (calls.statLookup.child_eq bound)).symm.trans
    calls.identifiedStat
  exact ⟨object, original, retained, read, same.symm.trans (congrFun opened.objects object)⟩

theorem readsManifest {bytes : ByteArray} (present : retry.image.directory.active.manifest = some bytes) :
    opened.ReadsOriginal (directory.file .manifest) "MANIFEST" bytes := by
  obtain ⟨object, prior, retained⟩ := seen.retainsManifest present
  have same : (previous.afterDrops drops).2.image.directory.active = retry.image.directory.active :=
    (previous.valid drops).selected
  obtain ⟨⟨file⟩, _⟩ := opened.opening.reads.metadata.manifestFile bytes (same.symm ▸ present)
  exact opened.readsOriginal prior retained file.calls

theorem readsRun {bytes payload : ByteArray} {manifest : IntegrityCheckpoint}
    (present : retry.image.directory.active.manifest = some bytes) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    {index : Nat} (within : index < manifest.header.runCount.toNat)
    (stored : published.durable manifest.header.generation index = some payload) :
    opened.ReadsOriginal (directory.file (.run manifest.header.generation index))
      (renderRunFileName manifest.header.generation index) payload := by
  obtain ⟨object, prior, retained⟩ := seen.retainsRun present decoded within stored
  have same : (previous.afterDrops drops).2.image.directory.active = retry.image.directory.active :=
    (previous.valid drops).selected
  obtain ⟨_, _, _, ⟨calls⟩⟩ := opened.opening.reads.runs bytes manifest (same.symm ▸ present) decoded index within payload stored
  exact opened.readsOriginal prior retained calls

theorem readsMarker {bytes : ByteArray} (present : retry.image.directory.active.walBoundary = some bytes) :
    opened.ReadsOriginal (directory.file .walBoundary) "WAL.commit" bytes := by
  obtain ⟨object, prior, retained⟩ := seen.retainsMarker present
  have same : (previous.afterDrops drops).2.image.directory.active = retry.image.directory.active :=
    (previous.valid drops).selected
  obtain ⟨file, _⟩ := opened.opening.reads.metadata.markerFile bytes (same.symm ▸ present)
  exact opened.readsOriginal prior retained file.calls

theorem readsKeeper :
    opened.ReadsOriginal (directory.file (.walSegment layout.keeper.first)) (renderWalSegmentName layout.keeper.first)
      (layout.keeper.bytes ++ layout.tail) := by
  obtain ⟨object, prior, retained⟩ := seen.retainsWal previous.prepared layout.keeper (by simp)
  exact opened.readsOriginal prior (by simpa only [ite_true] using retained) opened.opening.reads.wal.keeper.calls

theorem readsSeal (segment : WalSegment) (selected : segment ∈ layout.sealed) :
    opened.ReadsOriginal (directory.file (.walSegment segment.first)) (renderWalSegmentName segment.first) segment.bytes := by
  obtain ⟨object, prior, retained⟩ :=
    seen.retainsWal previous.prepared segment (List.mem_append_left _ selected)
  have sorted := (List.pairwise_append.mp (List.pairwise_append.mp reads.catalog.ordered).1).2.1
  rw [List.map_append, List.map_singleton] at sorted
  have earlier := (List.pairwise_append.mp sorted).2.2 segment.first (List.mem_map_of_mem selected)
    layout.keeper.first (List.mem_singleton_self _)
  simp only [ite_eq_right (Nat.ne_of_lt earlier)] at retained
  exact opened.readsOriginal prior retained (opened.opening.reads.wal.sealedFile segment selected).calls


/-- The next checked namespace sees the original failed target at its
same child, or sees it absent when that unlink took effect. -/
theorem observesFailedTarget :
    opened.opening.admission.view.child opened.opening.admission.root (renderWalSegmentName seen.first) =
      (if seen.effective then none else some seen.lookup.child) :=
  opened.failedName.trans seen.unlinkBinding

/-- The newly checked directory scan selects the residual suffix on
the original marker. In particular, a reported deletion removes the
first name from the new dispatcher's input. -/
theorem checkedRemaining :
    ∃ markerBytes count extents required,
      (previous.afterDrops drops).2.image.directory.active.walBoundary = some markerBytes ∧
      WAL.Boundary.decode markerBytes = .ok count ∧
      readWalSegmentExtentsWith (m := Except IO.Error) directory
        (fun path => .ok (opened.opening.reads.catalog.inventory.reports.lstat path))
        (opened.opening.reads.catalog.entries.toList.map (·.fileName)) = .ok extents ∧
      selectWalExtentsThrough extents layout.range.watermark (count.toNat / WAL.frameSize) =
        some (required, if seen.effective then seen.rest else seen.first :: seen.rest) ∧
      required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first := by
  obtain ⟨_, _, marker, count, named, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting (previous.retryLayout drops).decoded
  obtain ⟨extents, required, scanned, selected, offsets, _⟩ := opened.opening.reads.catalog.scanSelected
    previous.following ((previous.retryPrepared drops).newer _ List.mem_cons_self) absolute
  rw [previous.remaining drops] at selected
  exact ⟨marker, count, extents, required, named, decoded, scanned, selected, offsets⟩

/-- A healthy next open executes the actual bounded repair on the
remaining names, reading the exact preserved selected files from the
reached census. The returned table explains the previous read ledger. -/
theorem reopens
    (pending : PendingClientReplay log recorded history) (bounded : ∀ read ∈ recorded, read.BoundedBy history.length) :
    previous.run = .error (seen.diagnostic previous.unlock) (seen.census, seen.afterUnlock previous.unlock) ∧
    (previous.retryLayout drops).boundedPlan.newer = (if seen.effective then seen.rest else seen.first :: seen.rest) ∧
    ∃ (state : NativeReadyState) (repairs : Nat),
      NativeReadyReadPrefix (opened.opening.finish.run opened.opening.chronology) state history log recorded state ∧
      opened.opening.finish.run opened.opening.chronology = .ok state.session (state.census, state.files) ∧
      state.files.image.Ready layout.target ∧ state.writer.checkpoint = checkpoint ∧
      state.writer.published.durable = published.durable ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok state.writer.installed.table ∧
      InstalledClientReplay log recorded history state.writer.installed state.session ∧
      countBoundedRepairCallbacks directory (previous.retryLayout drops).boundedPlan
        opened.opening.reads.wal.keeper.calls.metadata.byteSize.toNat = .ok repairs ∧
      2 + repairs ≤ 2 + (if seen.effective then seen.rest.length else seen.rest.length + 1) + 6 := by
  have sameTarget := previous.sameTarget drops
  have prepared := previous.retryPrepared drops
  have accepted := previous.retryAccepted drops
  have following := previous.following
  obtain ⟨state, started, _, _, _, _, _, durable, sameCheckpoint, path, target, _, _, _, _, _⟩ :=
    opened.opening.finish.startsNativeReadPrefix opened.opening.chronology opened.opening.markerFound
      prepared following accepted seed.ordered seed.readLayout seed.valid seed.spans
      (by rw [sameTarget, ← previous.original]; exact seed.active)
      (by rw [sameTarget, ← previous.original]; exact seed.keeper)
      ((previous.keepsSealed drops).trans seed.kept) pending bounded
  obtain ⟨session, final, repairs, returned, _, installed, _, _, count, limit⟩ :=
    opened.opening.installsWithWork prepared following accepted seed.ordered
  obtain ⟨table, chosen, _, installedSession, installedFiles, result, _, _, phase, _, _, _, _, _, _, _, _, _,
    _, selected, replay, _, _, _, _, _, _, _, _⟩ := installed
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj result
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (started.frames.1.symm.trans returned)
  have loaded := Phase.ready.inj (started.refines.1.phase.symm.trans (sameSession.symm ▸ phase))
  have sameTable : state.writer.installed.table = table.table := congrArg Installed.table loaded
  have sameSelected := selected.uniqueResult (previous.retrySelected drops)
  rw [previous.remaining drops] at limit
  have length : (if seen.effective then seen.rest else seen.first :: seen.rest).length =
      (if seen.effective then seen.rest.length else seen.rest.length + 1) := by
    split <;> simp_all only [Bool.false_eq_true, ite_false, ite_true, List.length_cons]
  rw [length] at limit
  refine ⟨previous.returned, previous.remaining drops, state, repairs, started, started.frames.1, ?_,
    sameCheckpoint, durable, ?_, started.guardedReplay, count, ?_⟩
  · exact (target.trans sameTarget) ▸ started.refines.1.retained.resumed.ready
  · rw [sameTable, ← sameSelected]
    exact replay
  · omega

end NativeMarkedUnlinkReopenReads

end Alvoki.Storage.DiskSession
