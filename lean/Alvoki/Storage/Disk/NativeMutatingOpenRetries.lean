import Alvoki.Storage.Disk.Checkpoint.BarrierRetryObservations
import Alvoki.Storage.Disk.NativeRawUncertainWrite
import Alvoki.Storage.Disk.NativeMarkedOpenInterpreter
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.WalSegmentRepairEffects

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {start : heap}

/-- A bounded repair error is the return of the fixed marked worker at
the cache that read that exact checkpoint and selected WAL. -/
theorem MarkedWalExtentReports.workerReturnsFailedRepair
    {entry : heap} {input : FilePath} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout (view.files entry).image history} {published : CheckpointPublication.Image}
    {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
    {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    {raw : RawOpenAdmissionReport admission view source.calls entry}
    {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
    {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
    {chronology : CapturedMarkedReadCensus reads keeper} {checkpoint : Option (PackedTable × UInt64)}
    {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
    {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
    (extents : MarkedWalExtentReports prepared listing)
    {beforeKeeper afterKeeper failedHeap : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef (pushPending path handle))
      (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    {cause : IO.Error}
    (repair : let sync := source.keeperCallbacks.withFileReads source.fileCalls
      finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
        source.remove (source.stage.stage seed.pendingRef sync.modifyPending)
        (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) source.rename afterKeeper =
      .error cause failedHeap) :
    ∀ cache, source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock cache seed.afterPending =
      .error cause failedHeap := by
  intro cache
  obtain ⟨_, returned, _⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered
    flat marked _ keeperRead source.remove _ _ source.rename repair (source.bootstrap directory cache)
  unfold RawMarkedOpenInterpreter.worker recoverHealthyMarkedWithRefs
  rw [← sameStat]
  simp only [Bind.bind, EStateM.bind, returned]

/-- Identify a reported failed worker and its finalizers with one fixed
opener. The worker is applied to the cache from this admission. -/
theorem RawFinalizedOpenAttempt.returnsFixedInterpreter
    {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    {input : FilePath} {entry : heap} {workerImage : FileImage}
    (failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry workerImage)
    (sameWorker : failed.recover = source.worker failed.seed.directoryRef failed.seed.activeRef failed.seed.pendingRef)
    (sameDisposal : source.dispose = failed.disposed.dispose)
    (returned : failed.recover directory failed.admitted.lock
      (RawMarkedOpenInterpreter.makeCache directory failed.seed.directoryRef failed.seed.activeRef failed.seed.pendingRef)
      failed.seed.afterPending = .error failed.cause failed.beforeCleanup) :
    source.openTable input entry = .error failed.diagnostic failed.reached := by
  apply failed.disposed.returnsMarkedInterpreter source sameDisposal _ failed.finalized
  rw [← sameWorker]
  exact returned

/-- A scoped frame over singleton live observations carries a named
payload without constraining absent paths or unrelated inode contents. -/
theorem CheckpointSurvivingFiles.Frames.visiblePayload {before after : heap} {scope : FilePath → Prop}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    (frame : (⟨names before, fun inode => [bytes before inode]⟩ : CheckpointSurvivingFiles).Frames scope
      ⟨names after, fun inode => [bytes after inode]⟩) {path : FilePath} (selected : scope path) :
    (names after path).map (bytes after) = (names before path).map (bytes before) := by
  obtain ⟨named, contents⟩ := frame path selected
  change names after path = names before path at named
  rw [named]
  cases found : names before path with
  | none => rfl
  | some inode =>
    have same : [bytes after inode] = [bytes before inode] := contents inode found
    exact congrArg some (List.cons.inj same).1

/-- The live keeper is the file currently bound at the selected path.
Its previous binding can still be a crash alternative. -/
def RawOpenRetryTrace.KeeperAt (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (target : Target) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (atHeap : heap) : Prop :=
  (view.files atHeap).image.keeper.active = (names atHeap (directory.file (.walSegment target.first))).map (bytes atHeap)

/-- The modeled suffix and the live canonical bindings agree at the
same retry heap. The selected target supplies the marker cutoff. -/
def RawOpenRetryTrace.LaterWalAt (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (target : Target) (names : heap → FilePath → Option Nat) (atHeap : heap) : Prop :=
  ∀ start, start ∈ (view.files atHeap).image.later.visible ↔
    target.range.through < start ∧ ∃ inode, names atHeap (directory.file (.walSegment start)) = some inode

theorem RawOpenRetryTrace.LaterWalAt.framePresence {target : Target} {names : heap → FilePath → Option Nat}
    {before after : heap} (initial : LaterWalAt view directory target names before)
    (image : (view.files after).image.later.visible = (view.files before).image.later.visible)
    (present : ∀ start, target.range.through < start →
      (names after (directory.file (.walSegment start))).isSome =
        (names before (directory.file (.walSegment start))).isSome) :
    LaterWalAt view directory target names after := by
  intro start
  rw [image, initial start]
  by_cases later : target.range.through < start
  · simp only [← Option.isSome_iff_exists, present start later]
  · simp only [later, false_and]

theorem RawOpenRetryTrace.LaterWalAt.frame {target : Target} {names : heap → FilePath → Option Nat}
    {before after : heap} (initial : LaterWalAt view directory target names before)
    (image : (view.files after).image.later.visible = (view.files before).image.later.visible)
    (binds : ∀ start, target.range.through < start →
      names after (directory.file (.walSegment start)) = names before (directory.file (.walSegment start))) :
    LaterWalAt view directory target names after :=
  initial.framePresence image (fun start later => congrArg Option.isSome (binds start later))

/-- An unlink's realized effect removes one address from both
representations. Other canonical names beyond the marker are framed. -/
theorem RawOpenRetryTrace.LaterWalAt.unlinked {target : Target} {names : heap → FilePath → Option Nat}
    {before after : heap} {ordinal : Nat} (initial : LaterWalAt view directory target names before)
    (image : (view.files after).image.later.visible = ((view.files before).image.unlinkLater ordinal).later.visible)
    (absent : names after (directory.file (.walSegment ordinal)) = none)
    (binds : ∀ start, target.range.through < start → start ≠ ordinal →
      names after (directory.file (.walSegment start)) = names before (directory.file (.walSegment start))) :
    LaterWalAt view directory target names after := by
  intro start
  rw [image]
  change start ∈ ((view.files before).image.later.visible.filter fun later => decide (later ≠ ordinal)) ↔ _
  rw [List.mem_filter, decide_eq_true_eq, initial start]
  by_cases same : start = ordinal
  · subst start
    simp [absent]
  · by_cases later : target.range.through < start
    · rw [binds start later same]
      exact ⟨And.left, fun bound => ⟨bound, same⟩⟩
    · simp only [later, false_and]

/-- Carry suffix agreement across the actual completed unlink prefix.
The local effect is stated at each reached remove, with the result
accepted by the production guard. -/
theorem RawOpenRetryTrace.LaterWalAt.afterAcceptedUnlinks {target : Target}
    {names : heap → FilePath → Option Nat} {first last : heap}
    (initial : LaterWalAt view directory target names first) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (view.files after).image.later.visible = ((view.files before).image.unlinkLater ordinal).later.visible ∧
      names after (directory.file (.walSegment ordinal)) = none ∧
      ∀ start, target.range.through < start → start ≠ ordinal →
        names after (directory.file (.walSegment start)) = names before (directory.file (.walSegment start)))
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    LaterWalAt view directory target names last := by
  exact foldReturnedWalUnlinks directory plan remove write sync rename
    (fun (_ : Unit) atHeap => LaterWalAt view directory target names atHeap) (fun _ _ => ())
    (initial := ()) initial (fun member called accepted earlier => by
      obtain ⟨image, absent, bindings⟩ := unlink member called accepted
      exact earlier.unlinked image absent bindings) returned

/-- The actual finalized read-only attempts keep their file image. A
scoped physical frame on later names carries the matching bindings. -/
theorem RawFinalizedOpenAttempts.keepsLaterWal {target : Target} {names : heap → FilePath → Option Nat}
    {returns : List (FilePath × IO.Error)} {reached : heap}
    (block : RawFinalizedOpenAttempts view directory calls init release start returns reached)
    (binds : ∀ offset, target.range.through < offset →
      names reached (directory.file (.walSegment offset)) = names start (directory.file (.walSegment offset)))
    (initial : RawOpenRetryTrace.LaterWalAt view directory target names start) :
    RawOpenRetryTrace.LaterWalAt view directory target names reached :=
  initial.frame (congrArg (fun image => image.later.visible) block.preserves.2) binds

/-- Join the actual scan's later-name characterization to the
carried file image using its canonical child bindings. This gives both
directions needed to justify a completed prune or an empty suffix. -/
theorem RawOpenRetryTrace.LaterWalAt.scanNames {target : Target} {names : heap → FilePath → Option Nat}
    {entry : heap} (initial : LaterWalAt view directory target names entry)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) {newer : List Nat}
    (listed : ∀ start, start ∈ newer ↔ target.range.through < start ∧
      ∃ object, namespaceView.child root (renderWalSegmentName start) = some object)
    (child : ∀ start, target.range.through < start →
      (namespaceView.child root (renderWalSegmentName start)).map namespaceView.modelObject =
        names entry (directory.file (.walSegment start))) :
    ∀ start, start ∈ newer ↔ start ∈ (view.files entry).image.later.visible := by
  intro start
  rw [listed start, initial start]
  constructor
  · rintro ⟨later, object, bound⟩
    exact ⟨later, namespaceView.modelObject object, by simpa only [bound, Option.map_some] using (child start later).symm⟩
  · rintro ⟨later, inode, bound⟩
    obtain ⟨object, named, _⟩ := Option.map_eq_some_iff.mp ((child start later).trans bound)
    exact ⟨later, object, named⟩

/-- The marker joins the immutable write footprint once a retry has
selected a target. Repair gives the live keeper its own relation. -/
def NativeReadyState.selectedRetryPath (state : NativeReadyState) (path : FilePath) : Prop :=
  path = state.session.directory.file .walBoundary ∨ state.writeFramePath path

/-- Facts established when entering a selected retry epoch. The actual
open attempts and their local effects are indexed separately. -/
structure RawOpenRetryTrace.SelectedEntry (view : OpenCloseHeapView heap FileImage)
    (state : NativeReadyState) (target : Target) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (first : heap) : Prop where
  valid : (view.files first).image.Valid target
  kept : (view.files first).image.kept = state.writer.files.kept
  manifest : target.pair.manifest = state.writer.target.pair.manifest
  protectedFiles : NativeReadyProtectedStorage state ⟨names first, fun inode => [visible first inode]⟩
  keeper : KeeperAt view state.session.directory target names visible first
  marker : (names first (state.session.directory.file .walBoundary)).map (visible first) = target.pair.walBoundary

/-- A read-only block carries the named keeper using the scoped live
file frame, leaving repairs to establish their own local effect. -/
theorem RawFinalizedOpenAttempts.keepsVisibleKeeper {target : Target}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    {returns : List (FilePath × IO.Error)} {reached : heap}
    (block : RawFinalizedOpenAttempts view directory calls init release start returns reached)
    (frame : (⟨names start, fun inode => [bytes start inode]⟩ : CheckpointSurvivingFiles).Frames
      (· = directory.file (.walSegment target.first)) ⟨names reached, fun inode => [bytes reached inode]⟩)
    (keeper : RawOpenRetryTrace.KeeperAt view directory target names bytes start) :
    RawOpenRetryTrace.KeeperAt view directory target names bytes reached := by
  unfold RawOpenRetryTrace.KeeperAt at keeper ⊢
  rw [block.preserves.2, keeper]
  exact (frame.visiblePayload rfl).symm

/-- The proof of selected-file preservation follows the fixed opener's
failed calls. A read-only block keeps its image. Repair may change the
keeper and later names while framing protected paths. -/
inductive RawOpenRetryTrace.SelectedEffects (view : OpenCloseHeapView heap FileImage)
    {stream : Type} (source : RawMarkedOpenInterpreter heap stream) (start : heap) (target : Target)
    (files : heap → CheckpointSurvivingFiles) (protectedPaths : FilePath → Prop) (keep : heap → Prop) :
    ∀ {returns : List (FilePath × IO.Error)} {reached : heap}, source.FailedCalls start returns reached → Prop where
  | empty : SelectedEffects view source start target files protectedPaths keep .empty
  | append {earlier more : List (FilePath × IO.Error)} {entry reached : heap}
      {prior : source.FailedCalls start earlier entry} {calls : source.FailedCalls entry more reached}
      (before : SelectedEffects view source start target files protectedPaths keep prior)
      (image : (view.files reached).image = (view.files entry).image ∨
        EffectTrace target (view.files entry).image (view.files reached).image)
      (frame : (files entry).Frames protectedPaths (files reached))
      (carries : keep entry → keep reached) :
      SelectedEffects view source start target files protectedPaths keep (prior.append calls)

namespace RawOpenRetryTrace.SelectedEffects

variable {stream : Type} {source : RawMarkedOpenInterpreter heap stream} {target : Target}
  {files : heap → CheckpointSurvivingFiles} {protectedPaths : FilePath → Prop} {keep : heap → Prop}
  {earlier : List (FilePath × IO.Error)} {entry : heap}
  {prior : source.FailedCalls start earlier entry}

/-- Add read-only attempts using their existing block frame and actual
returns from the fixed interpreter. -/
theorem readOnly (before : SelectedEffects view source start target files protectedPaths keep prior)
    {more : List (FilePath × IO.Error)} {reached : heap}
    (block : RawFinalizedOpenAttempts view directory source.calls source.init source.release entry more reached)
    (frame : (files entry).Frames protectedPaths (files reached))
    (carries : keep entry → keep reached)
    (executed : source.FailedCalls entry more reached) :
    SelectedEffects view source start target files protectedPaths keep (prior.append executed) :=
  .append (calls := executed) before (.inl block.preserves.2) frame carries

/-- Add one failed repair at its returned heap. Cleanup preserves the
image reached by the worker, including any replacement keeper. -/
theorem repair (before : SelectedEffects view source start target files protectedPaths keep prior)
    {input : FilePath} {workerImage : FileImage}
    (failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry workerImage)
    (repair : EffectTrace target (view.files entry).image workerImage)
    (frame : (files entry).Frames protectedPaths (files failed.reached))
    (carries : keep entry → keep failed.reached)
    (returned : source.openTable input entry = .error failed.diagnostic failed.reached) :
    SelectedEffects view source start target files protectedPaths keep (prior.next input returned) := by
  obtain ⟨_, _, _, _, _, _, image, _⟩ := failed.returns
  exact .append (calls := .next .empty input returned) before (.inr (image.symm ▸ repair)) frame carries

/-- Fold the image, file frame and keeper observation over the same
caller-visible endpoints as the actual failed calls. -/
theorem preserves {returns : List (FilePath × IO.Error)} {reached : heap}
    {attempts : source.FailedCalls start returns reached}
    (effects : SelectedEffects view source start target files protectedPaths keep attempts)
    (valid : (view.files start).image.Valid target) :
    (view.files reached).image.Valid target ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) ∧
      (keep start → keep reached) := by
  induction effects with
  | empty => exact ⟨valid, rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, id⟩
  | @append _ _ entry reached _ _ _ image frame carries ih =>
    obtain ⟨valid, kept, protectedFiles, keptObservation⟩ := ih
    obtain ⟨next, sameSeals⟩ : (view.files reached).image.Valid target ∧
        (view.files reached).image.kept = (view.files entry).image.kept := image.elim
      (fun unchanged => ⟨unchanged.symm ▸ valid, congrArg FileImage.kept unchanged⟩)
      (fun repair => ⟨repair.valid valid.selected valid.keeper valid.later, repair.keepsSealed⟩)
    exact ⟨next, sameSeals.trans kept, protectedFiles.trans frame,
      carries ∘ keptObservation⟩

end RawOpenRetryTrace.SelectedEffects

/-- After a sequence of read-only and mutating failed opens, the new
reader uses the keeper and later names at the last returned heap. The
selected history, retained runs and earlier client reads are unchanged. -/
theorem NativeReadPosition.preparesWriteRetry {stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {prior : List WAL.Write} {log : List DatabaseSubmissions}
    (current : NativeReadPosition prior log) {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write}
    {table : PackedTable} (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    (manifest : target.pair.manifest = current.state.writer.target.pair.manifest)
    {returns : List (FilePath × IO.Error)} {reached : heap} {files : heap → CheckpointSurvivingFiles}
    {protectedPaths : FilePath → Prop} {keep : heap → Prop}
    {attempts : source.FailedCalls start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view source start
      target files protectedPaths keep attempts) (initial : (view.files start).image.Valid target) :
    Nonempty (current.SelectedWritePlan batch target (view.files reached).image) ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) ∧ (keep start → keep reached) := by
  obtain ⟨observed, sealed, frame, carries⟩ := effects.preserves initial
  exact ⟨current.preparesSelectedWrite prepared fits admitted observed manifest, sealed, frame, carries⟩

end Alvoki.Storage.DiskSession
