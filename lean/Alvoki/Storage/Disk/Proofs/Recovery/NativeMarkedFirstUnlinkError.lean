import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedFirstBarrierWork
import Alvoki.Storage.Disk.Proofs.Recovery.HeldLaterWalPrune
import Alvoki.Storage.Disk.NativeAlignedKeeperCache
import Alvoki.Storage.Disk.Proofs.Write.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeOpenReadyStorage

namespace Alvoki.Storage.DiskSession

open System Manifest SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The post-prune retry retains the selected children and the complete
canonical WAL inventory through the selected marker, including gaps. -/
def NativeReadyState.pruneRecoveryScope (state : NativeReadyState) (through : Nat) (path : FilePath) : Prop :=
  (state.selectedRetryPath path ∧ path ≠ state.session.directory.path) ∨
    ∃ start ≤ through, path = state.session.directory.file (.walSegment start)

theorem NativeReadyState.pruneRecoveryScope_child {state : NativeReadyState} {through : Nat} {path : FilePath}
    (inScope : state.pruneRecoveryScope through path) : ∃ file, path = state.session.directory.file file := by
  rcases inScope with ⟨selected, notRoot⟩ | ⟨start, _, rfl⟩
  · have protectedPath : state.crashPath path :=
      NativeReadyState.crashPath_iff_write.mpr (selected.imp id Or.inr)
    exact (NativeReadyState.crashPath_rootOrChild protectedPath).resolve_left notRoot
  · exact ⟨.walSegment start, rfl⟩

/-- A directory fsync that reports an error before settlement retains
one earlier crash namespace for all these children. The live map at
issuance can already lack the names removed by the accepted suffix. -/
theorem WalRootSyncEffect.crashFilesBeforeEffect
    {directory : DiskDirectory} {scope : FilePath → Prop} {before reached : CheckpointStorageObservation}
    (effect : WalRootSyncEffect directory false before reached)
    (managed : ∀ path, scope path → ∃ file, path = directory.file file) :
    before.CrashFileFrame scope reached := by
  constructor
  · constructor
    · intro path inside
      obtain ⟨file, rfl⟩ := managed path inside
      have visible := effect.visible file
      exact ⟨visible, fun inode bound => effect.bytes _ (.inl rfl) file inode (visible.trans bound)⟩
    · intro names possible
      obtain ⟨prior, earlier, same⟩ := effect.unchanged rfl names possible
      refine ⟨prior, earlier, fun path inside => ?_⟩
      obtain ⟨file, rfl⟩ := managed path inside
      exact same file
  · intro names possible path inside inode bound payload sampled
    obtain ⟨file, rfl⟩ := managed path inside
    exact effect.bytes names (.inr possible) file inode bound ▸ sampled

/-- Every reached crash namespace retains the settled bindings of the
source files in scope. Its named inode can use a durable payload from
the source. A successful barrier can select the current live bindings
even when no earlier crash namespace was observed. -/
structure CheckpointStorageObservation.SettledCrashFiles (scope : FilePath → Prop)
    (source reached : CheckpointStorageObservation) : Prop where
  visible : source.files.Frames scope reached.files
  names : ∀ names ∈ reached.crashNames, ∀ path, scope path → names path = source.files.names path
  bytes : ∀ names ∈ reached.crashNames, ∀ path, scope path → ∀ inode, names path = some inode →
    ∀ payload ∈ reached.files.bytes inode, payload ∈ source.files.bytes inode

theorem CheckpointStorageObservation.SettledCrashFiles.frame {scope : FilePath → Prop}
    {source before reached : CheckpointStorageObservation}
    (kept : source.SettledCrashFiles scope before) (frame : before.CrashFileFrame scope reached) :
    source.SettledCrashFiles scope reached := by
  refine ⟨kept.visible.trans frame.toFrames.visible, ?_, ?_⟩
  · intro names possible path inside
    obtain ⟨prior, earlier, same⟩ := frame.toFrames.survivors names possible
    exact (same path inside).trans (kept.names prior earlier path inside)
  · intro names possible path inside inode bound payload durable
    obtain ⟨prior, earlier, same⟩ := frame.toFrames.survivors names possible
    exact kept.bytes prior earlier path inside inode ((same path inside).symm.trans bound) payload
      (frame.bytes names possible path inside inode bound payload durable)

/-- A returned error before settlement keeps an earlier map. An error
after settlement instead keeps the issued live map. Both preserve the
same already-settled authorization footprint through the cutoff. -/
theorem WalRootSyncEffect.keepsSettledCrashFiles
    {directory : DiskDirectory} {scope : FilePath → Prop} {effective : Bool}
    {source before reached : CheckpointStorageObservation}
    (effect : WalRootSyncEffect directory effective before reached)
    (managed : ∀ path, scope path → ∃ file, path = directory.file file)
    (beforeSync : source.CrashFileFrame scope before)
    (settled : source.SettledCrashFiles scope source) :
    source.SettledCrashFiles scope reached := by
  cases effective
  · exact settled.frame (beforeSync.trans (effect.crashFilesBeforeEffect managed))
  · have afterSync : before.files.Frames scope reached.files := by
      intro path inside
      obtain ⟨file, rfl⟩ := managed path inside
      have kept := effect.visible file
      exact ⟨kept, fun inode named => effect.bytes _ (.inl rfl) file inode (kept.trans named)⟩
    refine ⟨beforeSync.toFrames.visible.trans afterSync, ?_, ?_⟩
    · intro names possible path inside
      obtain ⟨file, rfl⟩ := managed path inside
      exact (effect.settled rfl names possible file).trans
        ((effect.visible file).trans (beforeSync.toFrames.visible _ inside).1)
    · intro names possible path inside inode bound payload durable
      obtain ⟨file, rfl⟩ := managed path inside
      have atIssue := ((effect.settled rfl names possible file).trans (effect.visible file)).symm.trans bound
      obtain ⟨sameName, sameBytes⟩ := beforeSync.toFrames.visible _ inside
      have atSource := sameName.symm.trans atIssue
      exact sameBytes inode atSource ▸ (effect.bytes names (.inr possible) file inode bound ▸ durable)

/-- Fold the same primitive frame over the literal accepted unlinks.
The frame covers only unaffected paths, with byte choices of crash
inodes included even when those inodes are not live. -/
theorem CheckpointStorageObservation.CrashFileFrame.afterReturnedWalUnlinks
    {heap : Type} {directory : DiskDirectory} {plan : Plan}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    {observe : heap → CheckpointStorageObservation} {scope : FilePath → Prop}
    {authorized unlinked : heap}
    (offTarget : ∀ ordinal ∈ plan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    (unlink : ∀ {ordinal issued after result}, ¬ scope (directory.file (.walSegment ordinal)) →
      remove (directory.file (.walSegment ordinal)) issued = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (observe issued).CrashFileFrame scope (observe after))
    (unlinks : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () unlinked) :
    (observe authorized).CrashFileFrame scope (observe unlinked) := by
  exact foldReturnedWalUnlinks directory plan remove write sync rename
    (fun (_ : Unit) atHeap => (observe authorized).CrashFileFrame scope (observe atHeap))
    (fun _ _ => ()) (initial := ()) (.refl _ _)
    (fun listed called accepted framed => framed.trans (unlink (offTarget _ listed) called accepted)) unlinks

/-- Before keeper rename, every crash choice names one old inode. Its
sampled bytes and the immutable children on that same map determine the
ordinary retry entry, both during pruning and after a scratch-file error. -/
theorem RawWriteRebootEntry.selectsSettledKeeper
    {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {failed rebooted : heap} {target : Target} {old : Nat}
    (seen : RawWriteRebootEntry state view observe (fun h => (observe h).files.names) visible failed rebooted)
    (first : target.first = state.writer.wal.active.first)
    (manifest : target.pair.manifest = state.writer.target.pair.manifest)
    (durable : state.SelectedRetryDurability target (observe failed))
    (bound : ∀ names ∈ (observe failed).crashNames, names (state.session.directory.file (.walSegment target.first)) = some old)
    (accepted : ∀ bytes ∈ (observe failed).files.bytes old, target.Accepts (some bytes))
    (children : ∀ path, state.selectedRetryPath path → path ≠ state.session.directory.path →
      (observe rebooted).files.names path = (observe failed).files.names path) :
    (observe rebooted).files.names (state.session.directory.file (.walSegment target.first)) = some old ∧
      target.Accepts (some (visible rebooted old)) ∧
      RawOpenRetryTrace.SelectedEntry view state target (fun h => (observe h).files.names) visible rebooted ∧
      TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
      (view.descriptors rebooted).slots = [] := by
  let path := state.session.directory.file (.walSegment target.first)
  have named := bound _ seen.chosen
  have sampled := seen.samplesWal path old
    (.inr (.inr (congrArg (fun n => state.session.directory.file (.walSegment n)) first))) named
  exact ⟨named, accepted _ sampled, seen.selectsRetryAfterRepair first manifest durable children
    (fun names possible => ⟨old, bound names possible, accepted⟩)⟩

/-- The second reboot uses its sampled protected files to select the same
target and its sampled namespace to discover any later WAL names. Only
the inventory through the selected marker is preserved across pruning. -/
theorem RawWriteRebootEntry.startsRecoveryAfterFramedPrune
    {heap : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {authorized failed rebooted : heap} {target : Target} {firstOffset : Nat}
    (seen : RawWriteRebootEntry state view observe (fun atHeap => (observe atHeap).files.names)
      visible failed rebooted)
    (reset : seen.DurableReset)
    (first : target.first = state.writer.wal.active.first)
    (sameManifest : target.pair.manifest = state.writer.target.pair.manifest)
    (durable : state.SelectedRetryDurability target (observe failed))
    (keeper : RawOpenRetryTrace.LiveKeeperCrashChoices state.session.directory target (observe authorized))
    (window : state.writer.wal.NamespaceWindow state.session.directory firstOffset target.range.through
      (observe authorized).files.names)
    (survivors : (observe authorized).SettledCrashFiles (state.pruneRecoveryScope target.range.through) (observe failed)) :
    RawOpenRetryTrace.SelectedEntry view state target (fun atHeap => (observe atHeap).files.names) visible rebooted ∧
      TryLockObserves (view.files rebooted).owners state.session.directory (.ok true) ∧
      (view.descriptors rebooted).slots = [] ∧
      RawOpenRetryTrace.RecoveryObservations view state target observe visible firstOffset target.range.through rebooted := by
  let directory := state.session.directory
  obtain ⟨inode, bound, accepted⟩ := keeper
  let path := directory.file (.walSegment target.first)
  have inside : state.pruneRecoveryScope target.range.through path := .inr ⟨_, target.firstCovered, rfl⟩
  have oldBound names allowed := (survivors.names names allowed path inside).trans bound
  have oldBytes := (survivors.visible path inside).2 inode bound
  obtain ⟨_, _, selected, vacant, empty⟩ := seen.selectsSettledKeeper first sameManifest durable oldBound
    (fun bytes member => accepted bytes (oldBytes ▸ member)) (fun path protectedPath notRoot =>
      (survivors.names _ seen.chosen path (.inl ⟨protectedPath, notRoot⟩)).trans
        (survivors.visible path (.inl ⟨protectedPath, notRoot⟩)).1.symm)
  have chosenWindow := window.frame (by
    intro start _ within
    let path := directory.file (.walSegment start)
    have inside : state.pruneRecoveryScope target.range.through path := .inr ⟨start, within, rfl⟩
    exact congrArg Option.isSome (survivors.names _ seen.chosen path inside))
  exact ⟨selected, vacant, empty, seen.startsRecoveryObservations reset selected chosenWindow⟩

section SuffixRetryFrame

variable {heap : Type} {directory : DiskDirectory} {scope : FilePath → Prop} {through : Nat}
  {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}

/-- The physical frame follows each reached unlink, including an outer
error or an inner result that the owned unlink rejects. It stops at the
same heap as the actual loop. Only the off-target scope is protected. -/
theorem CheckpointStorageObservation.CrashFileFrame.afterWalUnlinks
    {plan : Plan}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (outside : ∀ ordinal ∈ plan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    (unlink : ∀ ordinal ∈ plan.newer, ∀ issued, ¬ scope (directory.file (.walSegment ordinal)) →
      (observe issued).CrashFileFrame scope
        (observe (NativeFileEffectProjection.reached (remove (directory.file (.walSegment ordinal)) issued))))
    (authorized : heap) :
    (observe authorized).CrashFileFrame scope
      (observe (NativeFileEffectProjection.reached (((plan.newer.map Step.unlink).forM
        (performPaths directory plan remove throw write sync rename)) authorized))) :=
  framesWalUnlinks (fun before after => (observe before).CrashFileFrame scope (observe after))
    (fun atHeap => .refl scope (observe atHeap)) (fun before after => before.trans after)
    (fun ordinal member issued => unlink ordinal member issued (outside ordinal member)) authorized

variable (directory scope through observe readBytes) in
/-- The remove's reached state preserves the selected files, the
bounded catalog, and the root's name in its parent. -/
def SampledCheckpointRetryFrame.WalUnlinkEffects (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) : Prop :=
  ∀ ordinal ∈ plan.newer, ∀ issued,
    let victim := directory.file (.walSegment ordinal)
    let after := NativeFileEffectProjection.reached (remove victim issued)
    (observe issued).files.Frames
      (fun path => (scope path ∨ ∃ start ≤ through, path = directory.file (.walSegment start)) ∧ path ≠ victim)
      (observe after).files ∧
    (observe issued).Frames (· = directory.path) (observe after) ∧
    ∀ path, scope path → path ≠ victim → ∀ inode,
      (observe issued).files.names path = some inode → readBytes after inode = readBytes issued inode

/-- The checked suffix starts beyond the selected cutoff. Each reached
remove can change its own binding while preserving the selected scope. -/
theorem SampledCheckpointRetryFrame.afterWalUnlinks
    {plan : Plan}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (valid : plan.valid = true) (cutoff : through ≤ plan.through)
    (outside : ∀ ordinal ∈ plan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    (unlink : SampledCheckpointRetryFrame.WalUnlinkEffects directory scope through observe readBytes plan remove)
    (entry : heap) :
    SampledCheckpointRetryFrame directory scope through observe readBytes entry
      (NativeFileEffectProjection.reached (((plan.newer.map Step.unlink).forM
        (performPaths directory plan remove throw write sync rename)) entry)) := by
  let frame := SampledCheckpointRetryFrame directory scope through observe readBytes
  have each ordinal (listed : ordinal ∈ plan.newer) issued :
      frame issued (NativeFileEffectProjection.reached (remove (directory.file (.walSegment ordinal)) issued)) := by
    obtain ⟨physical, parent, visible⟩ := unlink ordinal listed issued
    have offTarget path (keep : scope path) : path ≠ directory.file (.walSegment ordinal) := by
      intro same
      exact outside ordinal listed (same ▸ keep)
    have durable : (observe issued).files.Frames scope
        (observe (NativeFileEffectProjection.reached (remove (directory.file (.walSegment ordinal)) issued))).files :=
      fun path keep => physical path ⟨.inl keep, offTarget path keep⟩
    refine ⟨?_, ?_, durable, parent⟩
    · intro path keep
      exact ⟨(durable path keep).1, fun inode named => congrArg (fun data => [data])
        (visible path keep (offTarget path keep) inode named)⟩
    · intro start within
      have later := (Plan.valid_iff plan).mp valid |>.2.2 ordinal listed
      have apart : directory.file (.walSegment start) ≠ directory.file (.walSegment ordinal) := by
        intro collision
        have ordinals := directory.walSegment_path_injective collision
        have upper : ordinal ≤ plan.through := ordinals ▸ Nat.le_trans within cutoff
        exact (Nat.not_lt_of_ge upper) later
      exact congrArg Option.isSome (physical _ ⟨.inr ⟨start, within, rfl⟩, apart⟩).1
  exact framesWalUnlinks (plan := plan) (write := write) (sync := sync) (rename := rename)
    frame SampledCheckpointRetryFrame.refl SampledCheckpointRetryFrame.trans each entry

/-- Once all removals returned, the only operation left in the
prune block is the root fsync. -/
theorem failedPruneDirectoryOfReturnedUnlinks
    {plan : Plan} {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    {authorized unlinked reached : heap} {cause : IO.Error}
    (unlinks : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () unlinked)
    (stopped : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .error cause reached) :
    sync #[directory.path] unlinked = .error cause reached := by
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at stopped
  simp only [Bind.bind, EStateM.bind, unlinks, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, Pure.pure, EStateM.pure] at stopped
  cases returned : sync #[directory.path] unlinked with
  | error => simpa only [returned] using stopped
  | ok value => cases value; simp [returned] at stopped

/-- The literal prune block carries the selected files across ordinary
errors. A barrier effect is used only after every unlink has returned. -/
theorem SampledCheckpointRetryFrame.afterFailedWalPruneBlock
    {plan : Plan} {physicalSize : Nat}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (valid : plan.valid = true) (bytes : plan.keeperBytes.size = plan.keeperSize)
    (bounded : plan.keeperSize ≤ physicalSize) (needsPrune : plan.newer ≠ [] ∨ plan.keeperSize < physicalSize)
    (cutoff : through ≤ plan.through)
    (outside : ∀ ordinal ∈ plan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    {entry authorized reached : heap} {cause : IO.Error}
    (authorization : sync #[directory.path] entry = .ok () authorized)
    (rootFrame : SampledCheckpointRetryFrame directory scope through observe readBytes entry authorized)
    (unlink : SampledCheckpointRetryFrame.WalUnlinkEffects directory scope through observe readBytes plan remove)
    (stopped : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .error cause reached)
    (barrier : ∀ {unlinked}, ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () unlinked →
      sync #[directory.path] unlinked = .error cause reached →
      SampledCheckpointRetryFrame directory scope through observe readBytes unlinked reached) :
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .error cause reached ∧
      SampledCheckpointRetryFrame directory scope through observe readBytes entry reached := by
  refine ⟨finishBoundedMarkedOpen_errorDuringPrune valid bytes bounded needsPrune authorization stopped, ?_⟩
  let perform := performPaths directory plan remove throw write sync rename
  have frame := rootFrame.trans (SampledCheckpointRetryFrame.afterWalUnlinks write sync rename valid cutoff outside
    unlink authorized)
  have stoppedPrune := stopped
  change ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) authorized = _ at stopped
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at stopped
  cases unlinks : ((plan.newer.map Step.unlink).forM perform) authorized with
  | error diagnostic failed =>
    have same : failed = reached := (EStateM.Result.error.inj
      (by simpa only [Bind.bind, EStateM.bind, unlinks] using stopped)).2
    subst failed
    simpa only [perform, unlinks, NativeFileEffectProjection.reached] using frame
  | ok value unlinked =>
    cases value
    have throughUnlinks : SampledCheckpointRetryFrame directory scope through observe readBytes entry unlinked := by
      simpa only [perform, unlinks, NativeFileEffectProjection.reached] using frame
    exact throughUnlinks.trans (barrier unlinks (failedPruneDirectoryOfReturnedUnlinks unlinks stoppedPrune))

end SuffixRetryFrame

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published}

private abbrev RepairState := CensusDirectoryCache × CensusOpenState
private abbrev CapturedHandle := DescriptorInventory × DescriptorSlot × Nat
private abbrev UnlinkState := RepairState × DirectoryReadNamespace × (Nat → Option ByteArray)

private def authorizedFiles (admission : CensusOpenAdmissionReports input directory inventory retry) :
    LockedFileState FileImage := { admission.held with image := retry.image.syncDirectory }

private def unlinkedFiles (admission : CensusOpenAdmissionReports input directory inventory retry)
    (first : Nat) (effective : Bool) : LockedFileState FileImage :=
  { admission.held with image :=
    if effective then retry.image.syncDirectory.unlinkLater first else retry.image.syncDirectory }

/-- Actual returned first unlink after a successful authorization sync.
The observed unlink resolves the selected child of the captured root.
The model covers reported errors before and after deletion, with no
descriptor changes during unlink itself. -/
structure NativeMarkedFirstUnlinkError (reads : CapturedMarkedReadReports admission layout published)
    (keeper : CapturedKeeperOpenReports reads) where
  first : Nat
  rest : List Nat
  order : retry.image.later.visible = first :: rest
  openRead : FilePath → EStateM IO.Error CensusOpenState CapturedHandle
  fsync : CapturedHandle → EStateM IO.Error CensusOpenState Unit
  write : FilePath → ByteArray → EStateM IO.Error RepairState Unit
  renameFile : FilePath → FilePath → EStateM IO.Error RepairState Unit
  afterAuthorization : List LockReferenceDrop
  authorized : fsync (admission.reached, admission.cached, 0) (keeper.afterRead, admission.held) =
    .ok () (keeper.afterRead.afterDrops afterAuthorization, authorizedFiles admission)
  ownerLive : admission.owner ∈ (keeper.afterRead.afterDrops afterAuthorization).slots
  directoryLive : admission.cached ∈ (keeper.afterRead.afterDrops afterAuthorization).slots
  keeperLive : layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat →
    reads.wal.keeper.calls.slot ∈ (keeper.afterRead.afterDrops afterAuthorization).slots
  lookup : RunChildLookup admission.root (renderWalSegmentName first) admission.view
  metadata : IO.FS.Metadata
  measured : reads.reads.stat (directory.file (.walSegment first)) =
    .ok (metadata, admission.view.modelObject lookup.child)
  beforeUnlink : DirectoryReadNamespace
  resolves : RunChildLookup admission.root (renderWalSegmentName first) beforeUnlink
  authorizedNames : ∀ name, beforeUnlink.child admission.root name = admission.view.child admission.root name
  cause : IO.Error
  propagated : RunCollection.ownedUnlinkResult (.error cause) = .error cause
  effective : Bool
  afterUnlink : DirectoryReadNamespace
  afterBytes : Nat → Option ByteArray
  unlink : FilePath → EStateM IO.Error UnlinkState (Except IO.Error Unit)
  failed : unlink (directory.file (.walSegment first))
    ((NativeMarkedFirstBarrierError.keeperCache (reads := reads),
      keeper.afterRead.afterDrops afterAuthorization, authorizedFiles admission), beforeUnlink, reads.reads.objectBytes) =
        .ok (.error cause) ((NativeMarkedFirstBarrierError.keeperCache (reads := reads),
          keeper.afterRead.afterDrops afterAuthorization, unlinkedFiles admission first effective), afterUnlink, afterBytes)
  removed : afterUnlink.child admission.root (renderWalSegmentName first) =
    if effective then none else some resolves.child
  otherNames : ∀ name ≠ renderWalSegmentName first,
    afterUnlink.child admission.root name = beforeUnlink.child admission.root name
  privateObject : ∀ name ≠ renderWalSegmentName first,
    (admission.view.child admission.root name).map admission.view.modelObject ≠
      some (admission.view.modelObject lookup.child)
  otherBytes : ∀ inode ≠ admission.view.modelObject lookup.child, afterBytes inode = reads.reads.objectBytes inode

namespace NativeMarkedFirstUnlinkError

variable {keeper : CapturedKeeperOpenReports reads}
  (seen : NativeMarkedFirstUnlinkError reads keeper)

def census : DescriptorInventory := keeper.afterRead.afterDrops seen.afterAuthorization

def reachedFiles : LockedFileState FileImage := unlinkedFiles admission seen.first seen.effective

def groupedSync : Array FilePath → EStateM IO.Error RepairState Unit :=
  SyncPathGroup.run (SyncHandleRouting.sync directory.path seen.openRead seen.fsync)

/-- Project the real unlink including its reported path bindings and
contents. The detailed raw state belongs to this one reached callback. -/
def removeFile (path : FilePath) : EStateM IO.Error RepairState (Except IO.Error Unit) :=
  fun before => match seen.unlink path (before, seen.beforeUnlink, reads.reads.objectBytes) with
  | .ok value (reached, _) => .ok value reached
  | .error cause (reached, _) => .error cause reached

theorem unlinkReturns :
    seen.removeFile (directory.file (.walSegment seen.first))
      (NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, authorizedFiles admission) =
    .ok (.error seen.cause) (NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, seen.reachedFiles) := by
  simp only [removeFile, census, reachedFiles, seen.failed]

theorem authorizes :
    seen.groupedSync #[directory.path]
      (NativeMarkedFirstBarrierError.keeperCache (reads := reads), keeper.afterRead, admission.held) =
    .ok () (NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, authorizedFiles admission) := by
  unfold groupedSync
  rw [SyncPathGroup.run_single]
  have cached : (NativeMarkedFirstBarrierError.keeperCache (reads := reads)).directory =
      some (admission.reached, admission.cached, 0) := by
    unfold NativeMarkedFirstBarrierError.keeperCache Cache.captureKeeper
    split <;> rfl
  simp [SyncHandleRouting.sync, Cache.resolve, cached, withCache, seen.authorized, census]

private theorem finishFirstUnlink {state : Type} (prepared : Prepared retry.image layout.target layout.plan)
    {first : Nat} {rest : List Nat} (order : retry.image.later.visible = first :: rest)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    {initial authorized reached : state} {cause : IO.Error}
    (good : sync #[directory.path] initial = .ok () authorized)
    (bad : removeFile (directory.file (.walSegment first)) authorized = .ok (.error cause) reached)
    (propagated : RunCollection.ownedUnlinkResult (.error cause) = .error cause) :
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size removeFile write sync renameFile initial =
      .error cause reached := by
  obtain ⟨covered, physical, later⟩ := (Plan.valid_iff layout.plan).mp prepared.valid
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have valid := (Plan.valid_iff layout.boundedPlan).mpr ⟨covered, Nat.le_of_eq bytes.symm, later⟩
  refine finishBoundedMarkedOpen_errorDuringUnlinks valid bytes physical good ?_
  have newer : layout.boundedPlan.newer = first :: rest := prepared.names.trans order
  simp only [newer, List.map_cons, List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind,
    performPaths, RunCollection.performPaths, bad, propagated, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Authorization uses the cached directory. Only the first canonical
later name reaches the reported unlink error. No later deletion,
suffix sync, keeper sync, trim or installation is reached. -/
theorem finishes (prepared : Prepared retry.image layout.target layout.plan) :
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      seen.removeFile seen.write seen.groupedSync seen.renameFile
      (NativeMarkedFirstBarrierError.keeperCache (reads := reads), keeper.afterRead, admission.held) =
    .error seen.cause (NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, seen.reachedFiles) :=
  finishFirstUnlink prepared seen.order _ _ _ _ seen.authorizes seen.unlinkReturns seen.propagated

private def charge (run : EStateM IO.Error RepairState α) : EStateM IO.Error (RepairState × Nat) α :=
  fun (before, calls) => match run before with
  | .ok value after => .ok value (after, calls + 1)
  | .error error after => .error error (after, calls + 1)

def countedFinish (plan : Plan) (measure : Nat) : EStateM IO.Error (RepairState × Nat) Unit :=
  finishBoundedMarkedOpen directory plan measure
    (fun path => charge (seen.removeFile path)) (fun path bytes => charge (seen.write path bytes))
    (fun paths => charge (seen.groupedSync paths)) (fun source target => charge (seen.renameFile source target))

/-- The counted schedule charges one grouped request for the singleton
authorization sync and one request for the actual first unlink. -/
theorem repairRequests (prepared : Prepared retry.image layout.target layout.plan) :
    seen.countedFinish layout.boundedPlan layout.plan.keeperBytes.size
      ((NativeMarkedFirstBarrierError.keeperCache (reads := reads), keeper.afterRead, admission.held), 0) =
    .error seen.cause
      ((NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, seen.reachedFiles), 2) := by
  unfold countedFinish
  let afterAuthorization := ((NativeMarkedFirstBarrierError.keeperCache (reads := reads),
    seen.census, authorizedFiles admission), 1)
  exact finishFirstUnlink prepared seen.order _ _ _ _ (authorized := afterAuthorization)
    (by simp [charge, seen.authorizes, afterAuthorization])
    (by simp [charge, seen.unlinkReturns, afterAuthorization]) seen.propagated

/-- The returned unlink belongs to the first regular single-link name
from the same checked catalog, with the actual unlink resolving its
measured object under the same captured parent. -/
theorem inspected :
    renderWalSegmentName seen.first ∈ reads.catalog.inventory.names ∧
    reads.catalog.inventory.reports.lstat (directory.file (.walSegment seen.first)) = .ok seen.metadata ∧
    seen.metadata.type = .file ∧ seen.metadata.numLinks = 1 ∧ seen.resolves.child = seen.lookup.child := by
  have first : seen.first ∈ retry.image.later.visible := seen.order.symm ▸ List.mem_cons_self ..
  have accepted : seen.first ∈ reads.catalog.older ++
      (layout.sealed ++ [layout.keeper]).map WalSegment.first ++ retry.image.later.visible :=
    List.mem_append_right _ first
  have oldBound := seen.lookup.binds
  rw [seen.lookup.atRoot, seen.lookup.atName] at oldBound
  have same := seen.resolves.child_eq ((seen.authorizedNames _).trans oldBound)
  obtain ⟨metadata, found, regular, oneLink⟩ := reads.catalog.regular seen.first accepted
  have measured := (reads.stat (directory.file (.walSegment seen.first))).trans (by rw [seen.measured])
  obtain rfl := Except.ok.inj (measured.symm.trans found)
  exact ⟨(reads.catalog.present _).mpr accepted, measured, regular, oneLink, same⟩

theorem unlinkBinding :
    seen.afterUnlink.child admission.root (renderWalSegmentName seen.first) =
      (if seen.effective then none else some seen.lookup.child) := by
  simpa only [seen.inspected.2.2.2.2] using seen.removed

def retains (name : String) (object : DeviceInode) (bytes : ByteArray) : Prop :=
  seen.afterUnlink.child admission.root name = some object ∧
    seen.afterBytes (admission.view.modelObject object) = some bytes

private theorem retainsChild {name : String} {object : DeviceInode} {bytes : ByteArray}
    (different : name ≠ renderWalSegmentName seen.first)
    (bound : admission.view.child admission.root name = some object)
    (contents : reads.reads.objectBytes (admission.view.modelObject object) = some bytes) :
    seen.retains name object bytes := by
  have apart := seen.privateObject name different
  rw [bound, Option.map_some, Ne, Option.some.injEq] at apart
  exact ⟨(seen.otherNames name different).trans ((seen.authorizedNames name).trans bound),
    (seen.otherBytes _ apart).trans contents⟩

/-- The selected WAL payloads, including the exact physical keeper
extent, retain their raw child identities and bytes at the unlink return. -/
theorem retainsWal (prepared : Prepared retry.image layout.target layout.plan)
    (segment : WalSegment) (selected : segment ∈ layout.sealed ++ [layout.keeper]) :
    ∃ object, admission.view.child admission.root (renderWalSegmentName segment.first) = some object ∧
      seen.retains (renderWalSegmentName segment.first) object
        (if segment.first = layout.keeper.first then layout.keeper.bytes ++ layout.tail else segment.bytes) := by
  have later : layout.range.through < seen.first :=
    prepared.newer _ List.mem_cons_self _ (seen.order.symm ▸ List.mem_cons_self ..)
  have within := layout.through ▸ layout.chain.startsWithin segment selected
  have different : renderWalSegmentName segment.first ≠ renderWalSegmentName seen.first := by
    intro names
    have path : directory.file (.walSegment segment.first) = directory.file (.walSegment seen.first) :=
      congrArg (fun name : String => (⟨(directory.path.toString ++ "/") ++ name⟩ : FilePath)) names
    have same := directory.walSegment_path_injective path
    omega
  rcases List.mem_append.mp selected with sealed | last
  · let file := reads.wal.sealedFile segment sealed
    have apart : segment.first ≠ layout.keeper.first := by
      have sorted := (List.pairwise_append.mp reads.catalog.ordered).1
      have selectedOrder := (List.pairwise_append.mp sorted).2.1
      rw [List.map_append, List.map_singleton] at selectedOrder
      have less := (List.pairwise_append.mp selectedOrder).2.2 segment.first (List.mem_map_of_mem sealed)
        layout.keeper.first (List.mem_singleton_self _)
      exact Nat.ne_of_lt less
    exact ⟨file.object, file.bound, by simpa only [ite_eq_right apart] using seen.retainsChild different file.bound file.contents⟩
  · obtain rfl := List.mem_singleton.mp last
    let file := reads.wal.keeper
    exact ⟨file.object, file.bound, by simpa only [ite_true] using seen.retainsChild different file.bound file.contents⟩

private theorem runNameNeLater (generation : UInt64) (index : Nat) :
    renderRunFileName generation index ≠ renderWalSegmentName seen.first := by
  intro same
  have paths : directory.file (.run generation index) = directory.file (.walSegment seen.first) :=
    congrArg (fun name : String => (⟨(directory.path.toString ++ "/") ++ name⟩ : FilePath)) same
  obtain ⟨_, impossible⟩ := directory.walSegment_exclusive paths
  cases impossible

theorem retainsRun {bytes payload : ByteArray} {manifest : IntegrityCheckpoint}
    (present : retry.image.directory.active.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) {index : Nat}
    (within : index < manifest.header.runCount.toNat)
    (stored : published.durable manifest.header.generation index = some payload) :
    ∃ object, admission.view.child admission.root (renderRunFileName manifest.header.generation index) = some object ∧
      seen.retains (renderRunFileName manifest.header.generation index) object payload := by
  obtain ⟨object, bound, contents, _⟩ := reads.runs bytes manifest present decoded index within payload stored
  exact ⟨object, bound, seen.retainsChild (seen.runNameNeLater _ _) bound contents⟩

theorem retainsManifest {bytes : ByteArray} (present : retry.image.directory.active.manifest = some bytes) :
    ∃ object, admission.view.child admission.root "MANIFEST" = some object ∧ seen.retains "MANIFEST" object bytes := by
  obtain ⟨⟨file⟩, _⟩ := reads.metadata.manifestFile bytes present
  have different : "MANIFEST" ≠ renderWalSegmentName seen.first := by
    intro same
    have names := congrArg (fun name : String => name.toList.take 4) same
    simp [renderWalSegmentName, String.toList_append] at names
  exact ⟨file.object, file.bound, seen.retainsChild different file.bound file.contents⟩

theorem retainsMarker {bytes : ByteArray} (present : retry.image.directory.active.walBoundary = some bytes) :
    ∃ object, admission.view.child admission.root "WAL.commit" = some object ∧ seen.retains "WAL.commit" object bytes := by
  obtain ⟨file, _⟩ := reads.metadata.markerFile bytes present
  have different : "WAL.commit" ≠ renderWalSegmentName seen.first := by
    intro same
    have names := congrArg (fun name : String => name.toList.take 4) same
    simp [renderWalSegmentName, String.toList_append] at names
  exact ⟨file.object, file.bound, seen.retainsChild different file.bound file.contents⟩

/-- Only the first later name can have become visibly absent. The
already authorized directory keeps the durable old sighting until a
later namespace barrier; the selected metadata and WAL image are fixed. -/
theorem fileEffects (prepared : Prepared retry.image layout.target layout.plan) :
    EffectTrace layout.target retry.image seen.reachedFiles.image ∧
    seen.reachedFiles.image.directory = retry.image.directory.syncDirectory ∧
    seen.reachedFiles.image.kept = retry.image.kept ∧ seen.reachedFiles.image.keeper = retry.image.keeper ∧
    seen.reachedFiles.image.later.crashImages =
      (if seen.effective then
        [(retry.image.syncDirectory.unlinkLater seen.first).later.visible, retry.image.later.visible]
      else [retry.image.later.visible]) := by
  have synced : EffectTrace layout.target retry.image retry.image.syncDirectory := .authorized
  have later : layout.range.through < seen.first :=
    prepared.newer _ List.mem_cons_self _ (seen.order.symm ▸ List.mem_cons_self ..)
  cases effect : seen.effective <;> simp only [reachedFiles, unlinkedFiles, effect, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨synced, rfl, rfl, rfl, rfl⟩
  · exact ⟨synced.unlink later, rfl, rfl, rfl, rfl⟩

theorem keepsSelection (prepared : Prepared retry.image layout.target layout.plan)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) :
    SelectedIntegrityCheckpoint published.durable seen.reachedFiles.image.directory.active.manifest checkpoint := by
  rw [(seen.fileEffects prepared).2.1]
  exact selected

/-- The captured lock, directory and any pending keeper are still live
at the failed unlink's return. The pending handle names the exact
physical keeper observed before the successful authorization. -/
theorem custody :
    admission.owner ∈ seen.census.slots ∧ admission.cached ∈ seen.census.slots ∧
    (layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat →
      reads.wal.keeper.calls.slot ∈ seen.census.slots) ∧
    seen.census.inode reads.wal.keeper.calls.slot.description =
      admission.view.modelObject reads.wal.keeper.object :=
  ⟨seen.ownerLive, seen.directoryLive, seen.keeperLive, keeper.openedKeeper.2.2.2.1⟩

/-- The same chronological keeper read reaches the real authorized
prune path and returns with the reported census and file image. -/
theorem stopsRecovery
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    let prepare := reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
      chronology.sealRelease keeper.readKeeperAt
    finishPreparedWithCensus prepare (fun plan measure =>
      finishBoundedMarkedOpen directory plan measure seen.removeFile seen.write seen.groupedSync seen.renameFile)
      admission.cache (admission.reached, admission.held) = .error seen.cause (seen.census, seen.reachedFiles) := by
  dsimp only
  have extent : reads.wal.keeper.calls.metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size :=
    reads.wal.keeper.observesFile.extent
  have fits : layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by rw [extent]; simp
  obtain ⟨opened, reached, _⟩ := reads.preparesFromCensus chronology.manifest chronology.runs selected
    chronology.marker chronology.beforeListing keeper chronology.seals chronology.offsets chronology.retained
    following prepared.newer accepted ordered keeper.readKeeperAt (keeper.reads fits)
  unfold finishPreparedWithCensus
  rw [reached]
  dsimp only
  have failed := seen.finishes prepared
  simp only [NativeMarkedFirstBarrierError.keeperCache] at failed
  rw [failed]

def afterUnlock (unlock : Except IO.Error Unit) : LockedFileState FileImage :=
  match unlock with
  | .ok () => { seen.reachedFiles with owners := seen.reachedFiles.owners.set (directory.file .lock) none }
  | .error _ => seen.reachedFiles

def diagnostic (unlock : Except IO.Error Unit) : IO.Error :=
  match unlock with
  | .ok () => seen.cause
  | .error cause => cause

def run (chronology : CapturedMarkedReadCensus reads keeper)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run fun path owner cache =>
    admission.recoverWithMarked path
      (finishPreparedWithCensus (reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
        chronology.sealRelease keeper.readKeeperAt) (fun plan measure =>
          finishBoundedMarkedOpen path plan measure seen.removeFile seen.write seen.groupedSync seen.renameFile) cache)
      (bootstrap path cache) >>= install path owner cache

/-- The native returned open error cleans up the still-owned lock in the
census produced by the successful authorization and failed unlink. The
cleanup leaves the exact pre- or post-unlink file image in either case. -/
theorem returns
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    {marker : IO.FS.Metadata}
    (found : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some marker) (admission.reached, admission.held))
    (unlock : Except IO.Error Unit)
    (unlocked : admission.unlock admission.owner () (seen.census, seen.reachedFiles) = match unlock with
      | .ok () => .ok () (seen.census, seen.afterUnlock unlock)
      | .error cause => .error cause (seen.census, seen.afterUnlock unlock))
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    seen.run chronology bootstrap install = .error (seen.diagnostic unlock) (seen.census, seen.afterUnlock unlock) ∧
    (seen.afterUnlock unlock).image = seen.reachedFiles.image ∧
    admission.owner ∈ seen.census.slots ∧ admission.cached ∈ seen.census.slots ∧
    (TryLockObserves (seen.afterUnlock unlock).owners directory (.ok true) ↔ unlock = .ok ()) ∧
    reads.metadataReadRequests + reads.payloadReadRequests ≤
      (retry.image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit +
        (((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
          (layout.range.through - layout.first) * WAL.frameSize) ∧
    reads.directoryWork.opendirCalls + reads.directoryWork.readdirCalls + reads.directoryWork.closedirCalls =
      reads.listing.scan.names.length + 3 ∧
    seen.countedFinish layout.boundedPlan layout.plan.keeperBytes.size
      ((NativeMarkedFirstBarrierError.keeperCache (reads := reads), keeper.afterRead, admission.held), 0) =
    .error seen.cause ((NativeMarkedFirstBarrierError.keeperCache (reads := reads), seen.census, seen.reachedFiles), 2) := by
  have stopped := seen.stopsRecovery chronology selected prepared following accepted ordered
  have returned : seen.run chronology bootstrap install =
      .error (seen.diagnostic unlock) (seen.census, seen.afterUnlock unlock) := by
    unfold run
    rw [admission.run_reachesRecovery]
    simp only [Bind.bind, EStateM.bind, admission.recoverWithMarked_selects flat found, Option.isSome_some,
      ↓reduceIte, stopped, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, unlocked]
    cases unlock with
    | ok result => cases result; rfl
    | error cause => rfl
  obtain ⟨opened, read, closed, _⟩ := reads.directoryWork_exact
  refine ⟨returned, ?_, seen.ownerLive, seen.directoryLive, ?_,
    Nat.add_le_add reads.metadataReadRequests_le (reads.payloadReadRequests_le selected prepared following),
    by omega, seen.repairRequests prepared⟩
  · cases unlock <;> rfl
  · cases unlock <;>
      simp [afterUnlock, reachedFiles, unlinkedFiles, TryLockObserves, LockOwners.set, CensusOpenAdmissionReports.held]


end NativeMarkedFirstUnlinkError
end Alvoki.Storage.DiskSession
