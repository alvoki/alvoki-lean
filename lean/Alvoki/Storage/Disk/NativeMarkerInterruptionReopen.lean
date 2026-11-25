import Alvoki.Storage.Disk.NativePendingMarkerDirectory
import Alvoki.Storage.Disk.NativePendingStagedMarkerSync
import Alvoki.Storage.Disk.NativeWriteCrashReads

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- At these issued operations the keeper's full file sync has returned.
The pending write still has no ordinary result. -/
inductive NativeMarkerPublicationStop {state : NativeReadyState} (prepared : NativeReadyWritePreparation state) where
  | stagedSync (stop : NativeWriteStagedMarkerSyncStop prepared)
  | rename (stop : NativeWriteMarkerRenameStop prepared)
  | directorySync (stop : NativeWriteMarkerDirectoryStop prepared)
      (oldMarker : RunChildLookup stop.renamed.root "WAL.commit" stop.renamed.stageView)
      (freshMarkerInode : stop.renamed.stageView.modelObject stop.renamed.openedMarker.child ≠
        stop.renamed.stageView.modelObject oldMarker.child)

namespace NativeMarkerPublicationStop

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

def request : NativeMarkerPublicationStop prepared → WriteRequest
  | .stagedSync stop | .rename stop | .directorySync stop _ _ => stop.request

def files : NativeMarkerPublicationStop prepared → FileImage
  | .stagedSync stop | .rename stop | .directorySync stop _ _ => stop.files

def cut : NativeMarkerPublicationStop prepared → MarkerInterruption
  | .stagedSync stop | .rename stop | .directorySync stop _ _ => stop.cut

def staging : NativeMarkerPublicationStop prepared → NativeReadyWriteStaging prepared
  | .stagedSync stop => stop.staging
  | .rename stop => stop.synced.toNativeReadyWriteStaging
  | .directorySync stop _ _ => stop.renamed.toNativeReadyWriteFileSyncs.toNativeReadyWriteStaging

def oldMarkerChild : NativeMarkerPublicationStop prepared → DeviceInode
  | .stagedSync stop => stop.oldMarker.child
  | .rename stop => stop.oldMarker.child
  | .directorySync _ oldMarker _ => oldMarker.child

def Reached {history log} (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} : NativeMarkerPublicationStop prepared → Prop
  | .stagedSync stop => NativePendingStagedMarkerSync current stop
  | .rename stop => NativePendingMarkerRename current stop
  | .directorySync stop _ _ => NativePendingMarkerDirectory current stop

theorem reaches (current : NativeReadPosition history log) {prepared : NativeReadyWritePreparation current.state}
    (stop : NativeMarkerPublicationStop prepared) : stop.Reached current := by
  cases stop with
  | stagedSync stopped => exact current.stopsAtStagedMarkerSync stopped
  | rename stopped => exact current.stopsAtMarkerRename stopped
  | directorySync stopped _ _ => exact current.stopsAtMarkerDirectory stopped

theorem batchCut (stop : NativeMarkerPublicationStop prepared) (valid : state.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  cases stop with
  | stagedSync stopped => exact stopped.batchCut valid
  | rename stopped => exact stopped.batchCut valid
  | directorySync stopped _ _ => exact stopped.batchCut valid

theorem kept (stop : NativeMarkerPublicationStop prepared) :
    stop.files.kept = state.files.image.kept := by
  cases stop <;> rfl

theorem keeperSurvives (stop : NativeMarkerPublicationStop prepared) (valid : state.Valid) :
    some (state.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∈ stop.files.keeper.crashImages := by
  cases stop with
  | stagedSync stopped =>
    obtain ⟨_, _, _, active, durable⟩ := stopped.choices valid
    change _ ∈ stopped.files.keeper.crashImages
    rw [durable, active]
    exact List.mem_singleton_self _
  | rename stopped =>
    obtain ⟨_, _, _, active, durable⟩ := stopped.choices valid
    change _ ∈ stopped.files.keeper.crashImages
    rw [durable, active]
    exact List.mem_singleton_self _
  | directorySync stopped _ _ =>
    obtain ⟨_, _, _, active, durable⟩ := stopped.choices valid
    change _ ∈ stopped.files.keeper.crashImages
    rw [durable, active]
    exact List.mem_singleton_self _

end NativeMarkerPublicationStop

/-- The reported power-loss choice covers the actual stopped write.
The new name, when it survives, names the exact staged inode that was
synced before rename. Other children still refer to the held directory. -/
structure NativeMarkerPublicationCrash {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}
    (stop : NativeMarkerPublicationStop prepared) where
  usesNewMarker : Bool
  survived : (if usesNewMarker then
      ⟨state.files.image.directory.active.manifest, some prepared.marker⟩ else state.writer.target.pair) ∈
    stop.files.directory.crashImages
  later : List Nat
  laterSurvived : later ∈ stop.files.later.crashImages
  namespaceView : DirectoryReadNamespace
  objects : namespaceView.modelObject = stop.staging.stageView.modelObject
  children : ∀ name, name ≠ "WAL.commit" → name ≠ "WAL.commit.next" →
    namespaceView.child stop.staging.root name = stop.staging.stageView.child stop.staging.root name
  marker : namespaceView.child stop.staging.root "WAL.commit" =
    some (if usesNewMarker then stop.staging.openedMarker.child else stop.oldMarkerChild)
  raw : WriteCrashView
  root : raw.names state.session.directory.path = some (namespaceView.modelObject stop.staging.root)
  lock : raw.names (state.session.directory.file .lock) =
    (namespaceView.child stop.staging.root "LOCK").map namespaceView.modelObject
  keeper : raw.names prepared.keeperPath =
    (namespaceView.child stop.staging.root prepared.keeperName).map namespaceView.modelObject
  markerPath : raw.names prepared.markerPath =
    (namespaceView.child stop.staging.root "WAL.commit").map namespaceView.modelObject

namespace NativeMarkerPublicationCrash

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}
  {stop : NativeMarkerPublicationStop prepared}

def pair (crash : NativeMarkerPublicationCrash stop) : DirectoryPublication.Bindings :=
  if crash.usesNewMarker then ⟨state.files.image.directory.active.manifest, some prepared.marker⟩
  else state.writer.target.pair

def retry (crash : NativeMarkerPublicationCrash stop) : LockedFileState FileImage :=
  ⟨stop.files.crash crash.pair (some (state.writer.wal.active.bytes ++ WAL.encode prepared.batch)) crash.later,
    state.writer.owners.set (state.session.directory.file .lock) none⟩

theorem vacant (crash : NativeMarkerPublicationCrash stop) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  simp [retry, TryLockObserves, LockOwners.set]

theorem powerLoss (crash : NativeMarkerPublicationCrash stop) (valid : state.Valid) :
    BoundedReopenTrace state.session.directory (BatchRetryTarget state.writer.history prepared.batch state.writer.wal.active.first)
      ⟨stop.files, state.writer.owners⟩ crash.retry :=
  .powerLoss .empty crash.survived (stop.keeperSurvives valid) crash.laterSurvived

theorem sameRoot (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names state.session.directory.path = some (state.census.inode state.directorySlot.description) := by
  rw [crash.root, crash.objects, stop.staging.stageObjects, stop.staging.directoryIdentity]

theorem sameLock (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  rw [crash.lock, crash.children "LOCK" (by decide) (by decide),
    stop.staging.stageBindings.2.1,
    Option.map_some, crash.objects, stop.staging.stageObjects, stop.staging.lockIdentity]

theorem sameKeeper (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names prepared.keeperPath = some (state.census.inode stop.staging.keeperSlot.description) := by
  have keeperName : prepared.keeperName ≠ "WAL.commit" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  have keeperStage : prepared.keeperName ≠ "WAL.commit.next" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  obtain ⟨_, inodes, _, _, keeperIdentity⟩ := stop.staging.selectsKeeper.custody
  rw [crash.keeper, crash.children _ keeperName keeperStage,
    stop.staging.stageBindings.1,
    Option.map_some, crash.objects, stop.staging.stageObjects, keeperIdentity, inodes]

theorem markerObject (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names prepared.markerPath = some (if crash.usesNewMarker then
      state.census.inode stop.staging.markerSlot.description else
      stop.staging.stageView.modelObject stop.oldMarkerChild) := by
  rw [crash.markerPath, crash.marker, Option.map_some, crash.objects]
  split <;> simp only [stop.staging.stageIdentity]

/-- The two encoded counts are distinct: the new marker covers a
nonempty accepted group and both counts fit in the format. -/
theorem selects (crash : NativeMarkerPublicationCrash stop) (valid : state.Valid)
    {chosen : List WAL.Write}
    (allowed : chosen = state.writer.history ∨ chosen = state.writer.history ++ prepared.batch)
    (marker : crash.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64)) :
    chosen = state.writer.history ++ (if crash.usesNewMarker then prepared.batch else []) := by
  have newCount := (prepared.extended valid).1
  have prior := valid.retained.resumed.bytes
  have grows : 0 < WAL.frameSize * prepared.rows.length :=
    Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (prepared.nonempty ∘ List.length_eq_zero_iff.mp))
  have increases : (WAL.encode state.writer.history).size < prepared.count := by
    dsimp only [NativeReadyWritePreparation.count]
    omega
  have newFits : prepared.count < UInt64.size := prepared.fits
  have oldFits := Nat.lt_trans increases newFits
  have different : WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 ≠ prepared.marker := by
    intro equal
    have counts := congrArg WAL.Boundary.decode equal
    simp only [NativeReadyWritePreparation.marker, WAL.Boundary.decode_encode, Except.ok.injEq] at counts
    have lengths := congrArg UInt64.toNat counts
    change (UInt64.ofNat (WAL.encode state.writer.history).size).toNat = (UInt64.ofNat prepared.count).toNat at lengths
    rw [UInt64.toNat_ofNat_of_lt' oldFits, UInt64.toNat_ofNat_of_lt' newFits] at lengths
    exact (Nat.ne_of_lt increases) lengths
  have oldMarker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  cases chosenMarker : crash.usesNewMarker with
  | false =>
    simp only [pair, chosenMarker, Bool.false_eq_true, ite_false, List.append_nil] at marker ⊢
    rcases allowed with prior | whole
    · exact prior
    · rw [whole, newCount, oldMarker] at marker
      exact False.elim (different (Option.some.inj marker))
  | true =>
    simp only [pair, chosenMarker, ite_true] at marker ⊢
    rcases allowed with prior | whole
    · rw [prior] at marker
      exact False.elim (different (Option.some.inj marker).symm)
    · exact whole

end NativeMarkerPublicationCrash

/-- A staged marker's file sync does not replace the active marker.
The reboot selects the old marker even when that file sync took effect. -/
theorem NativeMarkerPublicationCrash.oldMarkerAfterStagedSync {state : NativeReadyState}
    {prepared : NativeReadyWritePreparation state} {stopped : NativeWriteStagedMarkerSyncStop prepared}
    (crash : NativeMarkerPublicationCrash (.stagedSync stopped)) (valid : state.Valid) :
    crash.usesNewMarker = false := by
  have survived := crash.survived
  change crash.pair ∈ stopped.files.directory.crashImages at survived
  rw [(stopped.choices valid).2.1] at survived
  have prior := List.mem_singleton.mp survived
  have marker := (congrArg DirectoryPublication.Bindings.walBoundary prior).trans
    (valid.retained.selectPriorKeeper ByteArray.empty).1
  have history := crash.selects valid (.inl rfl) marker
  cases selected : crash.usesNewMarker with
  | false => rfl
  | true =>
    simp only [selected, ite_true] at history
    have count := congrArg List.length history
    have batch := (prepareBatch_spec prepared.prepared).1
    simp only [List.length_append] at count
    exact False.elim (prepared.nonempty (List.length_eq_zero_iff.mp (show prepared.rows.length = 0 by omega)))

/-- The next captured opener consumes the selected reboot inventory.
The raw directory and all its child identities agree with that report. -/
structure NativeMarkerPublicationCrashReads {state : NativeReadyState}
    {prepared : NativeReadyWritePreparation state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) (input : FilePath) {history : List WAL.Write}
    (layout : CanonicalKeeperLayout crash.retry.image history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint)
    extends NativeWriteCrashReads crash.raw input crash.vacant layout selected where
  root : opening.admission.root = stop.staging.root
  childMap : opening.admission.view.child opening.admission.root = crash.namespaceView.child stop.staging.root
  identityMap : opening.admission.view.modelObject = crash.namespaceView.modelObject

/-- Recovery returns the exact marked session from the survivor. The
interrupted write adds one submitted group and supplies no acknowledgement. -/
structure NativeMarkerPublicationCrashContinuation {history log} (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) (input : FilePath) (retained : List WAL.Write)
    (next : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch prepared.batch])) : Prop where
  reached : stop.Reached current
  wholeOrNone : retained = [] ∨ retained = prepared.batch
  chosenByMarker : retained = if crash.usesNewMarker then prepared.batch else []
  reads : next.reads = current.reads
  newPhase : next.state.session.phaseRef ≠ current.state.session.phaseRef
  newSession : next.state.session.sessionRef ≠ current.state.session.sessionRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  marker : next.state.files.image.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64)
  exactOpen :
    ∃ (layout : CanonicalKeeperLayout crash.retry.image (history ++ retained))
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (seen : NativeMarkerPublicationCrashReads crash input layout selected),
      next.opened = seen.opening.finish.run seen.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.session.directory = current.state.session.directory ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      seen.opening.reads.bindings (current.state.session.directory.file .lock) =
        some (current.state.census.inode current.state.owner.description) ∧
      seen.opening.reads.bindings current.state.session.directory.path =
        some (current.state.census.inode current.state.directorySlot.description) ∧
      seen.toNativeWriteCrashReads.ReadsSurvivor prepared.markerPath
        (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64) ∧
      seen.toNativeWriteCrashReads.ReadsSurvivor prepared.keeperPath
        (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  replay : InstalledClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads
    (history ++ retained) next.state.writer.installed next.state.session

namespace NativeMarkerPublicationCrash

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}
  {stop : NativeMarkerPublicationStop prepared}

def wal (crash : NativeMarkerPublicationCrash stop) (history : List WAL.Write) : WalSegmentImage :=
  state.writer.wal.appendSelectedView crash.retry.image.directory.active history

/-- One plan for the checkpoint and WAL bytes selected by the reported
survivor. Its history is fixed by the surviving marker. -/
structure Plan (crash : NativeMarkerPublicationCrash stop) where
  history : List WAL.Write
  allowed : history = state.writer.history ∨ history = state.writer.history ++ prepared.batch
  marker : crash.retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  layout : CanonicalKeeperLayout crash.retry.image history
  walLayout : (crash.wal history).ReadLayout history
  walValid : (crash.wal history).Valid history
  first : layout.target.first = (crash.wal history).active.first
  sameKeeper : layout.keeper = (crash.wal history).active
  descriptors : layout.sealed ++ [layout.keeper] = (crash.wal history).readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads ((crash.wal history).segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, ((crash.wal history).readDescriptors layout.range.watermark).map WalSegment.first)
  repair : Prepared crash.retry.image layout.target layout.plan
  kept : crash.retry.image.kept = ((crash.wal history).checkpointReopenFiles (crash.wal history).directory none).kept
  selected : SelectedIntegrityCheckpoint state.writer.published.durable crash.retry.image.directory.active.manifest
    state.writer.checkpoint
  accepted : state.writer.published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
    crash.retry.image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history
  noLater : crash.retry.image.later.visible = []

theorem plans (crash : NativeMarkerPublicationCrash stop) (valid : state.Valid) : Nonempty crash.Plan := by
  let ready := valid.retained
  have oldRange : state.writer.wal.directory.active.walRange =
      some ⟨state.writer.target.range.watermark, state.writer.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact state.writer.target.decoded
  have checkpoint := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  have count : state.writer.history.length = state.writer.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have fits : (WAL.encode (state.writer.history ++ prepared.batch)).size < UInt64.size :=
    (prepared.extended valid).1.symm ▸ (show prepared.count < UInt64.size from prepared.fits)
  have projected := stop.batchCut valid
  change BatchCutProjection stop.files
    ((writeFilesAfter (runBatchEffects state.writer.history prepared.batch
      (stop.cut.writeEffects prepared.tails (state.files.image.directory.staged .walBoundary))
      (state.files.image.directory.staged .walBoundary))).reopenSegment
      state.writer.wal.active.first state.writer.history state.files.image.directory.active.manifest)
    at projected
  have directoryFiles : state.files.image.directory = state.writer.wal.directory := ready.directoryFiles
  rw [directoryFiles] at projected
  obtain ⟨kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, _, first, sameKeeper, descriptors, offsets,
    repair, noLater, accepted, ordered, _⟩ :=
    (crash.powerLoss valid).selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered
      count prepared.prepared fits checkpoint _ projected
  have manifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  exact ⟨⟨chosen, allowed, marker, layout, walLayout, walValid, first, sameKeeper, descriptors, offsets, repair,
    kept.trans (stop.kept.trans ready.sealedFiles), manifest.symm ▸ ready.resumed.selected, accepted, ordered, noLater⟩⟩

/-- The same fully synced keeper is aligned for the new marker and
has exactly the attempted batch's excess length for the old marker. -/
theorem Plan.tailSize {crash : NativeMarkerPublicationCrash stop} (plan : crash.Plan) (valid : state.Valid) :
    plan.layout.tail.size = if crash.usesNewMarker then 0 else (WAL.encode prepared.batch).size := by
  have counted := congrArg ByteArray.size (Option.some.inj plan.layout.visible.symm)
  change (plan.layout.keeper.bytes ++ plan.layout.tail).size =
    (state.writer.wal.active.bytes ++ WAL.encode prepared.batch).size at counted
  have starts : state.writer.wal.active.first ≤ state.writer.history.length := by
    rw [← valid.retained.layout.activeEnd]
    exact valid.retained.layout.forward _ (List.mem_append_right _ (by simp))
  have selected := crash.selects valid plan.allowed plan.marker
  have keeper : plan.layout.keeper.bytes = WAL.encode (plan.history.drop state.writer.wal.active.first) := by
    rw [plan.sameKeeper]
    rfl
  rw [keeper.trans (congrArg (fun rows => WAL.encode (rows.drop state.writer.wal.active.first)) selected)] at counted
  cases marker : crash.usesNewMarker with
  | false =>
    simp only [marker, Bool.false_eq_true, ite_false, List.append_nil, ← valid.retained.layout.activeBytes,
      ByteArray.size_append] at counted ⊢
    omega
  | true =>
    simp only [marker, ite_true, List.drop_append_of_le_length starts, WAL.encode_append,
      ← valid.retained.layout.activeBytes, ByteArray.size_append] at counted ⊢
    omega

end NativeMarkerPublicationCrash

/-- Reuse the same admitted selected reader in the normalized continuation
and at the raw opened-table boundary. -/
theorem NativeReadPosition.recoversInterruptedMarkerFrom (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) {input : FilePath} (plan : crash.Plan)
    (seen : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected) :
    ∃ retained next, NativeMarkerPublicationCrashContinuation current crash input retained next ∧
      plan.history = history ++ retained ∧ next.opened = seen.opening.finish.run seen.opening.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.owner = seen.opening.admission.owner ∧
      next.state.directorySlot = seen.opening.admission.cached := by
  obtain ⟨valid, earlierHistory, replay⟩ := current.readPrefix.refines
  let ready := valid.retained
  obtain ⟨chosen, allowedInWriter, marker, layout, walLayout, walValid, first, _, descriptors, offsets, repair, kept,
    selected, accepted, ordered, _⟩ := plan
  have allowed : chosen = history ∨ chosen = history ++ prepared.batch :=
    allowedInWriter.imp (·.trans earlierHistory) (·.trans (congrArg (· ++ prepared.batch) earlierHistory))
  obtain ⟨pending, bounded⟩ := replay.appendUncertain current.readPrefix.readsBounded allowed ordered
  obtain ⟨reached, seed, cache, census, owner, directorySlot, pair, durable, checkpointEq, path, _, _,
    phaseFresh, sessionFresh⟩ :=
    seen.opening.finish.startsNativeReadPrefix seen.opening.chronology seen.opening.markerFound repair
      (seen.opening.reads.walReads.selectedAfterWatermark offsets descriptors) accepted ordered walLayout walValid
      ready.spans repair.pair first kept pending bounded
  let retained := if crash.usesNewMarker then prepared.batch else []
  have whole : retained = [] ∨ retained = prepared.batch := by
    dsimp only [retained]
    split
    · exact .inr rfl
    · exact .inl rfl
  have historySelected : chosen = history ++ retained :=
    (crash.selects valid allowedInWriter marker).trans (congrArg (· ++ retained) earlierHistory)
  subst chosen
  have markerRead := seen.toNativeWriteCrashReads.readsMarker marker
  have keeperRead := seen.toNativeWriteCrashReads.readsKeeper
  have keeperPath : current.state.session.directory.file (.walSegment layout.keeper.first) = prepared.keeperPath := by
    exact congrArg (fun offset => current.state.session.directory.file (.walSegment offset))
      (first.trans (ready.active.symm.trans ready.resumed.keeper.symm))
  have keeperBytes : layout.keeper.bytes ++ layout.tail = current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch :=
    Option.some.inj layout.visible.symm
  rw [keeperPath, keeperBytes] at keeperRead
  let next : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch prepared.batch]) :=
    ⟨seen.opening.finish.run seen.opening.chronology, reached, reached, current.reads, seed⟩
  exact ⟨retained, next, ⟨stop.reaches current, whole, rfl, rfl,
    fun same => phaseFresh (same.symm ▸ seen.previousTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.previousTokens.2),
    checkpointEq, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    ⟨layout, selected, seen, rfl, seed.frames.1, rfl, path, cache, census, owner, directorySlot,
      seen.lock.trans crash.sameLock, seen.directory.trans crash.sameRoot, markerRead, keeperRead⟩,
    next.readPrefix.guardedReplay⟩, rfl, rfl, seed.frames.1, cache, owner, directorySlot⟩

theorem NativeReadPosition.recoversInterruptedMarker (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) {input : FilePath}
    (observe : ∀ chosen, ∀ layout : CanonicalKeeperLayout crash.retry.image chosen,
      (chosen = current.state.writer.history ∨ chosen = current.state.writer.history ++ prepared.batch) →
      Prepared crash.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeMarkerPublicationCrashReads crash input layout selected)) :
    ∃ retained next, NativeMarkerPublicationCrashContinuation current crash input retained next := by
  obtain ⟨plan⟩ := crash.plans current.readPrefix.refines.1
  obtain ⟨seen⟩ := observe plan.history plan.layout plan.allowed plan.repair plan.selected
  obtain ⟨retained, next, reopened, _⟩ := current.recoversInterruptedMarkerFrom crash plan seen
  exact ⟨retained, next, reopened⟩

end Alvoki.Storage.DiskSession
