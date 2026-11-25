import Alvoki.Storage.Disk.NativePendingMarkerDirectory
import Alvoki.Storage.Disk.NativeWriteCrashReads

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- At either of these issued operations both file syncs have finished.
The pending write still has no ordinary result. -/
inductive NativeMarkerPublicationStop {state : NativeReadyState} (prepared : NativeReadyWritePreparation state) where
  | rename (stop : NativeWriteMarkerRenameStop prepared)
  | directorySync (stop : NativeWriteMarkerDirectoryStop prepared)
      (oldMarker : RunChildLookup stop.renamed.root "WAL.commit" stop.renamed.stageView)
      (freshMarkerInode : stop.renamed.stageView.modelObject stop.renamed.openedMarker.child ≠
        stop.renamed.stageView.modelObject oldMarker.child)

namespace NativeMarkerPublicationStop

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

def request : NativeMarkerPublicationStop prepared → WriteRequest
  | .rename stop | .directorySync stop _ _ => stop.request

def files : NativeMarkerPublicationStop prepared → FileImage
  | .rename stop | .directorySync stop _ _ => stop.files

def cut : NativeMarkerPublicationStop prepared → MarkerInterruption
  | .rename stop | .directorySync stop _ _ => stop.cut

def synced : NativeMarkerPublicationStop prepared → NativeReadyWriteFileSyncs prepared
  | .rename stop => stop.synced
  | .directorySync stop _ _ => stop.renamed.toNativeReadyWriteFileSyncs

def oldMarkerChild : NativeMarkerPublicationStop prepared → DeviceInode
  | .rename stop => stop.oldMarker.child
  | .directorySync _ oldMarker _ => oldMarker.child

def Reached {history log} (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} : NativeMarkerPublicationStop prepared → Prop
  | .rename stop => NativePendingMarkerRename current stop
  | .directorySync stop _ _ => NativePendingMarkerDirectory current stop

theorem reaches (current : NativeReadPosition history log) {prepared : NativeReadyWritePreparation current.state}
    (stop : NativeMarkerPublicationStop prepared) : stop.Reached current := by
  cases stop with
  | rename stopped => exact current.stopsAtMarkerRename stopped
  | directorySync stopped _ _ => exact current.stopsAtMarkerDirectory stopped

theorem batchCut (stop : NativeMarkerPublicationStop prepared) (valid : state.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  cases stop with
  | rename stopped => exact stopped.batchCut valid
  | directorySync stopped _ _ => exact stopped.batchCut valid

theorem kept (stop : NativeMarkerPublicationStop prepared) :
    stop.files.kept = state.files.image.kept := by
  cases stop <;> rfl

theorem keeperSurvives (stop : NativeMarkerPublicationStop prepared) (valid : state.Valid) :
    some (state.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∈ stop.files.keeper.crashImages := by
  cases stop with
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
  objects : namespaceView.modelObject = stop.synced.stageView.modelObject
  children : ∀ name, name ≠ "WAL.commit" → name ≠ "WAL.commit.next" →
    namespaceView.child stop.synced.root name = stop.synced.stageView.child stop.synced.root name
  marker : namespaceView.child stop.synced.root "WAL.commit" =
    some (if usesNewMarker then stop.synced.openedMarker.child else stop.oldMarkerChild)
  raw : WriteCrashView
  root : raw.names state.session.directory.path = some (namespaceView.modelObject stop.synced.root)
  lock : raw.names (state.session.directory.file .lock) =
    (namespaceView.child stop.synced.root "LOCK").map namespaceView.modelObject
  keeper : raw.names prepared.keeperPath =
    (namespaceView.child stop.synced.root prepared.keeperName).map namespaceView.modelObject
  markerPath : raw.names prepared.markerPath =
    (namespaceView.child stop.synced.root "WAL.commit").map namespaceView.modelObject

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
  rw [crash.root, crash.objects, stop.synced.stageObjects, stop.synced.directoryIdentity]

theorem sameLock (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  rw [crash.lock, crash.children "LOCK" (by decide) (by decide),
    stop.synced.stageBindings.2.1,
    Option.map_some, crash.objects, stop.synced.stageObjects, stop.synced.lockIdentity]

theorem sameKeeper (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names prepared.keeperPath = some (state.census.inode stop.synced.keeperSlot.description) := by
  have keeperName : prepared.keeperName ≠ "WAL.commit" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  have keeperStage : prepared.keeperName ≠ "WAL.commit.next" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  obtain ⟨_, inodes, _, _, keeperIdentity⟩ := stop.synced.selectsKeeper.custody
  rw [crash.keeper, crash.children _ keeperName keeperStage,
    stop.synced.stageBindings.1,
    Option.map_some, crash.objects, stop.synced.stageObjects, keeperIdentity, inodes]

theorem markerObject (crash : NativeMarkerPublicationCrash stop) :
    crash.raw.names prepared.markerPath = some (if crash.usesNewMarker then
      state.census.inode stop.synced.markerSlot.description else
      stop.synced.stageView.modelObject stop.oldMarkerChild) := by
  rw [crash.markerPath, crash.marker, Option.map_some, crash.objects]
  split <;> simp only [stop.synced.stageIdentity]

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

/-- The next captured opener consumes the selected reboot inventory.
The raw directory and all its child identities agree with that report. -/
structure NativeMarkerPublicationCrashReads {state : NativeReadyState}
    {prepared : NativeReadyWritePreparation state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) (input : FilePath) {history : List WAL.Write}
    (layout : CanonicalKeeperLayout crash.retry.image history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint)
    extends NativeWriteCrashReads crash.raw input crash.vacant layout selected where
  root : opening.admission.root = stop.synced.root
  childMap : opening.admission.view.child opening.admission.root = crash.namespaceView.child stop.synced.root
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
  obtain ⟨valid, earlierHistory, replay⟩ := current.readPrefix.refines
  let ready := valid.retained
  have oldRange : current.state.writer.wal.directory.active.walRange =
      some ⟨current.state.writer.target.range.watermark, current.state.writer.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact current.state.writer.target.decoded
  have checkpoint := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  have count : current.state.writer.history.length = current.state.writer.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have fits : (WAL.encode (current.state.writer.history ++ prepared.batch)).size < UInt64.size :=
    (prepared.extended valid).1.symm ▸ (show prepared.count < UInt64.size from prepared.fits)
  have projected := stop.batchCut valid
  change BatchCutProjection stop.files
    ((writeFilesAfter (runBatchEffects current.state.writer.history prepared.batch
      (stop.cut.writeEffects prepared.tails (current.state.files.image.directory.staged .walBoundary))
      (current.state.files.image.directory.staged .walBoundary))).reopenSegment
      current.state.writer.wal.active.first current.state.writer.history current.state.files.image.directory.active.manifest)
    at projected
  have directoryFiles : current.state.files.image.directory = current.state.writer.wal.directory := ready.directoryFiles
  rw [directoryFiles] at projected
  obtain ⟨kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, _, first, _, descriptors, offsets,
    repair, _, accepted, ordered, _⟩ :=
    (crash.powerLoss valid).selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered
      count prepared.prepared fits checkpoint _ projected
  have manifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  let selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.state.writer.checkpoint :=
    manifest.symm ▸ ready.resumed.selected
  have allowedInWriter := allowed
  obtain ⟨seen⟩ := observe chosen layout allowed repair selected
  have allowed : chosen = history ∨ chosen = history ++ prepared.batch :=
    allowed.imp (·.trans earlierHistory) (·.trans (congrArg (· ++ prepared.batch) earlierHistory))
  obtain ⟨pending, bounded⟩ := replay.appendUncertain current.readPrefix.readsBounded allowed ordered
  obtain ⟨reached, seed, cache, census, owner, directorySlot, pair, durable, checkpointEq, path, _, _,
    phaseFresh, sessionFresh⟩ :=
    seen.opening.finish.startsNativeReadPrefix seen.opening.chronology seen.opening.markerFound repair
      (seen.opening.reads.walReads.selectedAfterWatermark offsets descriptors) accepted ordered walLayout walValid
      ready.spans repair.pair first (kept.trans (stop.kept.trans ready.sealedFiles)) pending bounded
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
  exact ⟨retained, next, stop.reaches current, whole, rfl, rfl,
    fun same => phaseFresh (same.symm ▸ seen.previousTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.previousTokens.2),
    checkpointEq, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    ⟨layout, selected, seen, rfl, seed.frames.1, rfl, path, cache, census, owner, directorySlot,
      seen.lock.trans crash.sameLock, seen.directory.trans crash.sameRoot, markerRead, keeperRead⟩,
    next.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
