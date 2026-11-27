import Alvoki.Storage.Disk.Proofs.Session.BatchInterruptionDispatch
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendPowerLoss

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev RenameCall := FilePath × FilePath
private abbrev RenameFiles := DescriptorInventory × WriteFiles
private abbrev RenameState := CensusDirectoryCache × RenameFiles
private abbrev RenameM := ExceptT IO.Error (EStateM RenameCall RenameState)

def observeReturnedWriteCall {stop : Type} (census : DescriptorInventory)
    (operation : EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit) :
    ExceptT IO.Error (EStateM stop RenameState) Unit :=
  fun (cache, inventory, files) => match operation (cache, files) with
  | .ok value (next, reached) => .ok (.ok value) (next, census, reached)
  | .error cause (next, reached) => .ok (.error cause) (next, inventory, reached)

namespace NativeReadyWritePreparation

variable {before : NativeReadyState}

/-- A completed append has the exact whole-batch byte count. -/
theorem extended (prepared : NativeReadyWritePreparation before) (valid : before.Valid) :
    (WAL.encode (before.writer.history ++ prepared.batch)).size = prepared.count ∧
      WAL.OrdinalsFrom 1 (before.writer.history ++ prepared.batch) := by
  let ready := valid.retained
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.writer.history.length = before.writer.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨_, ordered, _, size⟩ := prepareBatch_extends_history ready.resumed.ordered count prepared.prepared
  exact ⟨size.trans (by rw [NativeReadyWritePreparation.count, ready.resumed.bytes]), ordered⟩

/-- The batch interpreter's authorization of the same marker cut. -/
def modeledMarkerCut (prepared : NativeReadyWritePreparation before) (cut : MarkerInterruption) : ReopenImage :=
  let scratch := before.files.image.directory.staged .walBoundary
  (writeFilesAfter (runBatchEffects before.writer.history prepared.batch (cut.writeEffects prepared.tails scratch) scratch)).reopenSegment
    before.writer.wal.active.first before.writer.history before.files.image.directory.active.manifest

/-- The observed write files project onto the established allowed cut.
The prefix equality relates the exact callbacks that returned to the
ordered prefix preceding this issued operation. -/
theorem projectMarkerCut (prepared : NativeReadyWritePreparation before) (valid : before.Valid)
    (cut : MarkerInterruption) {reached : WriteFiles}
    (earlier : cut.reachedBatch before.writer.history prepared.batch prepared.tails
      (before.files.image.directory.staged .walBoundary) = reached) :
    BatchCutProjection
      (resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first (cut.interrupt prepared.marker reached))
      (prepared.modeledMarkerCut cut) := by
  have count := (prepared.extended valid).1
  have projected := cut.matchesBatchEffects before.writer.history prepared.batch prepared.tails
    (before.files.image.directory.staged .walBoundary)
  dsimp only at projected
  rw [count, earlier] at projected
  obtain ⟨visible, tails, marker, pairs⟩ := projected
  let bindMarker := DirectoryPublication.Bindings.mk before.files.image.directory.active.manifest
  let includePrefix := fun tail => some (WAL.encode (before.writer.history.drop before.writer.wal.active.first) ++ tail)
  exact ⟨congrArg bindMarker marker, congrArg (List.map bindMarker) pairs,
    congrArg includePrefix visible, congrArg (List.map includePrefix) tails, valid.retained.resumed.ready.pruned⟩

/-- Every selectable binding and keeper image selects the prior history
or the whole submitted group with the identical checkpoint. -/
theorem selectsMarkerCut (prepared : NativeReadyWritePreparation before) (valid : before.Valid)
    (cut : MarkerInterruption) {files : FileImage} (projected : BatchCutProjection files (prepared.modeledMarkerCut cut))
    {pair : DirectoryPublication.Bindings} (choice : pair ∈ files.directory.active :: files.directory.crashImages)
    {bytes : ByteArray} (keeper : some bytes ∈ files.keeper.active :: files.keeper.crashImages) :
    ∃ chosen, (chosen = before.writer.history ∨ chosen = before.writer.history ++ prepared.batch) ∧
      pair.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      SelectedIntegrityCheckpoint before.writer.published.durable pair.manifest before.writer.checkpoint ∧
      selectRetained before.writer.wal.active.first (WAL.encode chosen).size.toUInt64 bytes =
        .ok (WAL.encode (chosen.drop before.writer.wal.active.first)) ∧ WAL.OrdinalsFrom 1 chosen := by
  let ready := valid.retained
  have starts : before.writer.wal.active.first ≤ before.writer.history.length := by
    rw [← ready.layout.activeEnd]
    exact ready.layout.forward before.writer.wal.active (List.mem_append_right _ (by simp))
  have extended := prepared.extended valid
  have fits : (WAL.encode (before.writer.history ++ prepared.batch)).size < UInt64.size :=
    extended.1.symm ▸ (show prepared.count < UInt64.size from prepared.fits)
  rw [projected.active, projected.metadata] at choice
  rw [projected.keeper, projected.keeperChoices] at keeper
  obtain ⟨chosen, allowed, manifest, marker, prefixBytes⟩ := selectSegment_atReportedBatchCut starts fits
    (cut.writeEffects prepared.tails (before.files.image.directory.staged .walBoundary))
    before.files.image.directory.active.manifest (before.files.image.directory.staged .walBoundary) pair bytes choice keeper
  have old : before.files.image.directory.active = before.writer.target.pair := ready.resumed.ready.selected
  have selected : SelectedIntegrityCheckpoint before.writer.published.durable pair.manifest before.writer.checkpoint :=
    (manifest.trans (congrArg DirectoryPublication.Bindings.manifest old)).symm ▸ ready.resumed.selected
  exact ⟨chosen, allowed, marker, selected, prefixBytes,
    allowed.elim (fun prior => prior.symm ▸ ready.resumed.ordered) (fun whole => whole.symm ▸ extended.2)⟩

end NativeReadyWritePreparation

/-- An issued marker rename after both group fsyncs have returned. Its
source is the staged inode, which remains bound after the temporary handle
closes. The observed effect may move that same inode to the active name. -/
structure NativeWriteMarkerRenameStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  synced : NativeReadyWriteFileSyncs prepared
  oldMarker : RunChildLookup synced.root "WAL.commit" synced.stageView
  freshMarkerInode : synced.stageView.modelObject synced.openedMarker.child ≠ synced.stageView.modelObject oldMarker.child
  rename : FilePath → FilePath → EStateM RenameCall RenameFiles (Except IO.Error Unit)
  applied : Bool
  stopped : rename prepared.stagedPath prepared.markerPath (synced.census, prepared.bothSynced) =
    .error (prepared.stagedPath, prepared.markerPath) (synced.census,
      (MarkerInterruption.rename applied).interrupt prepared.marker prepared.bothSynced)
  after : DirectoryReadNamespace
  objects : after.modelObject = synced.stageView.modelObject
  frame : ∀ name, name ≠ "WAL.commit.next" → name ≠ "WAL.commit" →
    after.child synced.root name = synced.stageView.child synced.root name
  activeBinding : after.child synced.root "WAL.commit" =
    some (if applied then synced.openedMarker.child else oldMarker.child)
  stagedBinding : after.child synced.root "WAL.commit.next" =
    if applied then none else some synced.openedMarker.child

namespace NativeWriteMarkerRenameStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeWriteMarkerRenameStop prepared) : MarkerInterruption := .rename stop.applied

def reached (stop : NativeWriteMarkerRenameStop prepared) : RenameFiles :=
  (stop.synced.census, stop.cut.interrupt prepared.marker prepared.bothSynced)

def session (_stop : NativeWriteMarkerRenameStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

private def renamePath (stop : NativeWriteMarkerRenameStop prepared) (source target : FilePath) : RenameM Unit :=
  fun (cache, files) => match stop.rename source target files with
  | .ok result next => .ok result (cache, next)
  | .error atCall next => .error atCall (cache, next)

noncomputable def publication (stop : NativeWriteMarkerRenameStop prepared)
    (installed : Installed) (events : List WAL.Write) (bytes : Nat) : RenameM Unit :=
  let seen := stop.synced
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => observeReturnedWriteCall seen.afterSelect (seen.append path payload))
    (fun path payload => observeReturnedWriteCall seen.afterMarkerOpen (seen.stage path payload))
    (fun paths => observeReturnedWriteCall seen.census (seen.sync paths)) stop.renamePath

theorem stopsPublication (stop : NativeWriteMarkerRenameStop prepared) :
    (stop.publication before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error (prepared.stagedPath, prepared.markerPath) (stop.synced.appendCache, stop.reached) := by
  rw [publication, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, stop.synced.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl,
    stop.synced.stageReturns, stop.synced.groupReturns, renamePath, stop.stopped, cut, reached]

noncomputable def run (stop : NativeWriteMarkerRenameStop prepared) :=
  stop.request.runWithInterruption before.session.directory stop.synced.activeGuard.lookup stop.publication
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeWriteMarkerRenameStop prepared) (valid : before.Valid) :
    stop.run = .error (prepared.stagedPath, prepared.markerPath)
      (.poisoned, ⟨(stop.synced.appendCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.synced.activeGuard stop.publication stop.stopsPublication

def files (stop : NativeWriteMarkerRenameStop prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first stop.reached.2

/-- The staged description has closed before rename. The namespace still
refers to its original inode at the source and at the observed moved name. -/
structure Custody (stop : NativeWriteMarkerRenameStop prepared) : Prop where
  census : stop.reached.1 = stop.synced.afterSelect
  stageClosed : stop.reached.1.references stop.synced.markerSlot.description = []
  ownerLive : before.owner ∈ stop.reached.1.slots
  directoryLive : before.directorySlot ∈ stop.reached.1.slots
  keeperLive : stop.synced.keeperSlot ∈ stop.reached.1.slots
  sourceAtIssue : (stop.synced.stageView.child stop.synced.root "WAL.commit.next").map stop.synced.stageView.modelObject =
    some (stop.reached.1.inode stop.synced.markerSlot.description)
  oldMarkerSeparate : stop.synced.stageView.modelObject stop.oldMarker.child ≠
    stop.reached.1.inode stop.synced.markerSlot.description
  keeperObject : (stop.after.child stop.synced.root prepared.keeperName).map stop.after.modelObject =
    some (stop.reached.1.inode stop.synced.keeperSlot.description)
  lockObject : (stop.after.child stop.synced.root "LOCK").map stop.after.modelObject =
    some (stop.reached.1.inode before.owner.description)
  directoryObject : stop.after.modelObject stop.synced.root = stop.reached.1.inode before.directorySlot.description
  keeperCapture : stop.synced.keeperHandle.1.inode stop.synced.keeperSlot.description =
    stop.reached.1.inode stop.synced.keeperSlot.description
  directoryCapture : stop.synced.directoryCapture.inode before.directorySlot.description =
    stop.reached.1.inode before.directorySlot.description
  published : stop.applied = true →
    (stop.after.child stop.synced.root "WAL.commit").map stop.after.modelObject =
      some (stop.reached.1.inode stop.synced.markerSlot.description) ∧
    stop.after.child stop.synced.root "WAL.commit.next" = none
  unchanged : stop.applied = false →
    stop.after.child stop.synced.root "WAL.commit" = some stop.oldMarker.child ∧
    stop.after.child stop.synced.root "WAL.commit.next" = some stop.synced.openedMarker.child

theorem custody (stop : NativeWriteMarkerRenameStop prepared) (valid : before.Valid) : stop.Custody := by
  let seen := stop.synced
  obtain ⟨previous, inode, keeperLive, captured, checked⟩ := seen.selectsKeeper.custody
  obtain ⟨keeper, lock, stage⟩ := seen.stageBindings
  have atCut : stop.reached.1 = seen.afterSelect := seen.censusAfterClose
  have differentStage : prepared.keeperName ≠ "WAL.commit.next" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  have differentMarker : prepared.keeperName ≠ "WAL.commit" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  have stageInode : seen.stageView.modelObject seen.openedMarker.child = stop.reached.1.inode seen.markerSlot.description := by
    rw [atCut, inode]
    exact seen.stageIdentity
  refine ⟨atCut, atCut.symm ▸ seen.markerFresh, atCut.symm ▸ previous _ valid.ownerLive,
    atCut.symm ▸ previous _ valid.directoryLive, atCut.symm ▸ keeperLive, ?_, ?_, ?_, ?_, ?_,
    atCut.symm ▸ captured, ?_, ?_, ?_⟩
  · rw [stage, Option.map_some, stageInode]
  · exact fun same => stop.freshMarkerInode (stageInode.trans same.symm)
  · rw [stop.frame _ differentStage differentMarker, keeper, Option.map_some, stop.objects, seen.stageObjects, atCut, checked]
  · rw [stop.frame _ (by decide) (by decide), lock, Option.map_some, stop.objects, seen.stageObjects,
      atCut, inode, seen.lockIdentity]
  · rw [stop.objects, seen.stageObjects, atCut, inode, seen.directoryIdentity]
  · rw [atCut, inode, seen.sameDirectoryInode]
  · intro moved
    simp only [stop.activeBinding, moved, ite_true, Option.map_some, stop.objects, stop.stagedBinding, and_true]
    exact congrArg some stageInode
  · intro notMoved
    simp [stop.activeBinding, stop.stagedBinding, notMoved]

theorem atCut (stop : NativeWriteMarkerRenameStop prepared) :
    stop.reached.2 = if stop.applied then prepared.renamed else prepared.bothSynced := by
  unfold reached cut
  cases stop.applied <;> rfl

def newPair (_stop : NativeWriteMarkerRenameStop prepared) : DirectoryPublication.Bindings :=
  ⟨before.files.image.directory.active.manifest, some prepared.marker⟩

/-- Only the live rename effect changes the active marker. An effective
rename admits old and new markers as crash outcomes until the directory
barrier. Both effects keep the completely synced keeper. -/
theorem choices (stop : NativeWriteMarkerRenameStop prepared) (valid : before.Valid) :
    stop.files.directory.active = (if stop.applied then stop.newPair else before.writer.target.pair) ∧
    stop.files.directory.crashImages = (if stop.applied then [stop.newPair, before.writer.target.pair] else [before.writer.target.pair]) ∧
    stop.files.directory.staged .walBoundary = (if stop.applied then none else some (prepared.marker, true)) ∧
    stop.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    stop.files.keeper.crashImages = [stop.files.keeper.active] := by
  have old : before.files.image.directory.active = before.writer.target.pair := valid.retained.resumed.ready.selected
  have marker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  have pair :
      (⟨before.files.image.directory.active.manifest, some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
        DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [old, ← marker]
  have key := valid.retained.layout.activeBytes
  unfold files
  rw [stop.atCut]
  cases moved : stop.applied with
  | false =>
    change _ = before.writer.target.pair ∧ _ = [before.writer.target.pair] ∧ _
    refine ⟨pair, congrArg (fun p => [p]) pair, rfl, ?_, rfl⟩
    exact congrArg (fun bytes => some (bytes ++ WAL.encode prepared.batch)) key.symm
  | true =>
    change _ = stop.newPair ∧ _ = [stop.newPair, before.writer.target.pair] ∧ _
    refine ⟨rfl, congrArg (fun p => [stop.newPair, p]) pair, rfl, ?_, rfl⟩
    exact congrArg (fun bytes => some (bytes ++ WAL.encode prepared.batch)) key.symm

theorem batchCut (stop : NativeWriteMarkerRenameStop prepared) (valid : before.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  apply prepared.projectMarkerCut valid stop.cut
  simp only [MarkerInterruption.reachedBatch, (prepared.extended valid).1]
  rfl

/-- Every selectable binding and keeper image selects the prior history
or the whole submitted group with the identical checkpoint. -/
theorem selects (stop : NativeWriteMarkerRenameStop prepared) (valid : before.Valid)
    {pair : DirectoryPublication.Bindings} (choice : pair ∈ stop.files.directory.active :: stop.files.directory.crashImages)
    {bytes : ByteArray} (keeper : some bytes ∈ stop.files.keeper.active :: stop.files.keeper.crashImages) :
    ∃ chosen, (chosen = before.writer.history ∨ chosen = before.writer.history ++ prepared.batch) ∧
      pair.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      SelectedIntegrityCheckpoint before.writer.published.durable pair.manifest before.writer.checkpoint ∧
      selectRetained before.writer.wal.active.first (WAL.encode chosen).size.toUInt64 bytes =
        .ok (WAL.encode (chosen.drop before.writer.wal.active.first)) ∧ WAL.OrdinalsFrom 1 chosen:=
  prepared.selectsMarkerCut valid stop.cut (stop.batchCut valid) choice keeper

end NativeWriteMarkerRenameStop
/-- The retained group and replay associated with every selectable marker
of a native interruption. The keeper payload is already fully synced. -/
def NativeMarkerCutReplay (current : NativeReadPosition history log)
    (prepared : NativeReadyWritePreparation current.state) (files : FileImage) : Prop :=
  ∀ pair ∈ files.directory.active :: files.directory.crashImages,
  ∃ retained : List WAL.Write, (retained = [] ∨ retained = prepared.batch) ∧
    pair.walBoundary = some (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64) ∧
    SelectedIntegrityCheckpoint current.state.writer.published.durable pair.manifest current.state.writer.checkpoint ∧
    selectRetained current.state.writer.wal.active.first (WAL.encode (history ++ retained)).size.toUInt64
      (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch) =
      .ok (WAL.encode ((history ++ retained).drop current.state.writer.wal.active.first)) ∧
    PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads (history ++ retained) ∧
    ∀ read ∈ current.reads, read.BoundedBy (history ++ retained).length

theorem NativeReadPosition.replaysMarkerCut (current : NativeReadPosition history log)
    (prepared : NativeReadyWritePreparation current.state) (cut : MarkerInterruption) {files : FileImage}
    (projected : BatchCutProjection files (prepared.modeledMarkerCut cut))
    (keeper : files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)) :
    NativeMarkerCutReplay current prepared files := by
  obtain ⟨valid, exactHistory, prior⟩ := current.readPrefix.refines
  intro pair choice
  have bytes : some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∈
      files.keeper.active :: files.keeper.crashImages := keeper ▸ List.mem_cons_self ..
  obtain ⟨chosen, allowed, marker, checkpoint, selected, ordered⟩ := prepared.selectsMarkerCut valid cut projected choice bytes
  have historyChoice : chosen = history ∨ chosen = history ++ prepared.batch :=
    allowed.imp (·.trans exactHistory) (·.trans (congrArg (· ++ prepared.batch) exactHistory))
  obtain ⟨replayed, bounded⟩ := prior.appendUncertain current.readPrefix.readsBounded historyChoice ordered
  rcases historyChoice with same | same
  · subst chosen
    exact ⟨[], .inl rfl, by simpa only [List.append_nil] using marker, checkpoint,
      by simpa only [List.append_nil] using selected, by simpa only [List.append_nil] using replayed,
      by simpa only [List.append_nil] using bounded⟩
  · subst chosen
    exact ⟨prepared.batch, .inr rfl, marker, checkpoint, selected, replayed, bounded⟩

/-- The new marker is strictly beyond the old committed count because
preflight has accepted a nonempty batch without overflowing the count. -/
theorem NativeMarkerCutReplay.wholeAt {current : NativeReadPosition history log}
    {prepared : NativeReadyWritePreparation current.state} {files : FileImage}
    (replay : NativeMarkerCutReplay current prepared files)
    {pair : DirectoryPublication.Bindings} (choice : pair ∈ files.directory.active :: files.directory.crashImages)
    (published : pair.walBoundary = some prepared.marker) :
    PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads (history ++ prepared.batch) ∧
    ∀ read ∈ current.reads, read.BoundedBy (history ++ prepared.batch).length := by
  obtain ⟨retained, allowed, marker, _, _, pending, bounded⟩ := replay pair choice
  rcases allowed with rfl | rfl
  · obtain ⟨valid, exactHistory, _⟩ := current.readPrefix.refines
    have oldBytes := valid.retained.resumed.bytes.trans (congrArg (fun events => (WAL.encode events).size) exactHistory)
    have rows : 0 < prepared.rows.length := Nat.pos_of_ne_zero (prepared.nonempty ∘ List.length_eq_zero_iff.mp)
    have appended := Nat.mul_pos (by decide : 0 < WAL.frameSize) rows
    have fits : prepared.count < UInt64.size := prepared.fits
    have earlier : (WAL.encode history).size < prepared.count := by
      dsimp only [NativeReadyWritePreparation.count]
      omega
    simp only [List.append_nil] at marker
    have equal := congrArg WAL.Boundary.decode (Option.some.inj (published.symm.trans marker))
    simp only [NativeReadyWritePreparation.marker, WAL.Boundary.decode_encode, Except.ok.injEq] at equal
    have counts := congrArg UInt64.toNat equal
    change (UInt64.ofNat prepared.count).toNat = (UInt64.ofNat (WAL.encode history).size).toNat at counts
    rw [UInt64.toNat_ofNat_of_lt' fits, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans earlier fits)] at counts
    omega
  · exact ⟨pending, bounded⟩

/-- The terminal rename observation keeps the selected file alternatives
and every prior read, with one uncertain submission in either outcome. -/
structure NativePendingMarkerRename (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteMarkerRenameStop prepared) : Prop where
  stopped : stop.run = .error (prepared.stagedPath, prepared.markerPath)
    (.poisoned, ⟨(stop.synced.appendCache, stop.reached), current.state.files.owners⟩)
  phase : stop.session.phase = .poisoned
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  custody : stop.Custody
  pending : stop.synced.appendCache.pending = []
  active : stop.synced.appendCache.active = some (prepared.keeperPath, stop.synced.keeperHandle)
  directory : stop.synced.appendCache.directory = some (stop.synced.directoryCapture, current.state.directorySlot, 0)
  livePair : stop.files.directory.active = (if stop.applied then stop.newPair else current.state.writer.target.pair)
  crashPairs : stop.files.directory.crashImages =
    (if stop.applied then [stop.newPair, current.state.writer.target.pair] else [current.state.writer.target.pair])
  scratch : stop.files.directory.staged .walBoundary = (if stop.applied then none else some (prepared.marker, true))
  keeper : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  durableKeeper : stop.files.keeper.crashImages = [stop.files.keeper.active]
  seals : stop.files.kept = current.state.files.image.kept
  later : stop.files.later = current.state.files.image.later
  selections : NativeMarkerCutReplay current prepared stop.files

theorem NativeReadPosition.stopsAtMarkerRename (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteMarkerRenameStop prepared) :
    NativePendingMarkerRename current stop := by
  let valid := current.readPrefix.refines.1
  obtain ⟨live, crash, scratch, keeper, durable⟩ := stop.choices valid
  refine ⟨stop.stopsWrite valid, rfl, valid.retained.held, stop.custody valid, stop.synced.pendingEmpty, rfl,
    stop.synced.directoryCached, live, crash, scratch, keeper, durable, rfl, rfl, ?_⟩
  exact current.replaysMarkerCut prepared stop.cut (stop.batchCut valid) keeper

end Alvoki.Storage.DiskSession
