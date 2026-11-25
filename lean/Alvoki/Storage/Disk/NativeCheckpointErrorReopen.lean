import Alvoki.Storage.Disk.NativeCheckpointDirectoryError
import Alvoki.Storage.Disk.NativeMarkedReadPrefix
import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.ClientCachedClose
import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WalSegmentRepair (FileImage Prepared)
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

namespace NativeCheckpointDirectoryError

def closeState (report : NativeCheckpointDirectoryError (image := image) state cut) :
    CachedCloseState CheckpointOpenHandle image :=
  ⟨.poisoned, ⟨(state.cache, report.after), state.files.owners⟩, report.callbackPrefix.descriptors report.after⟩

variable {report : NativeCheckpointDirectoryError (image := image) state cut}

namespace Physical

def released (physical : report.Physical) : LockedFileState FileImage :=
  ⟨physical.files report.after, state.files.owners.set (state.session.directory.file .lock) none⟩

theorem vacant (physical : report.Physical) :
    TryLockObserves physical.released.owners state.session.directory (.ok true) := by
  intro _
  simp [released, LockOwners.set]

noncomputable def publication (physical : report.Physical) : Image :=
  ⟨(physical.files report.after).directory.project .manifest, (physical.runs report.after).guaranteed⟩

/-- The returned physical image is the retained WAL with the manifest
publication seen at the error. This equality includes the joint
directory choices and both staging fields. -/
theorem fileProjection (physical : report.Physical) (valid : state.Valid) :
    physical.released.image = CheckpointPowerCut.physical state.writer physical.publication := by
  let actual := (physical.files report.after).directory
  let modeled := (physical.publication.segmentedCheckpointView state.writer.wal).directory
  let old := state.writer.wal.directory.active
  let new := old.replace .manifest cut.checkpoint.manifest
  have marker := congrArg CheckpointWalView.stagedMarker physical.wal
  change actual.staged .walBoundary = state.writer.files.directory.staged .walBoundary at marker
  rw [valid.retained.directoryFiles] at marker
  obtain ⟨active, choices⟩ := physical.directory valid
  have activeEq : actual.active = modeled.active := by
    change actual.active = ⟨actual.active.manifest, old.walBoundary⟩
    rw [show actual.active = new from active]
    rfl
  have choicesEq : actual.crashImages = modeled.crashImages := by
    change actual.crashImages =
      (actual.crashImages.map (·.get .manifest)).map (fun binding => ⟨binding, old.walBoundary⟩)
    rw [show actual.crashImages = if cut.tookEffect then [new] else [new, old] from choices]
    cases cut.tookEffect with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]; rfl
    | true => rfl
  have stagesEq : actual.staged = modeled.staged := by
    funext entry
    cases entry with
    | manifest => rfl
    | walBoundary => exact marker
  have equal (left right : DirectoryPublication.Image) (active : left.active = right.active)
      (crashes : left.crashImages = right.crashImages) (staged : left.staged = right.staged) :
      left = right := by
    cases left
    cases right
    simp_all
  have dirEq := equal actual modeled activeEq choicesEq stagesEq
  have kept := congrArg CheckpointWalView.kept physical.wal
  have keeper := congrArg CheckpointWalView.keeper physical.wal
  have later := congrArg CheckpointWalView.later physical.wal
  change (physical.files report.after).kept = state.writer.files.kept at kept
  change (physical.files report.after).keeper = state.writer.files.keeper at keeper
  change (physical.files report.after).later = state.writer.files.later at later
  change (⟨actual, _, _, _⟩ : FileImage) = ⟨modeled, _, _, _⟩
  rw [dirEq, kept, keeper, later]

/-- The direct retry reads the live renamed manifest. Its recovery plan
and exact durable checkpoint are obtained before the next open reports. -/
structure LiveRetry (physical : report.Physical) where
  layout : CanonicalKeeperLayout physical.released.image state.writer.history
  keeper : layout.keeper = state.writer.wal.active
  aligned : layout.tail = ByteArray.empty
  descriptors : layout.sealed ++ [layout.keeper] =
    (physical.publication.segmentedCheckpointView state.writer.wal).readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, ((physical.publication.segmentedCheckpointView state.writer.wal).readDescriptors
      layout.range.watermark).map WalSegment.first)
  prepared : Prepared physical.released.image layout.target layout.plan
  checkpoint : Option (PackedTable × UInt64)
  selected : SelectedIntegrityCheckpoint physical.publication.durable physical.released.image.directory.active.manifest checkpoint
  generation : (checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation state.writer
  manifest : physical.released.image.directory.active.manifest = some cut.checkpoint.manifest
  accepted : physical.publication.AcceptsVersioned state.writer.history.length.toUInt64
    (CheckpointRepresentsPrefix state.writer.history) physical.released.image.directory.active.manifest
  walLayout : (physical.publication.segmentedCheckpointView state.writer.wal).ReadLayout state.writer.history
  walValid : (physical.publication.segmentedCheckpointView state.writer.wal).Valid state.writer.history

theorem liveRetry (physical : report.Physical) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history) :
    Nonempty physical.LiveRetry := by
  let current := physical.publication
  let wal := current.segmentedCheckpointView state.writer.wal
  obtain ⟨model, reached⟩ := physical.selects valid
  obtain ⟨other, executed, oldLayout, oldValid, oldInputs, _⟩ := cut.selectsAcknowledgedHistory valid.retained
  have sameModel := Option.some.inj (executed.symm.trans reached.executed)
  subst other
  obtain ⟨active, choices⟩ := physical.directory valid
  have visible : current.manifest.active = some cut.checkpoint.manifest :=
    congrArg DirectoryPublication.Bindings.manifest active
  have oldActive : (model.segmentedCheckpointView state.writer.wal).directory.active = wal.directory.active := by
    change DirectoryPublication.Bindings.mk model.manifest.active _ = DirectoryPublication.Bindings.mk current.manifest.active _
    rw [reached.liveManifest, visible]
  have candidates : current.manifest.crashImages = model.manifest.crashImages := by
    simp only [current, publication, DirectoryPublication.Image.project, choices, reached.manifestChoices]
    cases cut.tookEffect <;> rfl
  have sameChoices : (model.segmentedCheckpointView state.writer.wal).directory.crashImages = wal.directory.crashImages := by
    change model.manifest.crashImages.map _ = current.manifest.crashImages.map _
    rw [candidates]
  have chosen (pair) (here : wal.Selects pair) : (model.segmentedCheckpointView state.writer.wal).Selects pair := by
    change pair ∈ (model.segmentedCheckpointView state.writer.wal).directory.active ::
      (model.segmentedCheckpointView state.writer.wal).directory.crashImages
    rw [oldActive, sameChoices]
    exact here
  have walValid : wal.Valid state.writer.history := fun pair here => oldValid pair (chosen pair here)
  have inputs (pair) (here : wal.Selects pair) :
      current.AcceptsVersioned state.writer.history.length.toUInt64 (CheckpointRepresentsPrefix state.writer.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = state.writer.history.length := by
    obtain ⟨accepted, range, decoded, through⟩ := oldInputs pair (chosen pair here)
    have binding : pair.manifest = state.writer.wal.directory.active.manifest ∨ pair.manifest = some cut.checkpoint.manifest := by
      rcases List.mem_cons.mp (chosen pair here) with rfl | survived
      · exact .inr reached.liveManifest
      · obtain ⟨manifest, name, rfl⟩ := List.mem_map.mp survived
        rw [reached.manifestChoices] at name
        split at name
        · exact .inr (List.mem_singleton.mp name)
        · rcases List.mem_cons.mp name with fresh | prior
          · exact .inr fresh
          · exact .inl (List.mem_singleton.mp prior)
    have runs := cut.selectedRunAgreement valid.retained model pair.manifest binding
      (physical.runs report.after).guaranteed reached.newRuns reached.priorRuns
    exact ⟨SelectedRunsAgree.acceptsVersioned (actual := current) runs decoded accepted, range, decoded, through⟩
  have exactFiles : physical.released.image = wal.checkpointReopenFiles wal.directory state.writer.files.keeper.staged :=
    (physical.fileProjection valid).trans (CheckpointPowerCut.physical_eq current valid.retained)
  have walLayout : wal.ReadLayout state.writer.history :=
    ⟨oldLayout.ordered, oldLayout.forward, oldLayout.activeEnd, oldLayout.activeBytes⟩
  obtain ⟨layout, _, keeper, aligned, descriptors, offsets, prepared, _, accepted⟩ :=
    current.checkpointRetryLayout (before := state.writer.wal) walLayout walValid .visible inputs
      (current := physical.released.image) (scratch := state.writer.files.keeper.staged)
      (exactFiles.symm ▸ .before .live)
  have survives : some cut.checkpoint.manifest ∈ current.manifest.crashImages := by
    rw [candidates, reached.manifestChoices]
    cases cut.tookEffect <;> simp
  have bound : physical.released.image.directory.active.manifest = some cut.checkpoint.manifest := visible
  obtain ⟨_, checkpoint, _, _, selected, generation, _⟩ := reached.replaysPending valid.retained pending survives
  have generationEq : (checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation state.writer := by
    rcases generation with ⟨_, same⟩ | ⟨generation, _⟩
    · exact False.elim (cut.manifestChanges valid.retained same.symm)
    · exact generation
  exact ⟨⟨layout, keeper, aligned, descriptors, offsets, prepared, checkpoint, bound.symm ▸ selected,
    generationEq, bound, accepted, walLayout, walValid⟩⟩

end Physical

end NativeCheckpointDirectoryError
/-- Pathnames use the binding view already captured at the error.
These are the payload reports for the reached, still-live names. -/
structure NativeCheckpointCloseFiles {report : NativeCheckpointDirectoryError (image := image) state cut}
    (physical : report.Physical) where
  bytes : Nat → Option ByteArray
  manifest : ∃ inode, report.bindings report.after (state.session.directory.file .manifest) = some inode ∧
    bytes inode = some cut.checkpoint.manifest
  marker : ∀ payload, state.writer.wal.directory.active.walBoundary = some payload →
    ∃ inode, report.bindings report.after (state.session.directory.file .walBoundary) = some inode ∧
      bytes inode = some payload
  wal : ∀ segment ∈ state.writer.wal.segments,
    ∃ inode, report.bindings report.after (state.session.directory.file (.walSegment segment.first)) = some inode ∧
      bytes inode = some segment.bytes
  runs : ∀ metadata, Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    physical.publication.durable metadata.header.generation index = some payload →
      ∃ inode, report.bindings report.after (state.session.directory.file (.run metadata.header.generation index)) =
        some inode ∧ bytes inode = some payload

/-- The next held open follows the actual clear/unlock census. Its child
lookups use the stable names observed at the final checkpoint error. -/
structure NativeCheckpointAlignedReads
    {report : NativeCheckpointDirectoryError (image := image) state cut} {physical : report.Physical}
    (files : NativeCheckpointCloseFiles physical) (input : FilePath) (inventory : DescriptorInventory)
    (plan : physical.LiveRetry) where
  opening : CheckpointBarrierAlignedReports input state.session.directory inventory physical.released plan.layout
    physical.publication physical.vacant plan.selected (report.bindings report.after)
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  directoryObject : opening.reads.bindings state.session.directory.path = report.bindings report.after state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) =
    report.bindings report.after (state.session.directory.file .lock)
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeCheckpointAlignedReads

variable {report : NativeCheckpointDirectoryError (image := image) state cut} {physical : report.Physical}
  {files : NativeCheckpointCloseFiles physical} {input : FilePath} {inventory : DescriptorInventory}
  {plan : physical.LiveRetry}

noncomputable def run (seen : NativeCheckpointAlignedReads files input inventory plan) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def ReadsOriginal (seen : NativeCheckpointAlignedReads files input inventory plan)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    report.bindings report.after path = some read.object ∧ files.bytes read.object = some payload

private theorem readsFile (seen : NativeCheckpointAlignedReads files input inventory plan)
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (same : CheckpointCrashChild (report.bindings report.after) seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some child)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view)
    (original : ∃ inode, report.bindings report.after path = some inode ∧ files.bytes inode = some payload) :
    seen.ReadsOriginal path payload := by
  obtain ⟨inode, named, bytes⟩ := original
  let read := calls.observesFile bound contents
  have identified : report.bindings report.after path = some read.object := same.sameObject calls bound contents
  exact ⟨read, identified, (Option.some.inj (identified.symm.trans named)).symm ▸ bytes⟩

/-- The next successful open reads the live manifest, its exact ordered
run payloads and the original marker and selected WAL payloads. -/
structure SelectedReads (seen : NativeCheckpointAlignedReads files input inventory plan) : Prop where
  manifest : seen.ReadsOriginal (state.session.directory.file .manifest) cut.checkpoint.manifest
  runs : ∀ metadata, Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    physical.publication.durable metadata.header.generation index = some payload →
      seen.ReadsOriginal (state.session.directory.file (.run metadata.header.generation index)) payload
  marker : seen.ReadsOriginal (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  wal : ∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
    seen.ReadsOriginal (state.session.directory.file (.walSegment segment.first)) segment.bytes

theorem readsSelected (seen : NativeCheckpointAlignedReads files input inventory plan) (valid : state.Valid) :
    seen.SelectedReads := by
  let opening := seen.opening
  obtain ⟨⟨manifest⟩, _⟩ := opening.reads.metadata.manifestFile _ plan.manifest
  have marker : state.writer.wal.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    have marker := congrArg Publication.Image.active valid.retained.resumed.markerImage
    change state.writer.files.directory.active.walBoundary = _ at marker
    rw [valid.retained.directoryFiles] at marker
    exact marker
  have retryMarker : physical.released.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    change (physical.files report.after).directory.active.walBoundary = _
    rw [(physical.directory valid).1]
    exact marker
  obtain ⟨boundary, _⟩ := opening.reads.metadata.markerFile _ retryMarker
  refine ⟨seen.readsFile opening.manifestChild manifest.bound manifest.contents manifest.calls files.manifest, ?_,
    seen.readsFile opening.markerChild boundary.bound boundary.contents boundary.calls (files.marker _ marker), ?_⟩
  · intro metadata decoded index inside payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := opening.reads.runs _ metadata plan.manifest decoded index inside payload stored
    exact seen.readsFile (opening.runChild _ metadata plan.manifest decoded index inside) bound contents calls
      (files.runs metadata decoded index inside payload stored)
  · intro segment appears
    have saved : segment ∈ state.writer.wal.segments := by
      rw [plan.descriptors, WalSegmentImage.readDescriptors] at appears
      split at appears
      · exact (List.mem_filter.mp appears).1
      · exact List.mem_append_right _ appears
    have original := files.wal segment saved
    rcases List.mem_append.mp appears with sealed | last
    · let file := opening.reads.wal.sealedFile segment sealed
      exact seen.readsFile (opening.sealChild segment sealed) file.bound file.contents file.calls original
    · obtain rfl := List.mem_singleton.mp last
      let file := opening.reads.wal.keeper
      have contents : opening.reads.reads.objectBytes (opening.admission.view.modelObject file.object) =
          some plan.layout.keeper.bytes := by simpa only [plan.aligned, ByteArray.append_empty] using file.contents
      exact seen.readsFile opening.keeperChild file.bound contents file.calls original

end NativeCheckpointAlignedReads

/-- An ordinary close releases a poisoned checkpoint's original lock and
hands its reached census and live files to a direct aligned open. The
returned session selects the new generation and retains the prior client
ledger. A later power loss would instead use the reported crash choices. -/
theorem NativeReadyReadPrefix.reopensCheckpointDirectoryError
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial : NativeReadyState}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (report : NativeCheckpointDirectoryError (image := image) state cut) (physical : report.Physical)
    (close : CachedCloseReports state.session.directory state.session.descriptor report.closeState)
    (owner : close.slot = state.owner) (closed : close.result = .ok ()) (files : NativeCheckpointCloseFiles physical)
    {input : FilePath}
    (observe : ∀ plan : physical.LiveRetry, Nonempty (NativeCheckpointAlignedReads files input close.finished.descriptors plan)) :
    report.run = .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) ∧
    close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
    close.finished.files = ⟨(⟨none, none, []⟩, report.after), physical.released.owners⟩ ∧
    close.finished.descriptors = state.census.afterDrops (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    close.bindings (state.session.directory.file .lock) = report.bindings report.after (state.session.directory.file .lock) ∧
    ∃ (plan : physical.LiveRetry) (seen : NativeCheckpointAlignedReads files input close.finished.descriptors plan)
      (next : NativeReadyState),
      NativeReadyReadPrefix seen.run next history log reads next ∧
      next.session.directory = state.session.directory ∧ next.owner = seen.opening.admission.owner ∧
      next.directorySlot = seen.opening.admission.cached ∧ next.cache = seen.opening.admission.cache ∧
      next.census = seen.opening.finish.census ∧
      next.session.sessionRef ≠ state.session.sessionRef ∧ next.session.phaseRef ≠ state.session.phaseRef ∧
      next.census.inode next.owner.description = state.census.inode state.owner.description ∧
      next.census.inode next.directorySlot.description = state.census.inode state.directorySlot.description ∧
      next.files.image.directory.active = physical.released.image.directory.active ∧
      next.files.image.kept = state.files.image.kept ∧
      next.writer.target = plan.layout.target ∧ next.writer.checkpoint = plan.checkpoint ∧
      next.writer.published.durable = physical.publication.durable ∧
      next.writer.installed.generation = SegmentedCheckpointReport.generation state.writer ∧
      seen.SelectedReads ∧ InstalledClientReplay log reads history next.writer.installed next.session := by
  obtain ⟨valid, exactHistory, pending⟩ := prior.refines
  have ready := valid.retained
  have held := (report.custody valid).2 report.after (by simp)
  have heldPaths := report.heldBindings report.after (by simp)
  have closeReached := close.reaches (by simp [NativeCheckpointDirectoryError.closeState]) ready.held
  rw [CachedCloseReports.Reached, closed] at closeReached
  obtain ⟨finished, phase, cleared, closeCensus, _⟩ := closeReached
  have closeLock : close.bindings (state.session.directory.file .lock) =
      report.bindings report.after (state.session.directory.file .lock) := by
    rw [close.lockObject, owner, show report.closeState.descriptors = state.census from held.1, heldPaths.2]
  obtain ⟨plan⟩ := physical.liveRetry valid (exactHistory.symm ▸ pending)
  obtain ⟨seen⟩ := observe plan
  let opening := seen.opening
  let finish : CapturedKeeperFinish opening.callbacks opening.reads physical.vacant plan.selected := .aligned opening.finish
  let wal := physical.publication.segmentedCheckpointView state.writer.wal
  have sameFiles := physical.fileProjection valid
  have pair : wal.directory.active = plan.layout.target.pair :=
    (congrArg (fun view : FileImage => view.directory.active) sameFiles).symm.trans plan.prepared.pair
  have kept : physical.released.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := by
    have exactFiles := sameFiles.trans (CheckpointPowerCut.physical_eq physical.publication ready)
    have sameKept := congrArg FileImage.kept exactFiles
    exact sameKept
  have following := opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  obtain ⟨next, seeded, nextCache, nextCensus, nextOwner, nextDirectory, nextPair, nextRuns,
    nextCheckpoint, nextPath, nextTarget, nextKept, phaseFresh, sessionFresh⟩ :=
    finish.startsNativeReadPrefix seen.chronology opening.markerFound plan.prepared following plan.accepted
      ready.resumed.ordered plan.walLayout plan.walValid ready.spans pair (congrArg WalSegment.first plan.keeper) kept
      (exactHistory.symm ▸ pending) (exactHistory.symm ▸ prior.readsBounded)
  have continued : NativeReadyReadPrefix seen.run next history log reads next := exactHistory ▸ seeded
  have inventoryInodes : next.census.inode = opening.admission.reached.inode := by
    change next.census = opening.finish.census at nextCensus
    rw [nextCensus]
    change (opening.finish.authorization.keeper.inventory.afterDrops
      (opening.finish.repair.beforeAuthorization ++ opening.finish.repair.afterAuthorization ++ opening.finish.afterKeeper)).inode = _
    rw [opening.finish.repair.opened]
    rfl
  have objects := opening.reads.sameObjects
  have sameLock := Option.some.inj (objects.2.1.symm.trans (seen.lockObject.trans heldPaths.2))
  have sameDirectory := Option.some.inj (objects.1.symm.trans (seen.directoryObject.trans heldPaths.1))
  have generation : next.writer.installed.generation = SegmentedCheckpointReport.generation state.writer :=
    continued.refines.1.retained.resumed.generation.trans ((congrArg (fun cp => (cp.getD (.empty, 0)).2) nextCheckpoint).trans plan.generation)
  refine ⟨report.returns valid, finished, phase, cleared, held.1 ▸ closeCensus, closeLock, plan, seen, next, continued,
    nextPath, nextOwner, nextDirectory, nextCache, nextCensus, fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2),
    fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1), ?_, ?_, nextPair, ?_, nextTarget, nextCheckpoint,
    nextRuns, generation, seen.readsSelected valid, continued.guardedReplay⟩
  · rw [inventoryInodes, nextOwner]
    exact sameLock
  · rw [inventoryInodes, nextDirectory]
    exact sameDirectory
  · exact nextKept.trans (congrArg CheckpointWalView.kept physical.wal)

/-- Reports for the final checkpoint failure, successful explicit close,
and direct aligned open on the selected live checkpoint files. -/
structure NativeCheckpointReopenObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  reported : NativeCheckpointDirectoryError (image := image) state cut
  physical : reported.Physical
  close : CachedCloseReports state.session.directory state.session.descriptor reported.closeState
  owner : close.slot = state.owner
  closed : close.result = .ok ()
  files : NativeCheckpointCloseFiles physical
  reopen : ∀ plan : physical.LiveRetry, Nonempty (NativeCheckpointAlignedReads files input close.finished.descriptors plan)

def NativeCheckpointReopenObservation.diagnostic {input : FilePath}
    (observed : NativeCheckpointReopenObservation state input) : IO.Error :=
  observed.reported.error

/-- One execution continuation through the returned checkpoint error and
the two subsequent calls. The new ready position starts at the actual
returned open and carries the same ledger. -/
structure NativeCheckpointReopenContinuation (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCheckpointReopenObservation current.state input) (next : NativeReadPosition history log) : Prop where
  returned : observed.reported.run = .error observed.diagnostic
    (.poisoned, ⟨(current.state.cache, observed.reported.after), current.state.files.owners⟩)
  closed : observed.close.run = .ok () observed.close.finished ∧ observed.close.finished.phase = .closed ∧
    observed.close.finished.files =
      ⟨(⟨none, none, []⟩, observed.reported.after), observed.physical.released.owners⟩ ∧
    observed.close.finished.descriptors = current.state.census.afterDrops
      (observed.close.drops .active ++ observed.close.drops .pending ++ observed.close.drops .directory) ∧
    observed.close.bindings (current.state.session.directory.file .lock) =
      observed.reported.bindings observed.reported.after (current.state.session.directory.file .lock)
  reads : next.reads = current.reads
  directory : next.state.session.directory = current.state.session.directory
  directoryInode : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  lockInode : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  generation : next.state.writer.installed.generation = SegmentedCheckpointReport.generation current.state.writer
  pair : next.state.files.image.directory.active = observed.physical.released.image.directory.active
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : observed.physical.LiveRetry)
    (seen : NativeCheckpointAlignedReads observed.files input observed.close.finished.descriptors plan),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    next.state.writer.target = plan.layout.target ∧ next.state.writer.checkpoint = plan.checkpoint ∧
    next.state.writer.published.durable = observed.physical.publication.durable ∧ seen.SelectedReads
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.recoversCheckpointDirectoryError (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCheckpointReopenObservation current.state input) :
    ∃ next, NativeCheckpointReopenContinuation current observed next := by
  obtain ⟨returned, closed, phase, cleared, closeCensus, closeLock, plan, seen, state, readyPrefix, directory, owner,
    directorySlot, cache, census, sessionFresh, phaseFresh, lockInode, directoryInode, pair, seals, target, checkpoint,
    durable, generation, selected, replay⟩ := current.readPrefix.reopensCheckpointDirectoryError
      observed.reported observed.physical observed.close observed.owner observed.closed observed.files observed.reopen
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, readyPrefix⟩
  exact ⟨next, returned, ⟨closed, phase, cleared, closeCensus, closeLock⟩, rfl, directory, directoryInode, lockInode,
    phaseFresh, sessionFresh, generation, pair, seals,
    ⟨plan, seen, readyPrefix.frames.1, rfl, rfl, owner, directorySlot, cache, census, target, checkpoint, durable, selected⟩, replay⟩

end Alvoki.Storage.DiskSession
