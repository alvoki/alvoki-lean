import Alvoki.Storage.Disk.NativeCheckpointErrorReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WalSegmentRepair (FileImage Prepared)
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {barrier : NativeCheckpointFinalBarrier (image := image) state cut} {after : image}
  {physical : barrier.Physical after}

/-- An actual power-loss report from the reached checkpoint barrier.
One joint directory choice fixes the surviving manifest and marker.
The inode observations link that choice to the reached namespace and
the corresponding before-rename or renamed manifest binding. -/
structure NativeCheckpointCrashFiles (physical : barrier.Physical after) where
  pair : DirectoryPublication.Bindings
  chosen : pair ∈ (physical.files after).directory.crashImages
  keeper : Option ByteArray
  keeperSurvived : keeper ∈ (physical.files after).keeper.crashImages
  later : List Nat
  laterSurvived : later ∈ (physical.files after).later.crashImages
  names : FilePath → Option Nat
  contents : Nat → ByteArray
  directory : names state.session.directory.path = barrier.bindings after state.session.directory.path
  lock : names (state.session.directory.file .lock) = barrier.bindings after (state.session.directory.file .lock)
  manifest : names (state.session.directory.file .manifest) =
    if pair.manifest = some cut.checkpoint.manifest then barrier.bindings after (state.session.directory.file .manifest)
    else barrier.bindings barrier.observed.runsSettled.2 (state.session.directory.file .manifest)
  manifestBytes : (names (state.session.directory.file .manifest)).map contents = pair.manifest
  marker : ∀ payload, pair.walBoundary = some payload →
    ∃ inode, barrier.bindings after (state.session.directory.file .walBoundary) = some inode ∧
      names (state.session.directory.file .walBoundary) = some inode ∧ contents inode = payload
  wal : ∀ segment ∈ state.writer.wal.segments,
    ∃ inode, barrier.bindings after (state.session.directory.file (.walSegment segment.first)) = some inode ∧
      names (state.session.directory.file (.walSegment segment.first)) = some inode ∧ contents inode = segment.bytes
  runs : ∀ manifest metadata, pair.manifest = some manifest →
    Manifest.IntegrityCheckpoint.decode manifest = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    physical.publication.durable metadata.header.generation index = some payload →
      ∃ inode, barrier.bindings after (state.session.directory.file (.run metadata.header.generation index)) =
        some inode ∧ names (state.session.directory.file (.run metadata.header.generation index)) = some inode ∧
        contents inode = payload
  rebootObjects : Nat → Nat

namespace NativeCheckpointCrashFiles

def reboot (crash : NativeCheckpointCrashFiles physical) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

def retry (crash : NativeCheckpointCrashFiles physical) : LockedFileState FileImage :=
  ⟨(physical.files after).crash crash.pair crash.keeper crash.later, state.files.owners.set (state.session.directory.file .lock) none⟩

theorem vacant (crash : NativeCheckpointCrashFiles physical) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) :=
  by
    intro _
    simp [retry, LockOwners.set]

theorem losesPower (crash : NativeCheckpointCrashFiles physical) :
    BoundedReopenTrace state.session.directory (CheckpointRetryTarget state.writer.history state.writer.wal.active.first)
      ⟨physical.files after, state.files.owners⟩ crash.retry :=
  .powerLoss .empty crash.chosen crash.keeperSurvived crash.laterSurvived

theorem classification (crash : NativeCheckpointCrashFiles physical) (valid : state.Valid) :
    crash.pair.walBoundary = state.writer.wal.directory.active.walBoundary ∧
    (cut.tookEffect = true → crash.pair.manifest = some cut.checkpoint.manifest) ∧
    (crash.pair.manifest = state.writer.wal.directory.active.manifest ∨ crash.pair.manifest = some cut.checkpoint.manifest) := by
  have choices := (physical.directory valid).2
  have chosen := crash.chosen
  rw [choices] at chosen
  cases effect : cut.tookEffect with
  | false =>
    rw [effect] at chosen
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at chosen
    rcases chosen with fresh | prior
    · exact ⟨(congrArg DirectoryPublication.Bindings.walBoundary fresh).trans rfl, by simp,
        .inr (congrArg DirectoryPublication.Bindings.manifest fresh)⟩
    · exact ⟨congrArg DirectoryPublication.Bindings.walBoundary prior, by simp,
        .inl (congrArg DirectoryPublication.Bindings.manifest prior)⟩
  | true =>
    rw [effect] at chosen
    have fresh := List.mem_singleton.mp chosen
    have manifest := congrArg DirectoryPublication.Bindings.manifest fresh
    exact ⟨(congrArg DirectoryPublication.Bindings.walBoundary fresh).trans rfl, fun _ => manifest, .inr manifest⟩

theorem chosenPublication (crash : NativeCheckpointCrashFiles physical) (valid : state.Valid) :
    crash.pair ∈ (physical.publication.segmentedCheckpointView state.writer.wal).directory.crashImages := by
  have same := congrArg (fun files : FileImage => files.directory.crashImages) (physical.fileProjection valid)
  exact same ▸ crash.chosen

/-- The next reader uses the chosen directory binding with the same WAL
segments. The selected layout remains valid at the reboot image. -/
noncomputable def rebootWal (crash : NativeCheckpointCrashFiles physical) : WalSegmentImage :=
  { physical.publication.segmentedCheckpointView state.writer.wal with directory := .settled crash.pair }

theorem rebootWalSupport (crash : NativeCheckpointCrashFiles physical) (valid : state.Valid) :
    crash.rebootWal.ReadLayout state.writer.history ∧ crash.rebootWal.Valid state.writer.history := by
  obtain ⟨layout, retained, _⟩ := physical.retrySupport valid
  refine ⟨⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩, ?_⟩
  intro pair selected
  change pair ∈ [crash.pair, crash.pair] at selected
  have same : pair = crash.pair := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using selected
  cases same
  exact retained _ (List.mem_cons_of_mem _ (crash.chosenPublication valid))

/-- The chosen old or new manifest and the retained run bytes determine
the retry plan before obtaining any healthy-open reports. -/
structure Plan (crash : NativeCheckpointCrashFiles physical) where
  layout : CanonicalKeeperLayout crash.retry.image state.writer.history
  keeper : layout.keeper = state.writer.wal.active
  aligned : layout.tail = ByteArray.empty
  descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.retry.image layout.target layout.plan
  checkpoint : Option (PackedTable × UInt64)
  selected : SelectedIntegrityCheckpoint physical.publication.durable crash.pair.manifest checkpoint
  generation : (((checkpoint.getD (.empty, 0)).2 = state.writer.installed.generation ∧
      crash.pair.manifest = state.writer.wal.directory.active.manifest) ∨
    ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation state.writer ∧
      crash.pair.manifest = some cut.checkpoint.manifest))
  accepted : physical.publication.AcceptsVersioned state.writer.history.length.toUInt64
    (CheckpointRepresentsPrefix state.writer.history) crash.pair.manifest

/-- The settled reboot image keeps the exact pre-existing keeper and
sealed files. Their already-settled choices identify the payloads. -/
theorem reachedFiles (crash : NativeCheckpointCrashFiles physical) (valid : state.Valid) :
    let wal := physical.publication.segmentedCheckpointView state.writer.wal
    crash.retry.image = wal.checkpointReopenFiles (.settled crash.pair) none := by
  intro wal
  let publication := physical.publication
  have physicalFiles : physical.files after = wal.checkpointReopenFiles wal.directory state.writer.files.keeper.staged :=
    (physical.fileProjection valid).trans (CheckpointPowerCut.physical_eq publication valid.retained)
  have keeper : crash.keeper = some wal.active.bytes := by
    have survived := crash.keeperSurvived
    change crash.keeper ∈ (physical.files after).keeper.crashImages at survived
    rw [physicalFiles] at survived
    exact List.mem_singleton.mp survived
  have later : crash.later = [] := by
    have survived := crash.laterSurvived
    change crash.later ∈ (physical.files after).later.crashImages at survived
    rw [physicalFiles] at survived
    exact List.mem_singleton.mp survived
  change (physical.files after).crash crash.pair crash.keeper crash.later = _
  rw [physicalFiles, keeper, later]
  rfl

theorem plans (crash : NativeCheckpointCrashFiles physical) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history) :
    Nonempty crash.Plan := by
  let publication := physical.publication
  let wal := publication.segmentedCheckpointView state.writer.wal
  have selected := crash.chosenPublication valid
  have exactFiles := crash.reachedFiles valid
  obtain ⟨layout, validWal, inputs⟩ := physical.retrySupport valid
  have lineage : WalSegmentRepair.ReopenLineage
      (wal.checkpointReopenFiles (.settled crash.pair) none)
      (CheckpointRetryTarget state.writer.history state.writer.wal.active.first) crash.retry.image :=
    exactFiles.symm ▸ .before .live
  obtain ⟨layout, _, keeper, aligned, descriptors, offsets, prepared, _, accepted⟩ :=
    publication.checkpointRetryLayout layout validWal (.crash selected) inputs lineage
  obtain ⟨_, reached⟩ := physical.selects valid
  have acceptedManifest : crash.pair.manifest ∈ publication.manifest.crashImages := List.mem_map_of_mem crash.chosen
  obtain ⟨_, checkpoint, _, _, reads, generation, _⟩ := reached.replaysPending valid.retained pending acceptedManifest
  exact ⟨⟨layout, keeper, aligned, descriptors, offsets, prepared, checkpoint, reads, generation, accepted⟩⟩

end NativeCheckpointCrashFiles

/-- Primitive admission, ordered reads and aligned repair from the
reported reboot census and selected surviving files. -/
structure NativeCheckpointCrashAlignedReads (crash : NativeCheckpointCrashFiles physical)
    (input : FilePath) (plan : crash.Plan) where
  opening : CheckpointBarrierAlignedReports input state.session.directory crash.reboot crash.retry plan.layout
    physical.publication crash.vacant plan.selected crash.names
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  directoryObject : opening.reads.bindings state.session.directory.path = crash.names state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) = crash.names (state.session.directory.file .lock)
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeCheckpointCrashAlignedReads

variable {crash : NativeCheckpointCrashFiles physical} {input : FilePath} {plan : crash.Plan}

noncomputable def run (seen : NativeCheckpointCrashAlignedReads crash input plan) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def ReadsSurvivor (seen : NativeCheckpointCrashAlignedReads crash input plan)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsFile (seen : NativeCheckpointCrashAlignedReads crash input plan)
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (same : CheckpointCrashChild crash.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some child)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view)
    (survived : ∃ inode, crash.names path = some inode ∧ crash.contents inode = payload) :
    seen.ReadsSurvivor path payload := by
  obtain ⟨inode, named, payload⟩ := survived
  let read := calls.observesFile bound contents
  have observed := same.sameObject calls bound contents
  exact ⟨read, observed, (Option.some.inj (observed.symm.trans named)).symm ▸ payload⟩

/-- The next successful open reads the selected old or new manifest and
its exact ordered payloads. With no prior manifest, the same namespace
and no-follow stat report its absence. -/
structure SelectedReads (seen : NativeCheckpointCrashAlignedReads crash input plan) : Prop where
  manifestAbsent : crash.pair.manifest = none → crash.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message)
  manifest : ∀ bytes, crash.pair.manifest = some bytes → seen.ReadsSurvivor (state.session.directory.file .manifest) bytes
  runs : ∀ manifest metadata, crash.pair.manifest = some manifest →
    Manifest.IntegrityCheckpoint.decode manifest = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    physical.publication.durable metadata.header.generation index = some payload →
      seen.ReadsSurvivor (state.session.directory.file (.run metadata.header.generation index)) payload
  marker : seen.ReadsSurvivor (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  wal : ∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
    seen.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes

theorem readsSelected (seen : NativeCheckpointCrashAlignedReads crash input plan) (valid : state.Valid) :
    seen.SelectedReads := by
  let opening := seen.opening
  have marker : crash.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    have prior := congrArg Publication.Image.active valid.retained.resumed.markerImage
    change state.writer.files.directory.active.walBoundary = _ at prior
    rw [valid.retained.directoryFiles] at prior
    exact (crash.classification valid).1.trans prior
  obtain ⟨boundary, _⟩ := opening.reads.metadata.markerFile _ marker
  obtain ⟨inode, _, named, bytes⟩ := crash.marker _ marker
  refine ⟨?_, ?_, ?_, seen.readsFile opening.markerChild boundary.bound boundary.contents boundary.calls ⟨inode, named, bytes⟩, ?_⟩
  · intro absent
    have map := crash.manifestBytes.trans absent
    have missing : crash.names (state.session.directory.file .manifest) = none := by
      cases bound : crash.names (state.session.directory.file .manifest) <;> simp [bound] at map ⊢
    exact ⟨missing, (opening.reads.metadata.manifestMissing absent).2⟩
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes present
    have named := crash.manifestBytes.trans present
    obtain ⟨inode, binding, contents⟩ := Option.map_eq_some_iff.mp named
    exact seen.readsFile opening.manifestChild file.bound file.contents file.calls ⟨inode, binding, contents⟩
  · intro bytes metadata present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := opening.reads.runs bytes metadata present decoded index within payload stored
    obtain ⟨inode, _, name, value⟩ := crash.runs bytes metadata present decoded index within payload stored
    exact seen.readsFile (opening.runChild bytes metadata present decoded index within) bound contents calls ⟨inode, name, value⟩
  · intro segment appears
    have saved : segment ∈ state.writer.wal.segments := by
      rw [plan.descriptors, WalSegmentImage.readDescriptors] at appears
      split at appears
      · exact (List.mem_filter.mp appears).1
      · exact List.mem_append_right _ appears
    obtain ⟨inode, _, name, value⟩ := crash.wal segment saved
    rcases List.mem_append.mp appears with sealed | last
    · let file := opening.reads.wal.sealedFile segment sealed
      exact seen.readsFile (opening.sealChild segment sealed) file.bound file.contents file.calls ⟨inode, name, value⟩
    · obtain rfl := List.mem_singleton.mp last
      let file := opening.reads.wal.keeper
      have contents : opening.reads.reads.objectBytes (opening.admission.view.modelObject file.object) =
          some plan.layout.keeper.bytes := by simpa only [plan.aligned, ByteArray.append_empty] using file.contents
      exact seen.readsFile opening.keeperChild file.bound contents file.calls ⟨inode, name, value⟩

end NativeCheckpointCrashAlignedReads

/-- The direct aligned reopen of one reported survivor. Returned and
interrupted checkpoint calls use the same proof after power loss. -/
structure NativeCheckpointRebootContinuation (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {barrier : NativeCheckpointFinalBarrier (image := image) current.state cut} {after : image}
    {physical : barrier.Physical after}
    (crash : NativeCheckpointCrashFiles physical) (input : FilePath) (next : NativeReadPosition history log) : Prop where
  lost : BoundedReopenTrace current.state.session.directory
    (CheckpointRetryTarget current.state.writer.history current.state.writer.wal.active.first)
    ⟨physical.files after, current.state.files.owners⟩ crash.retry
  rebooted : crash.reboot.slots = []
  reads : next.reads = current.reads
  directory : next.state.session.directory = current.state.session.directory
  directoryInode : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  lockInode : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  settled : next.state.files.image.directory.active = crash.pair
  effective : cut.tookEffect = true → crash.pair.manifest = some cut.checkpoint.manifest
  generation : (next.state.writer.installed.generation = current.state.writer.installed.generation ∧
      crash.pair.manifest = current.state.writer.wal.directory.active.manifest) ∨
    (next.state.writer.installed.generation = SegmentedCheckpointReport.generation current.state.writer ∧
      crash.pair.manifest = some cut.checkpoint.manifest)
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : crash.Plan) (seen : NativeCheckpointCrashAlignedReads crash input plan),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    next.state.writer.target = plan.layout.target ∧ next.state.writer.checkpoint = plan.checkpoint ∧
    next.state.writer.published.durable = physical.publication.durable ∧ seen.SelectedReads
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.reopensCheckpointSurvivorWith (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {barrier : NativeCheckpointFinalBarrier (image := image) current.state cut} {after : image}
    {physical : barrier.Physical after}
    (crash : NativeCheckpointCrashFiles physical) {input : FilePath}
    (root : barrier.bindings after current.state.session.directory.path =
      some (current.state.census.inode current.state.directorySlot.description))
    (lock : barrier.bindings after (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description))
    {plan : crash.Plan} (seen : NativeCheckpointCrashAlignedReads crash input plan) :
    ∃ next, NativeCheckpointRebootContinuation current crash input next ∧
      seen.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      next.state.cache = seen.opening.admission.cache := by
  obtain ⟨valid, exactHistory, replay⟩ := current.readPrefix.refines
  have ready := valid.retained
  have pending : PendingClientReplay log current.reads current.state.writer.history :=
    Eq.mpr (congrArg (PendingClientReplay log current.reads) exactHistory) replay
  have bounded : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length :=
    Eq.mpr (congrArg (fun rows : List WAL.Write => ∀ read ∈ current.reads, read.BoundedBy rows.length)
      exactHistory) current.readPrefix.readsBounded
  let opening := seen.opening
  let finish : CapturedKeeperFinish opening.callbacks opening.reads crash.vacant plan.selected := .aligned opening.finish
  let rebootWal := crash.rebootWal
  have projected := crash.reachedFiles valid
  obtain ⟨layout, retained⟩ := crash.rebootWalSupport valid
  have kept : crash.retry.image.kept = (rebootWal.checkpointReopenFiles rebootWal.directory none).kept :=
    congrArg FileImage.kept projected
  have pair : rebootWal.directory.active = plan.layout.target.pair := plan.prepared.pair
  have following := opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  obtain ⟨state, seeded, cache, census, owner, directorySlot, settled, runs, checkpoint, directory, target,
    seals, _, _, phaseFresh, sessionFresh⟩ :=
    finish.startsNativeReadPrefix seen.chronology opening.markerFound plan.prepared following plan.accepted
      ready.resumed.ordered layout retained ready.spans pair (congrArg WalSegment.first plan.keeper) kept
      pending bounded
  have continued : NativeReadyReadPrefix seen.run state history log current.reads state :=
    Eq.mp (congrArg (fun rows => NativeReadyReadPrefix seen.run state rows log current.reads state) exactHistory) seeded
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, continued⟩
  have inodes : state.census.inode = opening.admission.reached.inode := by
    change state.census = opening.finish.census at census
    rw [census]
    change (opening.finish.authorization.keeper.inventory.afterDrops
      (opening.finish.repair.beforeAuthorization ++ opening.finish.repair.afterAuthorization ++ opening.finish.afterKeeper)).inode = _
    rw [opening.finish.repair.opened]
    rfl
  have objects := opening.reads.sameObjects
  have generation := continued.refines.1.retained.resumed.generation.trans
    (congrArg (fun cp => (cp.getD (.empty, 0)).2) checkpoint)
  have recoveredSeals : state.files.image.kept = current.state.files.image.kept :=
    seals.trans (congrArg CheckpointWalView.kept physical.wal)
  refine ⟨next, ⟨crash.losesPower, rfl, rfl,
    directory, ?_, ?_, fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2), settled, (crash.classification valid).2.1,
    ?_, recoveredSeals, ⟨plan, seen, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census, target,
      checkpoint, runs, seen.readsSelected valid⟩, continued.guardedReplay⟩,
    rfl, continued.frames.1, owner, directorySlot, cache⟩
  · change state.census.inode state.directorySlot.description = _
    rw [inodes, directorySlot]
    exact Option.some.inj (objects.1.symm.trans (seen.directoryObject.trans (crash.directory.trans root)))
  · change state.census.inode state.owner.description = _
    rw [inodes, owner]
    exact Option.some.inj (objects.2.1.symm.trans (seen.lockObject.trans (crash.lock.trans lock)))
  · exact plan.generation.imp (fun old => ⟨generation.trans old.1, old.2⟩)
      (fun fresh => ⟨generation.trans fresh.1, fresh.2⟩)

theorem NativeReadPosition.reopensCheckpointSurvivor (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {barrier : NativeCheckpointFinalBarrier (image := image) current.state cut} {after : image}
    {physical : barrier.Physical after}
    (crash : NativeCheckpointCrashFiles physical) {input : FilePath}
    (root : barrier.bindings after current.state.session.directory.path =
      some (current.state.census.inode current.state.directorySlot.description))
    (lock : barrier.bindings after (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description))
    (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointCrashAlignedReads crash input plan)) :
    ∃ next, NativeCheckpointRebootContinuation current crash input next := by
  obtain ⟨valid, sameHistory, replay⟩ := current.readPrefix.refines
  have pending : PendingClientReplay log current.reads current.state.writer.history := sameHistory.symm ▸ replay
  obtain ⟨plan⟩ := crash.plans valid pending
  obtain ⟨seen⟩ := observe plan
  obtain ⟨next, reopened, _⟩ := current.reopensCheckpointSurvivorWith crash root lock seen
  exact ⟨next, reopened⟩

/-- The returned-error route supplies the same observed crash files. -/
abbrev NativeCheckpointErrorCrash
    {report : NativeCheckpointDirectoryError (image := image) state cut}
    (physical : report.Physical) :=
  NativeCheckpointCrashFiles (barrier := report.barrier) (after := report.after) physical

namespace NativeCheckpointErrorCrash

export NativeCheckpointCrashFiles (losesPower classification reachedFiles plans)

end NativeCheckpointErrorCrash

/-- Exact native checkpoint error, following power loss and healthy
direct aligned open. The error retains the prior owner up to the crash,
and the newly opened position uses the reported reboot namespace. -/
structure NativeCheckpointCrashContinuation (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointDirectoryError (image := image) current.state cut} {physical : report.Physical}
    (crash : NativeCheckpointErrorCrash physical) (input : FilePath) (next : NativeReadPosition history log) : Prop
    extends NativeCheckpointRebootContinuation current crash input next where
  returned : report.run = .error report.error
    (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  reachedCensus : report.callbackPrefix.descriptors report.after = current.state.census
theorem NativeReadPosition.recoversCheckpointAfterPowerLoss (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointDirectoryError (image := image) current.state cut} {physical : report.Physical}
    (crash : NativeCheckpointErrorCrash physical) {input : FilePath}
    (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointCrashAlignedReads crash input plan)) :
    ∃ next, NativeCheckpointCrashContinuation current crash input next := by
  let valid := current.readPrefix.refines.1
  have paths := report.heldBindings report.after (by simp)
  obtain ⟨next, reopened⟩ := current.reopensCheckpointSurvivor crash paths.1 paths.2 observe
  exact ⟨next, reopened, report.returns valid, ((report.custody valid).2 report.after (by simp)).1⟩

/-- Reports for the returned checkpoint error, one later power loss,
and a direct healthy open of its chosen files. -/
structure NativeCheckpointCrashObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  reported : NativeCheckpointDirectoryError (image := image) state cut
  physical : reported.Physical
  crash : NativeCheckpointErrorCrash physical
  reopen : ∀ plan : crash.Plan, Nonempty (NativeCheckpointCrashAlignedReads crash input plan)

def NativeCheckpointCrashObservation.diagnostic {input : FilePath}
    (observed : NativeCheckpointCrashObservation state input) : IO.Error :=
  observed.reported.error

theorem NativeReadPosition.recoversCheckpointCrash (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeCheckpointCrashObservation current.state input) :
    ∃ next, NativeCheckpointCrashContinuation current observed.crash input next :=
  current.recoversCheckpointAfterPowerLoss observed.crash observed.reopen

end Alvoki.Storage.DiskSession
