import Alvoki.Storage.Disk.NativeCheckpointManifestRenameError
import Alvoki.Storage.Disk.NativeCheckpointErrorPowerLoss
import Alvoki.Storage.Disk.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {report : NativeCheckpointManifestRenameError (image := image) state cut}

/-- One real crash choice of the returned rename's namespace. The
surviving manifest bytes belong to the inode in that same map. The
protected WAL file observations are from the reached pre-crash view. -/
structure NativeCheckpointManifestRenameCrash (report : NativeCheckpointManifestRenameError (image := image) state cut) where
  pair : DirectoryPublication.Bindings
  chosen : pair ∈ (report.synced.settled.runs.files report.after).directory.crashImages
  names : FilePath → Option Nat
  survives : names ∈ report.view.crashBindings
  manifest : pair.manifest ∈ manifestCrashBytes (report.synced.settled.runs.inodes report.after)
    (names (state.session.directory.file .manifest))
  directory : names state.session.directory.path = report.view.visible state.session.directory.path
  lock : names (state.session.directory.file .lock) = report.view.visible (state.session.directory.file .lock)
  marker : ∀ bytes, pair.walBoundary = some bytes → ∃ inode,
    report.view.Stable (state.session.directory.file .walBoundary) inode bytes
  wal : ∀ segment ∈ state.writer.wal.segments, ∃ inode,
    report.view.Stable (state.session.directory.file (.walSegment segment.first)) inode segment.bytes
  rebootObjects : Nat → Nat

namespace NativeCheckpointManifestRenameCrash

def reboot (crash : NativeCheckpointManifestRenameCrash report) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

def retry (crash : NativeCheckpointManifestRenameCrash report) : LockedFileState FileImage :=
  ⟨(report.synced.settled.runs.files report.after).crash crash.pair (some state.writer.wal.active.bytes) [],
    state.files.owners.set (state.session.directory.file .lock) none⟩

def rebootWal (crash : NativeCheckpointManifestRenameCrash report) : WalSegmentImage :=
  { state.writer.wal with directory := .settled crash.pair }

def publication (_crash : NativeCheckpointManifestRenameCrash report) : Image :=
  ⟨(report.synced.settled.runs.files report.after).directory.project .manifest,
    (report.synced.settled.runs.runs report.after).guaranteed⟩

/-- The selected file's byte image is pinned to the exact reached
rename inode bytes, which each selected-file theorem shows were durable. -/
def Stored (crash : NativeCheckpointManifestRenameCrash report) (path : FilePath) (bytes : ByteArray) : Prop :=
  ∃ inode, crash.names path = some inode ∧ (report.synced.settled.runs.inodes report.after).visible inode = bytes ∧
    (report.synced.settled.runs.inodes report.after).crashBytes inode = [bytes]

theorem Stored.ofStable (crash : NativeCheckpointManifestRenameCrash report)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (stable : report.view.Stable path inode bytes) : crash.Stored path bytes :=
  ⟨inode, stable.crashBinding crash.names crash.survives, stable.visibleBytes, stable.crashBytes⟩

theorem vacant (crash : NativeCheckpointManifestRenameCrash report) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  intro _
  simp [retry, LockOwners.set]

theorem losesPower (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid) :
    BoundedReopenTrace state.session.directory (CheckpointRetryTarget state.writer.history state.writer.wal.active.first)
      ⟨report.synced.settled.runs.files report.after, state.files.owners⟩ crash.retry := by
  have frame := report.walAtReturn valid
  have keeper : (report.synced.settled.runs.files report.after).keeper.crashImages = [some state.writer.wal.active.bytes] :=
    (congrArg (fun files : CheckpointWalView => files.keeper.crashImages) frame).trans (by
      change state.writer.files.keeper.crashImages = [some state.writer.wal.active.bytes]
      rw [valid.retained.resumed.ready.keeperDurable, valid.retained.resumed.contents,
        valid.retained.active, valid.retained.layout.activeBytes])
  have later : (report.synced.settled.runs.files report.after).later.crashImages = [[]] :=
    (congrArg (fun files : CheckpointWalView => files.later.crashImages) frame).trans valid.retained.resumed.ready.pruned.2
  exact .powerLoss .empty crash.chosen (by rw [keeper]; simp) (by rw [later]; simp)

theorem reachedFiles (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid) :
    crash.retry.image = crash.rebootWal.checkpointReopenFiles crash.rebootWal.directory none := by
  have keeps : (report.synced.settled.runs.files report.after).kept =
      (state.writer.wal.checkpointReopenFiles state.writer.wal.directory none).kept :=
    (congrArg CheckpointWalView.kept (report.walAtReturn valid)).trans valid.retained.sealedFiles
  have exactFiles : ∀ (files : FileImage),
      files.kept = (state.writer.wal.checkpointReopenFiles state.writer.wal.directory none).kept →
      files.crash crash.pair (some state.writer.wal.active.bytes) [] =
        crash.rebootWal.checkpointReopenFiles crash.rebootWal.directory none := by
    intro files same
    cases files
    simp only [FileImage.crash, rebootWal, WalSegmentImage.checkpointReopenFiles, FileImage.mk.injEq, true_and,
      and_true] at same ⊢
    exact ⟨same, rfl⟩
  exact exactFiles _ keeps

theorem classification (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid) :
    let binding := crash.names (state.session.directory.file .manifest)
    (binding = report.synced.prior ∧ crash.pair.manifest = state.writer.wal.directory.active.manifest) ∨
    (cut.tookEffect = true ∧ binding = some report.synced.inode ∧ crash.pair.manifest = some cut.checkpoint.manifest) := by
  intro binding
  have bytes := crash.manifest
  rw [report.inodes] at bytes
  rcases report.survive crash.names crash.survives with prior | ⟨effect, new⟩
  · rw [prior, (report.synced.priorManifest valid).2.1] at bytes
    exact .inl ⟨prior, List.mem_singleton.mp bytes⟩
  · rw [new, manifestCrashBytes, report.synced.stagedBytes.2] at bytes
    exact .inr ⟨effect, new, List.mem_singleton.mp bytes⟩

theorem manifestPayload (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid) :
    (crash.names (state.session.directory.file .manifest)).map (report.synced.settled.runs.inodes report.after).visible =
      crash.pair.manifest := by
  rw [report.inodes]
  rcases crash.classification valid with ⟨binding, manifest⟩ | ⟨_, binding, manifest⟩
  · rw [binding, manifest]
    exact (report.synced.priorManifest valid).1
  · rw [binding, manifest]
    exact congrArg some report.synced.stagedBytes.1

theorem manifestStored (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid)
    {payload : ByteArray} (present : crash.pair.manifest = some payload) :
    crash.Stored (state.session.directory.file .manifest) payload := by
  obtain ⟨inode, named, visible⟩ := Option.map_eq_some_iff.mp ((crash.manifestPayload valid).trans present)
  refine ⟨inode, named, visible, ?_⟩
  rw [report.inodes]
  rcases crash.classification valid with ⟨oldName, oldPayload⟩ | ⟨_, replacement, encoded⟩
  · have durable := (report.synced.priorManifest valid).2.1
    rw [← oldName, named, manifestCrashBytes, ← oldPayload, present] at durable
    exact (List.map_inj_right (fun _ _ => Option.some.inj)).mp
      (durable.trans (show [some payload] = ([payload] : List ByteArray).map some from rfl))
  · have sameInode := Option.some.inj (named.symm.trans replacement)
    have sameBytes := Option.some.inj (encoded.symm.trans present)
    rw [sameInode, ← sameBytes]
    exact report.synced.stagedBytes.2

theorem oldOrNew (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid) :
    crash.pair.manifest = state.writer.wal.directory.active.manifest ∨
      (cut.tookEffect = true ∧ crash.pair.manifest = some cut.checkpoint.manifest) :=
  (crash.classification valid).imp And.right (fun chosen => ⟨chosen.1, chosen.2.2⟩)

private theorem newHeader (valid : state.Valid)
    {metadata : Manifest.IntegrityCheckpoint}
    (decoded : Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata) :
    metadata.header = checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation state.writer) := by
  let generation := SegmentedCheckpointReport.generation state.writer
  let files := cut.checkpoint.table.runs.map (·.run.bytes)
  let exactManifest := Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader cut.checkpoint.table generation) files
  have encoded : cut.checkpoint.manifest = exactManifest.encode := by
    by_cases fits : files.all (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact Except.ok.inj (cut.encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation
        (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))))
    · have rejected := cut.encoded
      simp [encodeCheckpointIntegrityManifest, files, fits, Bind.bind, Except.bind] at rejected
  obtain ⟨_, refinement, _⟩ := valid.retained.resumed.canonical
  have written := (WrittenCheckpoint.of_flushForCheckpoint cut.flushed refinement cut.runCountFits
    valid.retained.resumed.bounds.runs valid.retained.resumed.bounds.memory generation).1
  have roundTrip := Manifest.IntegrityCheckpoint.decode_encode exactManifest written.validFloor
    (by simpa [exactManifest, files, Manifest.IntegrityCheckpoint.fromRuns] using written.count)
  rw [encoded] at decoded
  exact congrArg Manifest.IntegrityCheckpoint.header (Except.ok.inj (decoded.symm.trans roundTrip))

/-- The chosen raw name map contains each selected physical run at the
same exact synced inode, with its sole recorded durable payload. -/
theorem runStored (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid)
    {manifest payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint}
    (present : crash.pair.manifest = some manifest)
    (decoded : Manifest.IntegrityCheckpoint.decode manifest = .ok metadata)
    {index : Nat} (within : index < metadata.header.runCount.toNat)
    (stored : crash.publication.durable metadata.header.generation index = some payload) :
    crash.Stored (state.session.directory.file (.run metadata.header.generation index)) payload := by
  rcases crash.oldOrNew valid with prior | ⟨_, replacement⟩
  · have oldManifest := prior.symm.trans present
    have known := report.retainsRunMap valid manifest metadata oldManifest decoded index within
    have oldBytes := known.symm.trans stored
    obtain ⟨_, _, stable⟩ := report.priorRunAtReturn valid oldManifest decoded within oldBytes
    exact Stored.ofStable crash stable
  · have same := Option.some.inj (replacement.symm.trans present)
    subst manifest
    have header := newHeader (cut := cut) valid decoded
    have inside : index < cut.checkpoint.table.runs.length := by
      rw [header] at within
      have count : (checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation state.writer)).runCount.toNat =
          cut.checkpoint.table.runs.length := UInt64.toNat_ofNat_of_lt' cut.runCountFits
      exact count ▸ within
    obtain ⟨run, _, _, stable⟩ := report.freshRunAtReturn inside
    rw [header] at stored ⊢
    have visible := stable.guaranteed
    have sameBytes := Option.some.inj (visible.symm.trans stored)
    exact sameBytes ▸ Stored.ofStable crash stable

structure Plan (crash : NativeCheckpointManifestRenameCrash report) where
  layout : CanonicalKeeperLayout crash.retry.image state.writer.history
  keeper : layout.keeper = state.writer.wal.active
  aligned : layout.tail = ByteArray.empty
  descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.retry.image layout.target layout.plan
  checkpoint : Option (PackedTable × UInt64)
  selected : SelectedIntegrityCheckpoint crash.publication.durable crash.pair.manifest checkpoint
  generations : (((checkpoint.getD (.empty, 0)).2 = state.writer.installed.generation ∧
      crash.pair.manifest = state.writer.wal.directory.active.manifest) ∨
    ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation state.writer ∧
      crash.pair.manifest = some cut.checkpoint.manifest))
  accepted : crash.publication.AcceptsVersioned state.writer.history.length.toUInt64
    (CheckpointRepresentsPrefix state.writer.history) crash.pair.manifest
  walValid : crash.rebootWal.Valid state.writer.history

theorem plans (crash : NativeCheckpointManifestRenameCrash report) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history) : Nonempty crash.Plan := by
  have marker := (report.crashSelection valid crash.chosen).1
  have origin := crash.oldOrNew valid
  obtain ⟨modeled, executed, choices, newRuns, oldRuns⟩ := report.modeledPublication valid
  obtain ⟨logical, exactExecution, _, logicalValid, acceptable, _⟩ := cut.selectsAcknowledgedHistory valid.retained
  have same := Option.some.inj (exactExecution.symm.trans executed)
  subst logical
  have choice : crash.pair.manifest ∈ modeled.manifest.crashImages := by
    rw [choices]
    rcases origin with prior | ⟨effect, replacement⟩
    · cases cut.tookEffect <;> simp [prior]
    · simp [effect, replacement]
  have pair : crash.pair ∈ (modeled.segmentedCheckpointView state.writer.wal).directory.crashImages := by
    refine List.mem_map.mpr ⟨crash.pair.manifest, choice, ?_⟩
    cases observed : crash.pair
    rw [observed] at marker
    simp only [DirectoryPublication.Bindings.mk.injEq, true_and]
    exact marker.symm
  have selected : (modeled.segmentedCheckpointView state.writer.wal).Selects crash.pair := List.mem_cons_of_mem _ pair
  obtain ⟨accepted, range, decoded, through⟩ := acceptable crash.pair selected
  have old : SelectedRunsAgree state.writer.wal.directory.active.manifest crash.publication.durable modeled.durable := by
    intro bytes metadata present decoded index within
    have different := (cut.priorSelectedGeneration valid.retained present decoded).2
    exact (report.retainsRunMap valid bytes metadata present decoded index within).trans (oldRuns _ different _).symm
  have new : ∀ index < cut.checkpoint.table.runs.length,
      crash.publication.durable (SegmentedCheckpointReport.generation state.writer) index =
        modeled.durable (SegmentedCheckpointReport.generation state.writer) index := by
    intro index within
    exact (report.freshRunMap within).trans (newRuns index).symm
  have exactRuns := cut.selectedRunAgreement valid.retained modeled crash.pair.manifest (origin.imp id And.right)
    crash.publication.durable new old
  have acceptedPhysical := exactRuns.acceptsVersioned decoded accepted
  have walValid : crash.rebootWal.Valid state.writer.history := by
    intro pair included
    have same : pair = crash.pair := by
      simpa [WalSegmentImage.Selects, rebootWal, DirectoryPublication.Image.settled] using included
    subst pair
    exact logicalValid _ selected
  let prior := valid.retained.layout
  let oldLayout : crash.rebootWal.ReadLayout state.writer.history :=
    ⟨prior.ordered, prior.forward, prior.activeEnd, prior.activeBytes⟩
  have exactFiles := crash.reachedFiles valid
  have chosen := oldLayout.checkpointReopenLayout walValid .visible decoded through none
  dsimp only at chosen
  rw [← exactFiles] at chosen
  obtain ⟨layout, rangeExact, keeper, aligned, descriptors, offsets, _, choices, keeperPrefix, laterValid⟩ := chosen
  rw [← rangeExact] at descriptors offsets laterValid
  obtain ⟨checkpoint, _, _, chosen, generations, _⟩ := report.replaysChoice valid pending origin
  exact ⟨⟨layout, keeper, aligned, descriptors, offsets, layout.prepared choices keeperPrefix laterValid,
    checkpoint, chosen, generations, acceptedPhysical, walValid⟩⟩

end NativeCheckpointManifestRenameCrash


/-- Actual marked reads and aligned installation start at the empty
reboot census and use the chosen post-error namespace. -/
structure NativeCheckpointManifestRenameReads (crash : NativeCheckpointManifestRenameCrash report)
    (input : FilePath) (plan : crash.Plan) where
  opening : CheckpointBarrierAlignedReports input state.session.directory crash.reboot crash.retry plan.layout
    crash.publication crash.vacant plan.selected crash.names
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  directoryObject : opening.reads.bindings state.session.directory.path = crash.names state.session.directory.path
  lockObject : opening.reads.bindings (state.session.directory.file .lock) = crash.names (state.session.directory.file .lock)
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeCheckpointManifestRenameReads

variable {crash : NativeCheckpointManifestRenameCrash report} {input : FilePath} {plan : crash.Plan}

noncomputable def run (seen : NativeCheckpointManifestRenameReads crash input plan) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def ReadsSurvivor (seen : NativeCheckpointManifestRenameReads crash input plan) (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ (report.synced.settled.runs.inodes report.after).crashBytes read.object = [payload]

private theorem readsFile (seen : NativeCheckpointManifestRenameReads crash input plan)
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (same : CheckpointCrashChild crash.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some child)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view)
    (stored : crash.Stored path payload) : seen.ReadsSurvivor path payload := by
  obtain ⟨inode, named, _, durable⟩ := stored
  let read := calls.observesFile bound contents
  have observed := same.sameObject calls bound contents
  exact ⟨read, observed, (Option.some.inj (observed.symm.trans named)).symm ▸ durable⟩

structure SelectedReads (seen : NativeCheckpointManifestRenameReads crash input plan) : Prop where
  manifestAbsent : crash.pair.manifest = none → crash.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message)
  manifest : ∀ bytes, crash.pair.manifest = some bytes → seen.ReadsSurvivor (state.session.directory.file .manifest) bytes
  runs : ∀ manifest metadata, crash.pair.manifest = some manifest →
    Manifest.IntegrityCheckpoint.decode manifest = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    crash.publication.durable metadata.header.generation index = some payload →
      seen.ReadsSurvivor (state.session.directory.file (.run metadata.header.generation index)) payload
  marker : seen.ReadsSurvivor (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  wal : ∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
    seen.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes

theorem readsSelected (seen : NativeCheckpointManifestRenameReads crash input plan) (valid : state.Valid) :
    seen.SelectedReads := by
  let opening := seen.opening
  have marker : crash.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    have prior := congrArg Publication.Image.active valid.retained.resumed.markerImage
    change state.writer.files.directory.active.walBoundary = _ at prior
    rw [valid.retained.directoryFiles] at prior
    exact (report.crashSelection valid crash.chosen).1.trans prior
  obtain ⟨boundary, _⟩ := opening.reads.metadata.markerFile _ marker
  obtain ⟨_, stableMarker⟩ := crash.marker _ marker
  refine ⟨?_, ?_, ?_, seen.readsFile opening.markerChild boundary.bound boundary.contents boundary.calls
    (NativeCheckpointManifestRenameCrash.Stored.ofStable crash stableMarker), ?_⟩
  · intro absent
    have map := (crash.manifestPayload valid).trans absent
    have missing : crash.names (state.session.directory.file .manifest) = none := by
      cases bound : crash.names (state.session.directory.file .manifest) <;> simp [bound] at map ⊢
    exact ⟨missing, (opening.reads.metadata.manifestMissing absent).2⟩
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes present
    exact seen.readsFile opening.manifestChild file.bound file.contents file.calls (crash.manifestStored valid present)
  · intro bytes metadata present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := opening.reads.runs bytes metadata present decoded index within payload stored
    exact seen.readsFile (opening.runChild bytes metadata present decoded index within) bound contents calls
      (crash.runStored valid present decoded within stored)
  · intro segment appears
    have saved : segment ∈ state.writer.wal.segments := by
      rw [plan.descriptors, WalSegmentImage.readDescriptors] at appears
      split at appears
      · exact (List.mem_filter.mp appears).1
      · exact List.mem_append_right _ appears
    obtain ⟨_, bytes⟩ := crash.wal segment saved
    have stored := NativeCheckpointManifestRenameCrash.Stored.ofStable crash bytes
    rcases List.mem_append.mp appears with sealed | last
    · let file := opening.reads.wal.sealedFile segment sealed
      exact seen.readsFile (opening.sealChild segment sealed) file.bound file.contents file.calls stored
    · obtain rfl := List.mem_singleton.mp last
      let file := opening.reads.wal.keeper
      have contents : opening.reads.reads.objectBytes (opening.admission.view.modelObject file.object) =
          some plan.layout.keeper.bytes := by simpa only [plan.aligned, ByteArray.append_empty] using file.contents
      exact seen.readsFile opening.keeperChild file.bound contents file.calls stored

end NativeCheckpointManifestRenameReads

/-- A real returned rename error followed by the chosen reboot and
the exact fresh session of its chronological aligned open. -/
structure NativeCheckpointManifestRenameReopened (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointManifestRenameError (image := image) current.state cut}
    (crash : NativeCheckpointManifestRenameCrash report) (input : FilePath) (next : NativeReadPosition history log) : Prop where
  failed : NativeReturnedCheckpointManifestRenameError current report
  lost : BoundedReopenTrace current.state.session.directory
    (CheckpointRetryTarget current.state.writer.history current.state.writer.wal.active.first)
    ⟨report.synced.settled.runs.files report.after, current.state.files.owners⟩ crash.retry
  rebooted : crash.reboot.slots = []
  reads : next.reads = current.reads
  directory : next.state.session.directory = current.state.session.directory
  directoryInode : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  lockInode : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  settled : next.state.files.image.directory.active = crash.pair
  generation : (next.state.writer.installed.generation = current.state.writer.installed.generation ∧
      crash.pair.manifest = current.state.writer.wal.directory.active.manifest) ∨
    (next.state.writer.installed.generation = SegmentedCheckpointReport.generation current.state.writer ∧
      crash.pair.manifest = some cut.checkpoint.manifest)
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : crash.Plan) (seen : NativeCheckpointManifestRenameReads crash input plan),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    next.state.writer.target = plan.layout.target ∧ next.state.writer.checkpoint = plan.checkpoint ∧
    next.state.writer.published.durable = crash.publication.durable ∧ seen.SelectedReads
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.recoversCheckpointManifestRenamePowerLoss (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointManifestRenameError (image := image) current.state cut}
    (crash : NativeCheckpointManifestRenameCrash report) {input : FilePath}
    (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointManifestRenameReads crash input plan)) :
    ∃ next, NativeCheckpointManifestRenameReopened current crash input next := by
  obtain ⟨valid, sameHistory, replay⟩ := current.readPrefix.refines
  have failed := current.checkpointManifestRenameError report
  have pending : PendingClientReplay log current.reads current.state.writer.history := sameHistory.symm ▸ replay
  have bounded : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length :=
    sameHistory.symm ▸ current.readPrefix.readsBounded
  obtain ⟨plan⟩ := crash.plans valid pending
  obtain ⟨seen⟩ := observe plan
  let opening := seen.opening
  let finish : CapturedKeeperFinish opening.callbacks opening.reads crash.vacant plan.selected := .aligned opening.finish
  let prior := valid.retained.layout
  let layout : crash.rebootWal.ReadLayout current.state.writer.history :=
    ⟨prior.ordered, prior.forward, prior.activeEnd, prior.activeBytes⟩
  have kept : crash.retry.image.kept = (crash.rebootWal.checkpointReopenFiles crash.rebootWal.directory none).kept :=
    congrArg FileImage.kept (crash.reachedFiles valid)
  have pair : crash.rebootWal.directory.active = plan.layout.target.pair := plan.prepared.pair
  have following := opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  obtain ⟨state, seeded, cache, census, owner, directorySlot, settled, runs, checkpoint, directory, target,
    seals, phaseFresh, sessionFresh⟩ :=
    finish.startsNativeReadPrefix seen.chronology opening.markerFound plan.prepared following plan.accepted
      valid.retained.resumed.ordered layout plan.walValid valid.retained.spans pair (congrArg WalSegment.first plan.keeper) kept
      pending bounded
  have continued : NativeReadyReadPrefix seen.run state history log current.reads state :=
    Eq.mp (congrArg (fun rows : List WAL.Write => NativeReadyReadPrefix seen.run state rows log current.reads state) sameHistory) seeded
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
    seals.trans (congrArg CheckpointWalView.kept failed.wal)
  have root := failed.directoryObject.trans (congrArg some report.synced.settled.runs.capturedInode)
  refine ⟨next, failed, crash.losesPower valid, rfl, rfl,
    directory, ?_, ?_, fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1),
    fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2), settled,
    ?_, recoveredSeals, ⟨plan, seen, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census, target,
      checkpoint, runs, seen.readsSelected valid⟩, continued.guardedReplay⟩
  · change state.census.inode state.directorySlot.description = _
    rw [inodes, directorySlot]
    exact Option.some.inj (objects.1.symm.trans (seen.directoryObject.trans (crash.directory.trans root)))
  · change state.census.inode state.owner.description = _
    rw [inodes, owner]
    exact Option.some.inj (objects.2.1.symm.trans (seen.lockObject.trans (crash.lock.trans failed.lockObject)))
  · exact plan.generations.imp (fun old => ⟨generation.trans old.1, old.2⟩)
      (fun fresh => ⟨generation.trans fresh.1, fresh.2⟩)

end Alvoki.Storage.DiskSession
