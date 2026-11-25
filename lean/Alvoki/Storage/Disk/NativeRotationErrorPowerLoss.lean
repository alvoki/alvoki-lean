import Alvoki.Storage.Disk.NativeRotationErrorReopen
import Alvoki.Storage.Disk.SegmentedReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation CheckpointPublication
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {state : NativeReadyState} {diagnostic : Option IO.Error} {cause : IO.Error}

/-- One reported reboot image at the reached final rotation barrier.
Every selected child and its payload come from this same reached image.
Other filesystem objects and crashes need separate observations. -/
structure NativeRotationErrorCrash (failure : NativeRotationDirectoryFailure state diagnostic) where
  view : DirectoryReadNamespace
  objects : view.modelObject = failure.reported.after.view.modelObject
  chosen : ∀ name, view.child failure.parent.root name ∈ failure.reported.after.crashNames name
  contents : Nat → ByteArray
  survives : ∀ name child, view.child failure.parent.root name = some child →
    contents (view.modelObject child) ∈ failure.reported.after.inodes.crashBytes (view.modelObject child)
  lock : view.child failure.parent.root "LOCK" = some failure.parent.lock.child
  names : FilePath → Option Nat
  child : ∀ name, names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
    (view.child failure.parent.root name).map view.modelObject
  directory : names state.session.directory.path = some (view.modelObject failure.parent.root)
  rebootObjects : Nat → Nat

namespace NativeRotationErrorCrash

variable {failure : NativeRotationDirectoryFailure state diagnostic}

private abbrev successorName (state : NativeReadyState) :=
  renderWalSegmentName (state.writer.installed.walBytes / frameSize)

def successor (crash : NativeRotationErrorCrash failure) : Option DeviceInode :=
  crash.view.child failure.parent.root (successorName state)

def keeperChild (crash : NativeRotationErrorCrash failure) : DeviceInode :=
  crash.successor.getD failure.parent.keeper.child

def payload (crash : NativeRotationErrorCrash failure) : ByteArray :=
  crash.contents (crash.view.modelObject crash.keeperChild)

def retry (crash : NativeRotationErrorCrash failure) : LockedFileState FileImage :=
  failure.reported.cut.crashedFiles state.writer.wal.directory.active crash.successor.isSome

def reboot (crash : NativeRotationErrorCrash failure) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

theorem vacant (crash : NativeRotationErrorCrash failure) :
    TryLockObserves crash.retry.owners state.session.directory (.ok true) := by
  intro _
  simp [retry, RotationInFlightCut.crashedFiles, RotationInFlightCut.released, LockOwners.set]

theorem keeperPayload (crash : NativeRotationErrorCrash failure) :
    crash.payload ∈ failure.reported.after.inodes.crashBytes
      (failure.reported.after.view.modelObject crash.keeperChild) := by
  have belongs : crash.payload ∈ failure.reported.after.inodes.crashBytes (crash.view.modelObject crash.keeperChild) := by
    cases choice : crash.successor with
    | none =>
      have old := crash.chosen (renderWalSegmentName state.writer.installed.activeFirst)
      rw [failure.keepsKeeperMarker.keeperCrash] at old
      simpa only [payload, keeperChild, choice, Option.getD_none] using
        crash.survives _ failure.parent.keeper.child (List.mem_singleton.mp old)
    | some child =>
      simpa only [payload, keeperChild, choice, Option.getD_some] using crash.survives (successorName state) child choice
  simpa only [crash.objects] using belongs

def writer (crash : NativeRotationErrorCrash failure) (valid : state.Valid) : SegmentedWriterState :=
  if crash.successor.isSome then state.writer.rotated valid.retained.rotationTarget else state.writer

theorem retained (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    (crash.writer valid).RetainedReady state.session.directory state.session.descriptor := by
  unfold writer
  split
  · exact valid.retained.rotates failure.parent.nonempty ⟨rfl, rfl, rfl⟩
  · exact valid.retained

theorem pair (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    (crash.writer valid).target.pair = state.writer.target.pair := by
  unfold writer
  split <;> rfl

theorem history (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    (crash.writer valid).history = state.writer.history := by
  unfold writer
  split <;> rfl

theorem physicalKeeper (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    (failure.reported.cut.survivingWal state.writer.wal.directory.active crash.successor.isSome).active =
      (crash.writer valid).wal.active := by
  unfold writer
  cases choice : crash.successor <;> simp only [Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem retryExact (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    crash.retry = (crash.writer valid).powerLossFiles state.session.directory := by
  let selected := crash.writer valid
  let ready := crash.retained valid
  have bytes : selected.target.trimmed = selected.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have pair : selected.target.pair = state.writer.wal.directory.active := (crash.pair valid).trans valid.retained.walPair.symm
  have keeperNames : (crash.retry.image).kept = selected.files.kept := by
    rw [ready.sealedFiles]
    unfold retry RotationInFlightCut.crashedFiles RotationInFlightCut.released State.settledReopenImage
    dsimp only [selected, writer]
    cases choice : crash.successor <;> simp only [Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte] <;> rfl
  change (⟨crash.retry.image, crash.retry.owners⟩ : LockedFileState FileImage) =
      ⟨(selected.powerLossFiles state.session.directory).image, (selected.powerLossFiles state.session.directory).owners⟩
  rw [LockedFileState.mk.injEq]
  constructor
  · change (⟨crash.retry.image.directory, crash.retry.image.kept, crash.retry.image.keeper, crash.retry.image.later⟩ : FileImage) =
      ⟨(selected.powerLossFiles state.session.directory).image.directory, (selected.powerLossFiles state.session.directory).image.kept,
        (selected.powerLossFiles state.session.directory).image.keeper, (selected.powerLossFiles state.session.directory).image.later⟩
    rw [FileImage.mk.injEq]
    refine ⟨?_, keeperNames, ?_, rfl⟩
    · change (failure.reported.cut.survivingWal state.writer.wal.directory.active crash.successor.isSome).directory =
        DirectoryPublication.Image.settled selected.target.pair
      rw [RotationInFlightCut.survivingWal, State.visible_metadata, pair]
      rfl
    · change Publication.Image.settled (some (failure.reported.cut.survivingWal state.writer.wal.directory.active
        crash.successor.isSome).active.bytes) = Publication.Image.settled (some selected.target.trimmed)
      rw [crash.physicalKeeper valid, bytes]
  · unfold retry RotationInFlightCut.crashedFiles RotationInFlightCut.released SegmentedWriterState.powerLossFiles
    change state.writer.owners.set _ none = selected.owners.set _ none
    dsimp only [selected, writer]
    split <;> rfl

/-- The observed crash selects the previous keeper or the newly created
empty successor before any recovery callbacks are considered. -/
theorem choosesKeeper (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    RotationReopenFailures state.session.directory state.writer.wal state.writer.history
      ⟨failure.reported.cut.image, state.writer.owners⟩
      (failure.reported.cut.released state.writer.wal.directory.active crash.successor.isSome) ∧
    (crash.writer valid).wal.active.bytes = crash.payload ∧
    (failure.reported.effective = true → crash.successor = some failure.created.child.child ∧ crash.payload = ByteArray.empty) := by
  have metadata : state.writer.wal.directory.active ∈ failure.reported.cut.image.metadata.crashImages := by
    cases effective : failure.reported.effective <;>
      simp [RotationDirectoryFsyncFailure.cut, RotationCreateParent.cutAtBarrier, effective,
        DirectoryPublication.Image.syncDirectory, valid.retained.walDirectorySettled]
  obtain ⟨survived, bytes, effective⟩ := failure.reported.selectedKeeperPayload
    (crash.chosen (successorName state)) crash.keeperPayload
  exact ⟨failure.reported.cut.startsRetry metadata survived,
    (congrArg WalSegment.bytes (crash.physicalKeeper valid)).symm.trans bytes, effective⟩

theorem alternatives (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    (crash.successor = none ∧ crash.payload = state.writer.wal.active.bytes) ∨
    (crash.successor = some failure.created.child.child ∧ crash.payload = ByteArray.empty) := by
  obtain ⟨_, bytes, afterEffect⟩ := crash.choosesKeeper valid
  cases effective : failure.reported.effective
  · have survived := crash.chosen (successorName state)
    rw [failure.reported.settled.2.2 effective] at survived
    obtain absent | present := failure.created.successorSurvivors _ survived
    · have absent : crash.successor = none := absent
      exact .inl ⟨absent, by simpa [writer, absent] using bytes.symm⟩
    · have present : crash.successor = some failure.created.child.child := present
      have empty : crash.payload = state.writer.wal.rotated.active.bytes := by
        simpa [writer, present, SegmentedWriterState.rotated] using bytes.symm
      exact .inr ⟨present, empty.trans rfl⟩
  · exact .inr (afterEffect effective)

theorem keeperBinding (crash : NativeRotationErrorCrash failure) (valid : state.Valid) :
    crash.view.child failure.parent.root (renderWalSegmentName (crash.writer valid).wal.active.first) =
      some crash.keeperChild := by
  have oldFirst : state.writer.wal.active.first = state.writer.installed.activeFirst :=
    (valid.retained.resumed.keeper.trans valid.retained.active).symm
  have newFirst : state.writer.wal.rotated.active.first = state.writer.installed.walBytes / frameSize :=
    valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
  unfold writer keeperChild
  cases choice : crash.successor with
  | none =>
    have old := crash.chosen (renderWalSegmentName state.writer.installed.activeFirst)
    rw [failure.keepsKeeperMarker.keeperCrash] at old
    simpa only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, oldFirst, Option.getD_none]
      using List.mem_singleton.mp old
  | some inode =>
    simpa only [Option.isSome_some, ↓reduceIte, Option.getD_some, SegmentedWriterState.rotated, successor, newFirst] using choice

structure Plan (crash : NativeRotationErrorCrash failure) (valid : state.Valid) where
  layout : CanonicalKeeperLayout crash.retry.image (crash.writer valid).history
  target : layout.target = (crash.writer valid).target
  keeper : layout.keeper = (crash.writer valid).wal.active
  aligned : layout.tail = ByteArray.empty
  descriptors : layout.sealed ++ [layout.keeper] = (crash.writer valid).wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads ((crash.writer valid).wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, ((crash.writer valid).wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.retry.image layout.target layout.plan

theorem prepares (crash : NativeRotationErrorCrash failure) (valid : state.Valid) : Nonempty (crash.Plan valid) := by
  let ready := crash.retained valid
  have exactRetry := crash.retryExact valid
  have selected : ∃ layout : CanonicalKeeperLayout crash.retry.image (crash.writer valid).history,
      layout.target = (crash.writer valid).target ∧ layout.keeper = (crash.writer valid).wal.active ∧
      layout.sealed ++ [layout.keeper] = (crash.writer valid).wal.readDescriptors layout.range.watermark ∧
      selectWalSegmentReads ((crash.writer valid).wal.segments.map WalSegment.first) layout.range.watermark =
        some (layout.first, ((crash.writer valid).wal.readDescriptors layout.range.watermark).map WalSegment.first) ∧
      Prepared crash.retry.image layout.target layout.plan := by
    rw [exactRetry]
    exact ready.powerLossLayout
  obtain ⟨layout, target, keeper, descriptors, offsets, prepared⟩ := selected
  have visible : crash.retry.image.keeper.active = some (crash.writer valid).wal.active.bytes := by
    rw [exactRetry]
    change some (crash.writer valid).target.trimmed = _
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have aligned : layout.tail = ByteArray.empty := by
    have bytes := Option.some.inj (layout.visible.symm.trans visible)
    rw [keeper] at bytes
    exact (ByteArray.append_right_inj _).mp (bytes.trans ByteArray.append_empty.symm)
  exact ⟨⟨layout, target, keeper, aligned, descriptors, offsets, prepared⟩⟩

end NativeRotationErrorCrash

variable {failure : NativeRotationDirectoryFailure state diagnostic}

/-- The final reported open uses the reboot census and the one picked
namespace. Its read callbacks supply bytes from that same inode map. -/
structure NativeRotationCrashReads (crash : NativeRotationErrorCrash failure) {valid : state.Valid}
    (input : FilePath) (plan : crash.Plan valid)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint) where
  opening : CheckpointBarrierAlignedReports input state.session.directory crash.reboot crash.retry plan.layout
    state.writer.published crash.vacant selected crash.names
  chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody
  root : opening.admission.root = failure.parent.root
  sameChildren : opening.admission.view.child opening.admission.root = crash.view.child failure.parent.root
  sameObjects : opening.admission.view.modelObject = crash.view.modelObject
  directory : opening.reads.bindings state.session.directory.path = crash.names state.session.directory.path
  lock : opening.reads.bindings (state.session.directory.file .lock) = crash.names (state.session.directory.file .lock)
  bytes : ∀ inode payload, opening.reads.reads.objectBytes inode = some payload → crash.contents inode = payload
  earlierTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧ state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeRotationCrashReads

variable {crash : NativeRotationErrorCrash failure} {valid : state.Valid} {input : FilePath} {plan : crash.Plan valid}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}

def run (seen : NativeRotationCrashReads crash input plan selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  seen.opening.finish.runFromCensus seen.chronology.metadataRelease seen.chronology.runs.released seen.chronology.sealRelease

def ReadsSurvivor (seen : NativeRotationCrashReads crash input plan selected)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsFile (seen : NativeRotationCrashReads crash input plan selected)
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (canonical : CheckpointCrashChild crash.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some child)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view) :
    seen.ReadsSurvivor path payload := by
  let read := calls.observesFile bound contents
  have object : seen.opening.admission.view.modelObject child = read.object :=
    (congrArg seen.opening.admission.view.modelObject (calls.statLookup.child_eq bound)).symm.trans calls.identifiedStat
  exact ⟨read, canonical.sameObject calls bound contents, object ▸ seen.bytes _ _ contents⟩

theorem readsWal (seen : NativeRotationCrashReads crash input plan selected)
    (segment : WalSegment) (present : segment ∈ plan.layout.sealed ++ [plan.layout.keeper]) :
    seen.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  rcases List.mem_append.mp present with sealed | last
  · let file := seen.opening.reads.wal.sealedFile segment sealed
    exact seen.readsFile (seen.opening.sealChild segment sealed) file.bound file.contents file.calls
  · obtain rfl := List.mem_singleton.mp last
    let file := seen.opening.reads.wal.keeper
    have contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject file.object) =
        some plan.layout.keeper.bytes := by simpa only [plan.aligned, ByteArray.append_empty] using file.contents
    exact seen.readsFile seen.opening.keeperChild file.bound contents file.calls

theorem readsKeeper (seen : NativeRotationCrashReads crash input plan selected) :
    seen.opening.reads.wal.keeper.calls.statLookup.child = crash.keeperChild ∧
    seen.opening.reads.wal.keeper.calls.openLookup.child = crash.keeperChild ∧
    ∃ read : seen.opening.reads.reads.ObservesFile
        (state.session.directory.file (.walSegment plan.layout.keeper.first)) plan.layout.keeper.bytes,
      read.object = crash.view.modelObject crash.keeperChild ∧ crash.payload = plan.layout.keeper.bytes := by
  have bound : seen.opening.admission.view.child seen.opening.admission.root
      (renderWalSegmentName plan.layout.keeper.first) = some crash.keeperChild := by
    rw [seen.sameChildren, plan.keeper]
    exact crash.keeperBinding valid
  let file := seen.opening.reads.wal.keeper
  let calls := file.calls
  have contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject crash.keeperChild) =
      some plan.layout.keeper.bytes := by
    have same := Option.some.inj (bound.symm.trans file.bound)
    rw [same]
    simpa only [plan.aligned, ByteArray.append_empty] using file.contents
  let read := calls.observesFile bound contents
  have stat := calls.statLookup.child_eq bound
  have object : read.object = crash.view.modelObject crash.keeperChild := by
    change calls.statObject = _
    exact calls.identifiedStat.symm.trans (by rw [stat, seen.sameObjects])
  have bytes := (congrArg WalSegment.bytes plan.keeper).trans (crash.choosesKeeper valid).2.1
  exact ⟨stat, calls.openLookup.child_eq bound, read, object, bytes.symm⟩

/-- The same crash view supplies the bounded checkpoint and marker
reads, in addition to the exact ordered WAL established separately. -/
structure Metadata (seen : NativeRotationCrashReads crash input plan selected) : Prop where
  absent : crash.retry.image.directory.active.manifest = none →
    crash.names (state.session.directory.file .manifest) = none ∧
    ∃ name message, seen.opening.reads.reads.stat (state.session.directory.file .manifest) =
      .error (.noFileOrDirectory name 2 message)
  manifest : ∀ bytes, crash.retry.image.directory.active.manifest = some bytes →
    seen.ReadsSurvivor (state.session.directory.file .manifest) bytes
  runs : ∀ bytes metadata, crash.retry.image.directory.active.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
    ∀ index < metadata.header.runCount.toNat, ∀ payload,
    state.writer.published.durable metadata.header.generation index = some payload →
    seen.ReadsSurvivor (state.session.directory.file (.run metadata.header.generation index)) payload
  marker : seen.ReadsSurvivor (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)

theorem readsMetadata (seen : NativeRotationCrashReads crash input plan selected)
    (pair : crash.retry.image.directory.active = state.writer.target.pair) (valid : state.Valid) :
    seen.Metadata := by
  let opening := seen.opening
  have marker : crash.retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary (pair.trans valid.retained.resumed.ready.selected.symm)).trans
      (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  obtain ⟨boundary, _⟩ := opening.reads.metadata.markerFile _ marker
  refine ⟨?_, ?_, ?_, seen.readsFile opening.markerChild boundary.bound boundary.contents boundary.calls⟩
  · intro absent
    obtain ⟨missing, stat⟩ := opening.reads.metadata.manifestMissing absent
    exact ⟨(opening.manifestChild : _ = _).symm.trans (by rw [missing]; rfl), stat⟩
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes present
    exact seen.readsFile opening.manifestChild file.bound file.contents file.calls
  · intro bytes metadata present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := opening.reads.runs bytes metadata present decoded index within payload stored
    exact seen.readsFile (opening.runChild bytes metadata present decoded index within) bound contents calls

end NativeRotationCrashReads

/-- The same reboot preparation and aligned installation apply after
an interrupted directory sync or its returned diagnostic. -/
structure NativeRotationSurvivorReopen (current next : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state diagnostic}
    (crash : NativeRotationErrorCrash failure) (input : FilePath) : Prop where
  loss : RotationReopenFailures current.state.session.directory current.state.writer.wal current.state.writer.history
    ⟨failure.reported.cut.image, current.state.writer.owners⟩
    (failure.reported.cut.released current.state.writer.wal.directory.active crash.successor.isSome)
  effective : failure.reported.effective = true → crash.successor = some failure.created.child.child ∧ crash.payload = ByteArray.empty
  alternatives : (crash.successor = none ∧ crash.payload = current.state.writer.wal.active.bytes) ∨
    (crash.successor = some failure.created.child.child ∧ crash.payload = ByteArray.empty)
  reads : next.reads = current.reads
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  lock : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  directory : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  pair : next.state.files.image.directory.active = current.state.writer.target.pair
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  exactOpen : ∃ (plan : crash.Plan current.readPrefix.refines.1)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (seen : NativeRotationCrashReads crash input plan selected),
    next.opened = seen.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    seen.opening.admission.root = failure.parent.root ∧
    next.state.writer.target = plan.layout.target ∧ next.state.writer.installed.activeFirst = plan.layout.keeper.first ∧
    seen.Metadata ∧
    (∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
      seen.ReadsSurvivor (current.state.session.directory.file (.walSegment segment.first)) segment.bytes) ∧
    seen.opening.reads.wal.keeper.calls.statLookup.child = crash.keeperChild ∧
    seen.opening.reads.wal.keeper.calls.openLookup.child = crash.keeperChild ∧
    ∃ read : seen.opening.reads.reads.ObservesFile
        (current.state.session.directory.file (.walSegment plan.layout.keeper.first)) plan.layout.keeper.bytes,
      read.object = crash.view.modelObject crash.keeperChild ∧ crash.payload = plan.layout.keeper.bytes
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

private theorem NativeReadPosition.reopensRotationSurvivor (current : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state diagnostic}
    (reached : NativeRotationFailureState current failure)
    (crash : NativeRotationErrorCrash failure) {input : FilePath}
    (observe : ∀ plan : crash.Plan current.readPrefix.refines.1,
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeRotationCrashReads crash input plan selected)) :
    ∃ next, NativeRotationSurvivorReopen current next crash input := by
  let valid := current.readPrefix.refines.1
  let ready := crash.retained valid
  obtain ⟨loss, _, effective⟩ := crash.choosesKeeper valid
  obtain ⟨plan⟩ := crash.prepares valid
  have pair := plan.prepared.pair.trans ((congrArg Target.pair plan.target).trans (crash.pair valid))
  let selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.state.writer.checkpoint :=
    (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ valid.retained.resumed.selected
  have accepted : current.state.writer.published.AcceptsVersioned (crash.writer valid).history.length.toUInt64
      (CheckpointRepresentsPrefix (crash.writer valid).history) crash.retry.image.directory.active.manifest := by
    rw [crash.history valid, pair]
    exact valid.retained.resumed.accepted
  obtain ⟨seen⟩ := observe plan selected
  let opening := seen.opening
  let finish : CapturedKeeperFinish opening.callbacks opening.reads crash.vacant selected := .aligned opening.finish
  have following := opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  have kept : crash.retry.image.kept =
      ((crash.writer valid).wal.checkpointReopenFiles (crash.writer valid).wal.directory none).kept := by
    rw [crash.retryExact valid]
    exact ready.sealedFiles
  let reads := current.reads
  have sameHistory := (crash.history valid).trans current.readPrefix.refines.2.1
  have pending : PendingClientReplay log reads (crash.writer valid).history :=
    Eq.mpr (congrArg (PendingClientReplay log reads) sameHistory) reached.reads
  have bounded : ∀ read ∈ reads, read.BoundedBy (crash.writer valid).history.length :=
    Eq.mpr (congrArg (fun history : List WAL.Write => ∀ read ∈ reads, read.BoundedBy history.length) sameHistory) reached.bounded
  obtain ⟨next, seed, cache, census, owner, directorySlot, nextPair, durable, checkpoint, path, target, nextKept,
    phaseFresh, sessionFresh⟩ := finish.startsNativeReadPrefix seen.chronology opening.markerFound plan.prepared
      following accepted ready.resumed.ordered ready.layout ready.valid ready.spans
      (ready.walPair.trans (congrArg Target.pair plan.target).symm) (congrArg WalSegment.first plan.keeper) kept
      pending bounded
  have continued : NativeReadyReadPrefix seen.run next history log reads next :=
    Eq.mp (congrArg (fun history => NativeReadyReadPrefix seen.run next history log reads next) sameHistory) seed
  let nextPosition : NativeReadPosition history log := ⟨seen.run, next, next, reads, continued⟩
  have active : next.writer.installed.activeFirst = plan.layout.keeper.first :=
    continued.refines.1.retained.resumed.keeper.trans (congrArg Target.first target)
  have lockAtCrash : crash.names (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description) := by
    change crash.names ⟨current.state.session.directory.path.toString ++ "/" ++ "LOCK"⟩ = _
    rw [crash.child, crash.lock, Option.map_some, crash.objects, reached.lockObject, reached.sameInodes]
  have directoryAtCrash : crash.names current.state.session.directory.path =
      some (current.state.census.inode current.state.directorySlot.description) := by
    rw [crash.directory, crash.objects, reached.directoryObject, reached.sameInodes]
  have objects := opening.reads.sameObjects
  have sameCensus : next.census.inode = opening.admission.reached.inode := by
    change next.census = opening.finish.census at census
    rw [census, CapturedAlignedFinish.census, opening.finish.repair.opened]
    rfl
  have lock := Option.some.inj (objects.2.1.symm.trans (seen.lock.trans lockAtCrash))
  have directory := Option.some.inj (objects.1.symm.trans (seen.directory.trans directoryAtCrash))
  refine ⟨nextPosition, loss, effective, crash.alternatives valid, rfl, fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2),
    fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1), ?_, ?_, nextPair.trans pair, checkpoint, durable,
    ⟨plan, selected, seen, rfl, continued.frames.1, cache, census, owner, directorySlot, seen.root, target, active, seen.readsMetadata pair valid, seen.readsWal,
      seen.readsKeeper⟩, continued.guardedReplay⟩
  · rw [owner, sameCensus]
    exact lock
  · rw [directorySlot, sameCensus]
    exact directory

/-- The ordinary diagnostic, selected keeper and returned session
belong to the same reported execution. -/
structure NativeRotationCrashReopen (current next : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state (some cause)}
    (crash : NativeRotationErrorCrash failure) (input : FilePath) : Prop
    extends NativeRotationSurvivorReopen current next crash input where
  failed : NativeReturnedRotationError current cause failure

theorem NativeReadPosition.recoversRotationPowerLoss (current : NativeReadPosition history log)
    {failure : NativeRotationDirectoryFailure current.state (some cause)}
    (crash : NativeRotationErrorCrash failure) {input : FilePath}
    (observe : ∀ plan : crash.Plan current.readPrefix.refines.1,
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeRotationCrashReads crash input plan selected)) :
    ∃ next, NativeRotationCrashReopen current next crash input := by
  have returned := current.rotationReturnsError cause failure
  obtain ⟨next, reopened⟩ := current.reopensRotationSurvivor returned.toNativeRotationFailureState crash observe
  exact ⟨next, reopened, returned⟩

/-- The outer stop at the issued fsync is retained alongside the actual
recovery return. The interrupted rotation has no ordinary result. -/
structure NativeInterruptedRotationCrashReopen (current next : NativeReadPosition history log)
    {stop : NativeRotationDirectoryStop current.state}
    (crash : NativeRotationErrorCrash stop) (input : FilePath) : Prop
    extends NativeRotationSurvivorReopen current next crash input where
  interrupted : NativePendingRotation current stop

theorem NativeReadPosition.recoversInterruptedRotation (current : NativeReadPosition history log)
    {stop : NativeRotationDirectoryStop current.state}
    (crash : NativeRotationErrorCrash stop) {input : FilePath}
    (observe : ∀ plan : crash.Plan current.readPrefix.refines.1,
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeRotationCrashReads crash input plan selected)) :
    ∃ next, NativeInterruptedRotationCrashReopen current next crash input := by
  have interrupted := current.stopsDuringRotation stop
  obtain ⟨next, reopened⟩ := current.reopensRotationSurvivor interrupted.toNativeRotationFailureState crash observe
  exact ⟨next, reopened, interrupted⟩

end Alvoki.Storage.DiskSession
