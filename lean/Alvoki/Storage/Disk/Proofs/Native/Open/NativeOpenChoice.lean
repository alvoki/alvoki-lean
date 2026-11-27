import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapExecution
import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeMarkedReadPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

private abbrev BootstrapState := LockedFileState WalSegmentRotation.State

/-- The observed admission and publication steps for a fresh directory. -/
structure EmptyOpenSuccessReports (input : FilePath) (directory : DiskDirectory) where
  before : BootstrapState
  calls : BootstrapOpenCalls CensusDirectoryCache directory before
  captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls
  listed : BootstrapCheckedListing captured
  keeper : BootstrapZeroKeeperRoute listed
  marker : BootstrapMarkerCustody listed
  handoff : BootstrapKeeperMarkerHandoff keeper marker
  admission : OpenAdmissionReports input directory calls.slot
  empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩
  effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker

/-- A healthy marked open starts from the reached history and selected
files. All read, allocation and repair effects are primitive reports. -/
structure MarkedOpenSuccessReports (input : FilePath) (directory : DiskDirectory)
    (history : List WAL.Write) (log : List DatabaseSubmissions) (recorded : List RecordedSnapshotRead) where
  inventory : DescriptorInventory
  retry : LockedFileState FileImage
  layout : CanonicalKeeperLayout retry.image history
  published : CheckpointPublication.Image
  checkpoint : Option (PackedTable × UInt64)
  selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint
  vacant : TryLockObserves retry.owners directory (.ok true)
  opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected
  prepared : Prepared retry.image layout.target layout.plan
  following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
    layout.range.watermark < start
  accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
    retry.image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history
  wal : WalSegmentImage
  walLayout : wal.ReadLayout history
  walValid : wal.Valid history
  spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize
  active : wal.directory.active = layout.target.pair
  keeper : layout.target.first = wal.active.first
  kept : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept
  pending : PendingClientReplay log recorded history
  bounded : ∀ read ∈ recorded, read.BoundedBy history.length

/-- Successful open reports use the original state of the selected
worker. Markerless bootstrap has a rotation image until the zero keeper
and marker are published. Marked recovery starts in a retained file image. -/
inductive NativeOpenSuccessReports (input : FilePath) (directory : DiskDirectory) :
    List WAL.Write → List DatabaseSubmissions → List RecordedSnapshotRead → Type where
  | empty (observed : EmptyOpenSuccessReports input directory) : NativeOpenSuccessReports input directory [] [] []
  | marked (observed : MarkedOpenSuccessReports input directory history log recorded) :
      NativeOpenSuccessReports input directory history log recorded

namespace NativeOpenSuccessReports

variable {input : FilePath} {directory : DiskDirectory}
  {history : List WAL.Write} {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

def Image (report : NativeOpenSuccessReports input directory history log recorded) : Type :=
  match report with
  | .empty .. => BootstrapState
  | .marked .. => CensusOpenState

/-- The exact result of the shared native admission, marker dispatch
and installation on the appropriate file-state interpretation. -/
noncomputable def run (report : NativeOpenSuccessReports input directory history log recorded) :
    EStateM.Result IO.Error report.Image SegmentedSession :=
  match report with
  | .empty observed => observed.calls.run observed.admission
  | .marked observed => observed.opening.finish.run observed.opening.chronology

def marker (report : NativeOpenSuccessReports input directory history log recorded) : Option IO.FS.Metadata :=
  match report with
  | .empty .. => none
  | .marked observed => some observed.opening.marker

/-- The no-follow marker probe made under the acquired lock. The markerless
projection handles ENOENT with the same metadata helper as marked recovery. -/
def markerRead (report : NativeOpenSuccessReports input directory history log recorded) :
    Except IO.Error (Option IO.FS.Metadata) :=
  match report with
  | .empty observed =>
    match (optionalMetadataWith (pure (observed.calls.lookup (directory.file .walBoundary))) :
      EStateM IO.Error WalSegmentRotation.State _) observed.before.image with
    | .ok value _ => .ok value
    | .error cause _ => .error cause
  | .marked observed =>
    let admission := observed.opening.admission
    match optionalMetadataWith (admission.lookup (directory.file .walBoundary))
        (admission.reached, admission.held) with
    | .ok value _ => .ok value
    | .error cause _ => .error cause

theorem readsMarker (report : NativeOpenSuccessReports input directory history log recorded) :
    report.markerRead = .ok report.marker := by
  cases report with
  | empty observed =>
    obtain ⟨_, name, message, absent⟩ := observed.calls.markerAbsent
    simp only [markerRead, marker, optionalMetadataWith, Bind.bind, EStateM.bind, absent, Pure.pure, EStateM.pure]
  | marked observed =>
    simp only [markerRead, marker, optionalMetadataWith, Bind.bind, EStateM.bind, observed.opening.markerFound,
      Pure.pure, EStateM.pure]

/-- The same native held dispatcher reaches the worker selected by that
probe. This assertion is independent of whether recovery then returns. -/
def Selects (report : NativeOpenSuccessReports input directory history log recorded) : Prop :=
  match report with
  | .empty observed =>
    observed.calls.run observed.admission =
      runOpenWithInstallation directory observed.calls.slot.description observed.calls.nextRef (.ok true)
        observed.calls.unlock (observed.calls.bootstrapAt directory observed.captured.cache) observed.before
  | .marked observed => ∀ marked bootstrap,
    let admission := observed.opening.admission
    let reached := (admission.reached, admission.held)
    admission.recoverWithMarked directory marked bootstrap reached = marked reached

theorem selects (report : NativeOpenSuccessReports input directory history log recorded) : report.Selects := by
  cases report with
  | empty observed => exact observed.calls.runMarkerless observed.admission observed.captured.captures.1
  | marked observed =>
    intro marked bootstrap admission reached
    have marker : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) reached =
        .ok (some observed.opening.marker) reached := by
      simp only [admission, reached, optionalMetadataWith, Bind.bind, EStateM.bind, observed.opening.markerFound,
        Pure.pure, EStateM.pure]
    simpa only [Option.isSome_some, ↓reduceIte] using admission.recoverWithMarked_selects
      (marked := marked) (bootstrap := bootstrap) observed.opening.callbacks.flat marker

/-- Each branch supplies the exact live handles and allocation facts
for the ready writer. Bootstrap projects its published directory and
marker release. Marked recovery returns the complete file state. -/
def UsesReachedState (report : NativeOpenSuccessReports input directory history log recorded)
    (state : NativeReadyState) (after : report.Image) : Prop :=
  match report with
  | .empty observed =>
    let settled := (observed.marker.inodeState.completeFileSync observed.marker.inodeState.active).settleBinding
    BootstrapReady after.image ∧ state.census = observed.effects.reached ∧
      state.files.image.directory = after.image.metadata ∧ state.files.owners = after.owners ∧
      state.cache = observed.captured.cache ∧ state.owner = observed.calls.slot ∧
      state.directorySlot = observed.captured.cached ∧
      state.session.phaseRef = observed.calls.nextRef ∧ state.session.sessionRef = observed.calls.nextRef + 1 ∧
      state.census.references observed.marker.slot.description = [] ∧
      observed.handoff.afterMarkerNames (renderWalSegmentName 0) = [some observed.keeper.keeperChild] ∧
      observed.handoff.afterMarkerNames "WAL.commit" = [some observed.marker.stageChild.child] ∧
      settled.crashBytes observed.keeper.settledImage.active = [ByteArray.empty] ∧
      settled.crashBytes observed.marker.inodeState.active = [WAL.Boundary.encode 0]
  | .marked observed =>
    let opening := observed.opening
    (state.census, state.files) = after ∧ state.cache = opening.admission.cache ∧ state.census = opening.finish.census ∧
      state.owner = opening.admission.owner ∧ state.directorySlot = opening.admission.cached ∧
      state.session.phaseRef ∉ opening.callbacks.liveRefs ∧ state.session.sessionRef ∉ opening.callbacks.liveRefs

/-- Either original open returns the session that seeds the common
ready state. The bootstrap projection preserves its returned metadata
and owner. The marked projection retains its entire returned file image. -/
theorem returnsReady (report : NativeOpenSuccessReports input directory history log recorded) :
    report.markerRead = .ok report.marker ∧ report.Selects ∧ ∃ (state : NativeReadyState) (after : report.Image),
      report.run = .ok state.session after ∧ state.session.directory = directory ∧
      report.UsesReachedState state after ∧ state.owner ∈ state.census.slots ∧ state.directorySlot ∈ state.census.slots ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state history log recorded state := by
  refine ⟨report.readsMarker, report.selects, ?_⟩
  cases report with
  | empty observed =>
    obtain ⟨start, returned, owners, metadata, _, stageClosed, keeperName, markerName, keeperBytes, markerBytes, seed⟩ :=
      observed.handoff.startsNativeReadPrefixFromEmpty observed.admission observed.empty observed.effects
    have bootstrapValid : BootstrapValid observed.before.image := observed.empty.symm ▸ bootstrap_fresh
    obtain ⟨_, _, _, _, _, _, installed, _, _, _⟩ := observed.handoff.installs observed.admission bootstrapValid false
    have sameSession := (EStateM.Result.ok.inj (returned.symm.trans installed)).1
    have atPhase := congrArg SegmentedSession.phaseRef sameSession
    have atSession := congrArg SegmentedSession.sessionRef sameSession
    exact ⟨_, start.final, returned, start.canonicalDirectory,
      ⟨start.bootstrap, rfl, metadata, owners, rfl, rfl, rfl, atPhase, atSession, stageClosed,
        keeperName, markerName, keeperBytes, markerBytes⟩, seed.refines.1.ownerLive, seed.refines.1.directoryLive, seed⟩
  | marked observed =>
    let opening := observed.opening
    obtain ⟨state, seed, cache, census, owner, directorySlot, _, _, _, path, _, _, _, _, phaseFresh, sessionFresh⟩ :=
      opening.finish.startsNativeReadPrefix opening.chronology opening.markerFound observed.prepared.newer
        observed.following observed.accepted observed.ordered observed.walLayout observed.walValid observed.spans
        observed.active observed.keeper observed.kept observed.pending observed.bounded
    have returned := seed.frames.1
    exact ⟨state, (state.census, state.files), returned, path,
      ⟨rfl, cache, census, owner, directorySlot, phaseFresh, sessionFresh⟩, seed.refines.1.ownerLive,
      seed.refines.1.directoryLive, returned ▸ seed⟩

end NativeOpenSuccessReports

/-- A successful marked open reaches the exact checkpoint replay and
census before calling the installer. The returned model phase contains
that same recovered value, with no file effect during construction. -/
theorem MarkedOpenSuccessReports.recoversBeforeInstallation
    (report : MarkedOpenSuccessReports input directory history log recorded) :
    ∃ (state : NativeReadyState) (final : CensusOpenState) (opened : Reopened),
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) = .ok opened final ∧
      opened.installed = state.writer.installed ∧
      report.opening.finish.run report.opening.chronology = .ok state.session final ∧
      final = (state.census, state.files) ∧ state.session.directory = directory ∧
      state.cache = report.opening.admission.cache ∧ state.owner = report.opening.admission.owner ∧
      state.directorySlot = report.opening.admission.cached ∧ state.census = report.opening.finish.census ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state history log recorded state := by
  let covered : NativeOpenSuccessReports input directory history log recorded := .marked report
  obtain ⟨_, _, state, final, returned, path, custody, _, _, seed⟩ := covered.returnsReady
  obtain ⟨sameFiles, cache, census, owner, slot, _, _⟩ := custody
  obtain ⟨opened, recovered, session⟩ := report.opening.finish.reachesInstaller report.opening.chronology
    report.opening.markerFound returned
  have phase := congrArg SegmentedSession.phase session
  exact ⟨state, final, opened, recovered, Phase.ready.inj (phase.symm.trans seed.refines.1.phase), returned,
    sameFiles.symm, path, cache, owner, slot, census, seed⟩

end Alvoki.Storage.DiskSession
