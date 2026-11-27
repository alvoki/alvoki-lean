import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapAdmissionEffects
import Alvoki.Storage.Disk.Proofs.Append.ReopenedSegmentAppend
import Alvoki.Storage.Disk.WalSegmentCheckpointReopen

namespace Alvoki.Storage.WalSegmentRepair

open System

theorem prepareBootstrapWith_noConflicts (directory : DiskDirectory)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata)) {empty : Option ByteArray}
    (prepared : prepareBootstrapWith directory list readEmpty metadata = .ok empty) :
    ∃ entries, list directory.path = .ok entries ∧
      entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false := by
  unfold prepareBootstrapWith at prepared
  cases listed : list directory.path with
  | error cause => simp [listed, Bind.bind, Except.bind] at prepared
  | ok entries =>
    refine ⟨entries, rfl, ?_⟩
    cases checked : entries.any (fun entry => conflictsWithBootstrap entry.fileName) with
    | false => rfl
    | true => simp [listed, checked, Bind.bind, Except.bind, throw] at prepared

/-- The durable segment reported by bootstrap is the initial keeper at
offset zero. The directory image comes from the completed publication. -/
def BootstrapReady.walImage {state : WalSegmentRotation.State} (_ : BootstrapReady state) : WalSegmentImage :=
  ⟨state.metadata, [], ⟨0, 0, ByteArray.empty⟩⟩

/-- Record the actual manifest projection and the empty known run map. -/
def BootstrapReady.checkpointImage {state : WalSegmentRotation.State}
    (_ : BootstrapReady state) : CheckpointPublication.Image :=
  ⟨state.metadata.project .manifest, fun _ _ => none⟩

theorem BootstrapReady.walRange {state : WalSegmentRotation.State} (ready : BootstrapReady state) :
    state.metadata.active.walRange = some ⟨0, 0⟩ := by
  simp [DirectoryPublication.Bindings.walRange, ready.manifestAbsent, ready.zeroMarker, selectedCheckpointWatermark,
    WAL.Boundary.decode_encode, Except.toOption, Bind.bind, Option.bind]

def BootstrapReady.target {state : WalSegmentRotation.State} (ready : BootstrapReady state) : Target :=
  ⟨state.metadata.active, ⟨0, 0⟩, ready.walRange, 0, Nat.le_refl _, ByteArray.empty, rfl⟩

theorem BootstrapReady.walCanonical {state : WalSegmentRotation.State} (ready : BootstrapReady state) :
    WalSegment.Chain [] 0 ready.walImage.segments ∧ ready.walImage.ReadLayout [] ∧ ready.walImage.Valid [] := by
  have chain : WalSegment.Chain [] 0 ready.walImage.segments :=
    .cons (segment := ⟨0, 0, ByteArray.empty⟩) (Nat.le_refl _) (fun _ => rfl) rfl .endOfHistory
  refine ⟨chain, ⟨by simp [BootstrapReady.walImage, WalSegmentImage.segments], ?_, rfl, rfl⟩, ?_⟩
  · intro segment present
    have same : segment = ready.walImage.active := by simpa [BootstrapReady.walImage, WalSegmentImage.segments] using present
    subst segment
    exact Nat.le_refl _
  · apply WalSegmentImage.Valid.of_chain chain
    intro pair chosen
    have same : pair = state.metadata.active := by
      simpa [WalSegmentImage.Selects, BootstrapReady.walImage, ready.settled] using chosen
    exact ⟨⟨0, 0⟩, same.symm ▸ ready.walRange, Nat.le_refl _, Nat.le_refl _⟩

theorem BootstrapReady.checkpointAbsent {state : WalSegmentRotation.State} (ready : BootstrapReady state) :
    ready.checkpointImage.manifest.active = none ∧ ready.checkpointImage.manifest.crashImages = [none] := by
  simp [BootstrapReady.checkpointImage, DirectoryPublication.Image.project, DirectoryPublication.Bindings.get,
    ready.manifestAbsent, ready.settled]

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The empty installed table and actual bootstrap bindings are ready for
the same acknowledged append proof used after a marked recovery. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.BootstrapReady.appendReady
    {state : WalSegmentRotation.State} (ready : BootstrapReady state) :
    ResumedAppendReady ⟨.empty, 0, 0, 0⟩ (ready.walImage.checkpointReopenFiles state.metadata none) ready.target
      [] ready.checkpointImage none := by
  refine
    { ready := ⟨rfl, ready.settled, rfl, rfl, rfl, rfl⟩
      through := rfl
      keeper := rfl
      bytes := rfl
      contents := rfl
      generation := rfl
      selected := ?_
      accepted := ?_
      ordered := trivial
      bounds := PackedTable.empty_rowBounds
      canonical := ⟨.empty, PackedTable.empty_refines, RepresentsWalHistory.empty⟩ }
  · change SelectedIntegrityCheckpoint ready.checkpointImage.durable state.metadata.active.manifest none
    rw [ready.manifestAbsent]
    exact .absent
  · change ready.checkpointImage.AcceptsVersioned 0 (WAL.Boundary.CheckpointRepresentsPrefix [])
      state.metadata.active.manifest
    rw [ready.manifestAbsent]
    exact trivial

/-- The markerless branch returns the exact initial writer when its locked
admission and durability callbacks succeed. The reached image supplies
the empty WAL and checkpoint witnesses used by the first append. -/
theorem runOpenWithInstallation_bootstrapReady (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    (seen : ∀ empty, readEmpty (directory.file (.walSegment 0)) = .ok empty → before.image.observeSuccessor = empty)
    (createEmpty : FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (rotation : WalSegmentRotation.EffectReports
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]))
    {session : SegmentedSession} {after : LockedFileState WalSegmentRotation.State} :
    let recover := bootstrapSegmentedWith directory
      (fun path => liftExcept (list path)) (fun path => liftExcept (readEmpty path))
      (fun path => liftExcept (metadata path)) createEmpty write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before = .ok session after →
      session = ⟨directory, descriptor, .ready ⟨.empty, 0, 0, 0⟩, nextRef, nextRef + 1⟩ ∧
      before.owners (directory.file .lock) = none ∧
      after.owners = before.owners.set (directory.file .lock) (some descriptor) ∧
      (∃ entries, list directory.path = .ok entries ∧
        entries.any (fun entry => conflictsWithBootstrap entry.fileName) = false) ∧
      BootstrapReady after.image := by
  intro recover opened
  have safety := runOpenWithInstallation_bootstrapFromReports directory descriptor nextRef before valid
    acquired acquisition unlock list readEmpty metadata seen createEmpty write sync renameFile rotation marker
  change (match runOpenWithInstallation directory descriptor nextRef acquired unlock recover before with
    | .ok session after => session.phase = .ready ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after.image ∧
        before.owners (directory.file .lock) = none ∧ after.owners.Owns directory descriptor ∧
        prepareBootstrapWith directory list readEmpty metadata = .ok before.image.observeSuccessor
    | .error _ after => _) at safety
  rw [opened] at safety
  obtain ⟨phase, ready, prior, _, admitted⟩ := safety
  have identity :
      session = ⟨directory, descriptor, .ready ⟨.empty, 0, 0, 0⟩, nextRef, nextRef + 1⟩ ∧
        after.owners = before.owners.set (directory.file .lock) (some descriptor) := by
    rw [runOpenWithInstallation_outcome] at opened
    rcases acquired with lockError | (_ | _)
    · cases opened
    · cases opened
    · rw [runOpenWithImage_acquired] at opened
      cases recovered : recover before.image with
      | error cause files => rw [recovered] at opened; cases unlock <;> cases opened
      | ok payload files =>
        rw [recovered] at opened
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj opened
        change Phase.ready payload.installed = _ at phase
        exact ⟨by rw [Phase.ready.inj phase], rfl⟩
  exact ⟨identity.1, prior, identity.2, prepareBootstrapWith_noConflicts directory list readEmpty metadata admitted, ready⟩

end Alvoki.Storage.DiskSession
