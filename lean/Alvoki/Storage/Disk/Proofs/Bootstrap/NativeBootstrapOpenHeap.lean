import Alvoki.Storage.Disk.NativeExecutionPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory}

private abbrev BootstrapImage := WalSegmentRotation.State

private def bootstrapFileStep {α : Type} (action : EStateM IO.Error BootstrapImage α) :
    EStateM IO.Error (heap × BootstrapImage) α :=
  fun (heap, files) => match action files with
    | .ok result after => .ok result (heap, after)
    | .error cause after => .error cause (heap, after)

private def bootstrapHeapStep {α : Type} (action : EStateM IO.Error heap α) :
    EStateM IO.Error (heap × BootstrapImage) α :=
  fun (heap, files) => match action heap with
    | .ok result after => .ok result (after, files)
    | .error cause after => .error cause (after, files)

namespace EmptyOpenSuccessReports

/-- The admitted markerless worker returns the exact payload and file
image used by the existing physically observed bootstrap installation. -/
theorem recoversBeforeInstallation (report : EmptyOpenSuccessReports input directory) :
    ∃ (state : NativeReadyState) (after : LockedFileState BootstrapImage) (opened : Reopened),
      report.calls.bootstrapAt directory report.captured.cache report.before.image = .ok opened after.image ∧
      opened.installed = state.writer.installed ∧
      report.calls.run report.admission = .ok state.session after ∧
      state.session = ⟨directory, report.calls.slot.description, .ready opened.installed,
        report.calls.nextRef, report.calls.nextRef + 1⟩ ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState state after ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state [] [] [] state := by
  obtain ⟨_, _, state, after, returned, _, reached, _, _, seed⟩ := (NativeOpenSuccessReports.empty report).returnsReady
  have selected := returned
  change report.calls.run report.admission = .ok state.session after at selected
  rw [report.calls.runMarkerless report.admission report.captured.captures.1,
    runOpenWithInstallation_outcome, runOpenWithImage_acquired] at selected
  cases result : report.calls.bootstrapAt directory report.captured.cache report.before.image with
  | error cause afterWorker =>
    simp only [result] at selected
    cases cleanup : report.calls.unlock <;> simp [cleanup] at selected
  | ok opened afterWorker =>
    simp only [result] at selected
    obtain ⟨sameSession, sameFiles⟩ := EStateM.Result.ok.inj selected
    have installed := Phase.ready.inj ((congrArg SegmentedSession.phase sameSession).trans seed.refines.1.phase)
    exact ⟨state, after, opened, by rw [← sameFiles], installed,
      returned, sameSession.symm, reached, seed⟩

/-- Interpret the admitted open, held guards and selected recovery
followed by the actual phase and token installer. The heap tracks those
two allocations. The cache operations use the existing file projection. -/
def runWithPhaseAllocations (report : EmptyOpenSuccessReports input directory)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable) (before : heap) :
    EStateM.Result IO.Error (LockedFileState (heap × BootstrapImage)) DiskTable :=
  let calls := report.calls
  let admission := report.admission
  DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
    (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path))
    (fun resolved slot => runOpenWithImage resolved slot.description (calls.flock slot) calls.unlock do
      let cache ← bootstrapFileStep (calls.openFiles resolved.path)
      let opened ← recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (pure (calls.lookup (resolved.file .wal)))))
        (optionalMetadataWith (pure (calls.lookup (resolved.file .walBoundary))))
        (bootstrapFileStep (calls.marked resolved cache)) (bootstrapFileStep (calls.bootstrapAt resolved cache))
      installReady opened.installed (fun phase => bootstrapHeapStep (allocatePhase phase))
        (fun token => bootstrapHeapStep (allocateToken token)) fun phase token => pure (assemble phase token))
    ⟨(before, report.before.image), report.before.owners⟩

/-- The durable keeper and marker belong to the same successful
markerless call whose returned payload initializes the actual phase
reference. The installation hands off the reached empty client prefix. -/
theorem installsReachedPhase (report : EmptyOpenSuccessReports input directory)
    {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
    (lockIdentity : IO.FS.Handle → Nat) (phaseIdentity : IO.Ref (Phase Installed) → Nat)
    (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (before : heap)
    (observe : ∀ (opened : Reopened) after,
      report.calls.bootstrapAt directory report.captured.cache report.before.image = .ok opened after →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken contents opened.installed before,
        lockIdentity lock = report.calls.slot.description ∧
        phaseIdentity allocation.phase = report.calls.nextRef ∧
        tokenIdentity allocation.token = report.calls.nextRef + 1) :
    ∃ (start : NativeExecutionPosition) (opened : Reopened) (after : LockedFileState BootstrapImage)
      (allocation : OpenReferenceAllocations allocatePhase allocateToken contents opened.installed before)
      (db : DiskTable),
      let state := start.ready.state
      opened.installed = state.writer.installed ∧
      report.runWithPhaseAllocations allocatePhase allocateToken assemble before =
        .ok db ⟨(allocation.afterToken, after.image), after.owners⟩ ∧
      db.UsesOpenReferences state.session.directory lock syncFiles allocation.phase allocation.token ∧
      contents allocation.afterToken allocation.phase = some state.session.phase ∧
      lockIdentity lock = state.session.descriptor ∧ phaseIdentity allocation.phase = state.session.phaseRef ∧
      tokenIdentity allocation.token = state.session.sessionRef ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState state after ∧
      start.history = [] ∧ start.submissions = [] ∧ start.ready.reads = [] ∧
      ∀ instructions requested, NativeExecutionTrace.Reports start instructions →
        (∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
          Nonempty (NativeExecutionEndObservation last requested)) →
        Nonempty (NativeReachedExecutionPrefix start instructions requested) := by
  obtain ⟨state, after, opened, recovered, installed, returned, session, reached, seed⟩ := report.recoversBeforeInstallation
  obtain ⟨allocation, locked, phase, token⟩ := observe opened after.image recovered
  obtain ⟨_, references, stored⟩ := allocation.installs constructor
  let start : NativeExecutionPosition := ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], seed⟩⟩
  refine ⟨start, opened, after, allocation, assemble allocation.phase allocation.token, installed, ?_, ?_, ?_, ?_,
    ?_, ?_, reached, rfl, rfl, rfl, NativeExecutionTrace.reachesPrefix start⟩
  all_goals try dsimp only [start]
  · obtain ⟨_, _, flat⟩ := report.calls.flatAbsent
    obtain ⟨_, _, marker⟩ := report.calls.markerAbsent.2
    have initialized := report.captured.captures.1
    have afterOwners : after.owners = report.before.owners.set (directory.file .lock) (some report.calls.slot.description) := by
      rw [report.calls.runMarkerless report.admission initialized, runOpenWithInstallation_outcome,
        runOpenWithImage_acquired, recovered] at returned
      exact (congrArg LockedFileState.owners (EStateM.Result.ok.inj returned).2).symm
    unfold runWithPhaseAllocations
    rw [report.admission.admits, report.calls.acquired, runOpenWithImage_acquired]
    simp only [Bind.bind, EStateM.bind, bootstrapFileStep, initialized, recoverSegmentedWalWith, rejectFlatWalWith,
      optionalMetadataWith, flat, marker, Pure.pure, EStateM.pure, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, recovered, installReady, bootstrapHeapStep, allocation.phaseAllocated, allocation.tokenAllocated, afterOwners]
  · rw [session]
    exact references
  · rw [session]
    exact stored
  · rw [session]
    exact locked
  · rw [session]
    exact phase
  · rw [session]
    exact token

end EmptyOpenSuccessReports
end Alvoki.Storage.DiskSession
