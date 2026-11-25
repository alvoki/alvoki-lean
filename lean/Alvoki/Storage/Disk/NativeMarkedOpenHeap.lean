import Alvoki.Storage.Disk.NativeExecutionPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type}

/-- The marked file worker and the phase allocator use separate projections
of a process state. File observations include descriptor effects. The heap
in this projection tracks the phase and token allocations. -/
private def markedFileStep {α : Type} (action : EStateM IO.Error CensusOpenState α) :
    EStateM IO.Error (heap × CensusOpenState) α :=
  fun (heap, files) => match action files with
    | .ok result reached => .ok result (heap, reached)
    | .error cause reached => .error cause (heap, reached)

private def markedHeapStep {α : Type} (action : EStateM IO.Error heap α) :
    EStateM IO.Error (heap × CensusOpenState) α :=
  fun (heap, files) => match action heap with
    | .ok result reached => .ok result (reached, files)
    | .error cause reached => .error cause (reached, files)

variable {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- The held suffix of the native open schedule. The guarded route uses
the same admitted cache and exact marked repair as the census projection.
The phase allocation consumes the value returned by that worker. -/
noncomputable def MarkedOpenSuccessReports.runWithPhaseAllocations
    (report : MarkedOpenSuccessReports input directory history log recorded)
    (bootstrap : EStateM IO.Error CensusOpenState Reopened)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (before : heap) : EStateM.Result IO.Error (heap × CensusOpenState) DiskTable :=
  let opening := report.opening
  let admission := opening.admission
  let action : EStateM IO.Error (heap × CensusOpenState) DiskTable := do
    let opened ← markedFileStep (admission.recoverWithMarked directory
      (opening.finish.markedWorker opening.chronology directory admission.cache) bootstrap)
    installReady opened.installed (fun phase => markedHeapStep (allocatePhase phase))
      (fun token => markedHeapStep (allocateToken token)) fun phase token => pure (assemble phase token)
  action (before, (admission.reached, admission.held))

/-- In one reported held execution the guarded recovery supplies the
exact checkpoint and WAL replay, and the following allocator puts that
value into the phase reference of the returned native table. There is
no separate value or file image at the installer boundary. The premise
governs allocation effects on the tracked process heap. -/
theorem MarkedOpenSuccessReports.installsReachedPhase
    (report : MarkedOpenSuccessReports input directory history log recorded)
    {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
    (lockIdentity : IO.FS.Handle → Nat) (phaseIdentity : IO.Ref (Phase Installed) → Nat)
    (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (before : heap)
    (observe : ∀ (opened : Reopened) final,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) = .ok opened final →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken contents opened.installed before,
        lockIdentity lock = report.opening.admission.owner.description ∧
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1) :
    ∃ (start : NativeExecutionPosition) (opened : Reopened)
      (allocation : OpenReferenceAllocations allocatePhase allocateToken contents opened.installed before)
      (db : DiskTable),
      let state := start.ready.state
      opened.installed = state.writer.installed ∧
      (∀ bootstrap, report.runWithPhaseAllocations bootstrap allocatePhase allocateToken assemble before =
        .ok db (allocation.afterToken, (state.census, state.files))) ∧
      db.UsesOpenReferences state.session.directory lock syncFiles allocation.phase allocation.token ∧
      contents allocation.afterToken allocation.phase = some state.session.phase ∧
      lockIdentity lock = state.session.descriptor ∧ phaseIdentity allocation.phase = state.session.phaseRef ∧
      tokenIdentity allocation.token = state.session.sessionRef ∧ state.cache = report.opening.admission.cache ∧
      state.owner = report.opening.admission.owner ∧ state.directorySlot = report.opening.admission.cached ∧
      start.history = history ∧ start.submissions = log ∧ start.ready.reads = recorded ∧
      ∀ instructions requested, NativeExecutionTrace.Reports start instructions →
        (∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
          Nonempty (NativeExecutionEndObservation last requested)) →
        Nonempty (NativeReachedExecutionPrefix start instructions requested) := by
  obtain ⟨state, final, opened, recovered, installed, returned, files, path, cache, owner, slot, _, seed⟩ :=
    report.recoversBeforeInstallation
  obtain ⟨allocation, locked, phase, token⟩ := observe opened final recovered
  obtain ⟨_, references, stored⟩ := allocation.installs constructor
  obtain ⟨selected, selectedReturn, session⟩ := report.opening.finish.reachesInstaller report.opening.chronology
    report.opening.markerFound returned
  have sameOpened := (EStateM.Result.ok.inj (selectedReturn.symm.trans recovered)).1
  subst opened
  let start : NativeExecutionPosition :=
    ⟨history, log, ⟨.ok state.session (state.census, state.files), state, state, recorded, seed⟩⟩
  refine ⟨start, _, allocation, assemble allocation.phase allocation.token, installed, ?_, ?_, ?_, ?_,
    ?_, ?_, cache, owner, slot, rfl, rfl, rfl, NativeExecutionTrace.reachesPrefix start⟩
  all_goals dsimp only [start]
  · intro bootstrap
    let opening := report.opening
    let admission := opening.admission
    let entry : CensusOpenState := (admission.reached, admission.held)
    have marker : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) entry =
        .ok (some opening.marker) entry := by
      simp only [entry, admission, opening, optionalMetadataWith, Bind.bind, EStateM.bind,
        report.opening.markerFound, Pure.pure, EStateM.pure]
    have repair := admission.recoverWithMarked_selects (bootstrap := bootstrap)
      (marked := opening.finish.markedWorker opening.chronology directory admission.cache) opening.callbacks.flat marker
    simp only [Option.isSome_some, ↓reduceIte] at repair
    dsimp only [opening, admission] at repair
    simp only [runWithPhaseAllocations, Bind.bind, EStateM.bind, markedFileStep, repair, recovered,
      installReady, markedHeapStep, allocation.phaseAllocated, allocation.tokenAllocated, Pure.pure, EStateM.pure, files]
  · exact path.symm ▸ references
  · rw [session]
    exact stored
  · rw [session]
    exact locked
  · rw [session]
    exact phase
  · rw [session]
    exact token

end Alvoki.Storage.DiskSession
