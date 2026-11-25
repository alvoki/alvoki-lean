import Alvoki.Storage.Disk.NativeOpenChoice

namespace Alvoki.Storage.DiskSession

open System

variable {heap : Type}

/-- Report the two reference allocation callbacks at the reached ready
installation. The second consumes the state returned by the first.
The contents projection describes the reported effect of each primitive. -/
structure OpenReferenceAllocations
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (phaseContents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (installed : Installed) (before : heap) where
  phase : IO.Ref (Phase Installed)
  token : IO.Ref Unit
  afterPhase : heap
  afterToken : heap
  phaseAllocated : allocatePhase (.ready installed) before = .ok phase afterPhase
  initialized : phaseContents afterPhase phase = some (.ready installed)
  tokenAllocated : allocateToken () afterPhase = .ok token afterToken
  keepsPhase : phaseContents afterToken phase = phaseContents afterPhase phase

namespace OpenReferenceAllocations

variable {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {phaseContents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
  {installed : Installed} {before : heap}

/-- Follow the production installer at the two reached raw reference
returns. Its result stores those exact cells and the ready phase
still contains the data passed to the first allocation. -/
theorem installs
    (observed : OpenReferenceAllocations allocatePhase allocateToken phaseContents installed before)
    {directory : DiskDirectory} {lock : IO.FS.Handle} {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock assemble) :
    installReady installed allocatePhase allocateToken (fun phase token => pure (assemble phase token)) before =
      .ok (assemble observed.phase observed.token) observed.afterToken ∧
    (assemble observed.phase observed.token).UsesOpenReferences directory lock observed.phase observed.token ∧
    phaseContents observed.afterToken observed.phase = some (.ready installed) := by
  refine ⟨?_, constructor.usesReferences observed.phase observed.token, observed.keepsPhase.trans observed.initialized⟩
  simp only [installReady, Bind.bind, EStateM.bind, observed.phaseAllocated, observed.tokenAllocated, Pure.pure, EStateM.pure]

end OpenReferenceAllocations

variable {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- For either successful native open route, the shared installation
callbacks place the exact recovered writer in the phase cell of the
returned DiskTable. The live cells and held handle use the identities
of the same ready read prefix. The premise reports just the two
allocation effects and the identities of their returned references. -/
theorem NativeOpenSuccessReports.returnsReadyWithReferences
    (report : NativeOpenSuccessReports input directory history log recorded)
    {lock : IO.FS.Handle} {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock assemble)
    (lockIdentity : IO.FS.Handle → Nat) (phaseIdentity : IO.Ref (Phase Installed) → Nat)
    (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (phaseContents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (heapAtInstall : heap)
    (observe : ∀ (session : SegmentedSession) (files : report.Image) (installed : Installed),
      report.run = .ok session files → session.phase = .ready installed →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken phaseContents installed heapAtInstall,
        lockIdentity lock = session.descriptor ∧ phaseIdentity allocation.phase = session.phaseRef ∧
        tokenIdentity allocation.token = session.sessionRef) :
    report.markerRead = .ok report.marker ∧ report.Selects ∧
    ∃ (state : NativeReadyState) (files : report.Image)
      (allocation : OpenReferenceAllocations allocatePhase allocateToken phaseContents state.writer.installed heapAtInstall)
      (db : DiskTable),
      report.run = .ok state.session files ∧ state.session.directory = directory ∧ report.UsesReachedState state files ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state history log recorded state ∧
      installReady state.writer.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token))
        heapAtInstall = .ok db allocation.afterToken ∧
      db.UsesOpenReferences directory lock allocation.phase allocation.token ∧
      phaseContents allocation.afterToken allocation.phase = some state.session.phase ∧
      lockIdentity lock = state.session.descriptor ∧ phaseIdentity allocation.phase = state.session.phaseRef ∧
      tokenIdentity allocation.token = state.session.sessionRef := by
  obtain ⟨marker, selected, state, files, returned, path, reached, _, _, seed⟩ := report.returnsReady
  have ready := seed.refines.1.phase
  obtain ⟨allocation, locked, phase, token⟩ := observe state.session files state.writer.installed returned ready
  obtain ⟨installed, uses, contents⟩ := allocation.installs constructor
  exact ⟨marker, selected, state, files, allocation, _, returned, path, reached, seed, installed, uses,
    ready.symm ▸ contents, locked, phase, token⟩

end Alvoki.Storage.DiskSession
