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
    {directory : DiskDirectory} {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble) :
    installReady installed allocatePhase allocateToken (fun phase token => pure (assemble phase token)) before =
      .ok (assemble observed.phase observed.token) observed.afterToken ∧
    (assemble observed.phase observed.token).UsesOpenReferences directory lock syncFiles observed.phase observed.token ∧
    phaseContents observed.afterToken observed.phase = some (.ready installed) := by
  refine ⟨?_, constructor.usesReferences observed.phase observed.token, observed.keepsPhase.trans observed.initialized⟩
  simp only [installReady, Bind.bind, EStateM.bind, observed.phaseAllocated, observed.tokenAllocated, Pure.pure, EStateM.pure]

/-- The marked worker supplies the recovered table and the marker to
the two-slot opener's three reference allocations in order. -/
theorem installsWithRecoveredMarker
    {handle plan : Type} {entry acquired prepared settled afterMarker : heap}
    (probe : EStateM IO.Error heap (Option IO.FS.Metadata))
    (bootstrap : EStateM IO.Error heap (WalSegmentRepair.Reopened × handle × WAL.TwoSlot.Selection))
    {metadata : IO.FS.Metadata} {probed : heap}
    (found : probe entry = .ok (some metadata) probed)
    (acquire : EStateM IO.Error heap (handle × WAL.TwoSlot.Selection))
    (prepare : WAL.TwoSlot.Selection → EStateM IO.Error heap (plan × WalSegmentRepair.Reopened × Nat))
    (stabilize : handle → EStateM IO.Error heap Unit)
    (finish : plan → Nat → EStateM IO.Error heap Unit)
    {opened : WalSegmentRepair.Reopened} {marker : handle} {selected : WAL.TwoSlot.Selection}
    (markerRead : acquire probed = .ok (marker, selected) acquired)
    {repairPlan : plan} {keeperSize : Nat}
    (readWal : prepare selected acquired = .ok (repairPlan, opened, keeperSize) prepared)
    (markerSynced : stabilize marker prepared = .ok () settled)
    (repaired : finish repairPlan keeperSize settled = .ok () before)
    (observed : OpenReferenceAllocations allocatePhase allocateToken phaseContents opened.installed before)
    {directory : DiskDirectory} {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
    (allocateMarker : Option (handle × WAL.TwoSlot.Selection) → EStateM IO.Error heap (IO.Ref (Option (handle × WAL.TwoSlot.Selection))))
    {cell : IO.Ref (Option (handle × WAL.TwoSlot.Selection))}
    (markerAllocated : allocateMarker (some (marker, selected)) observed.afterToken = .ok cell afterMarker)
    (keepsPhase : phaseContents afterMarker observed.phase = phaseContents observed.afterToken observed.phase)
    (markerContents : heap → IO.Ref (Option (handle × WAL.TwoSlot.Selection)) →
      Option (Option (handle × WAL.TwoSlot.Selection)))
    (initializedMarker : markerContents afterMarker cell = some (some (marker, selected))) :
    TwoSlotDiskTable.installWithMarker
      (do
        if (← probe).isSome then WAL.TwoSlot.reopenAcquiredWith acquire prepare stabilize finish
        else bootstrap)
      (fun reopened => installReady reopened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble phase token)))
      allocateMarker entry = .ok (assemble observed.phase observed.token, cell) afterMarker ∧
    (assemble observed.phase observed.token).UsesOpenReferences directory lock syncFiles observed.phase observed.token ∧
    phaseContents afterMarker observed.phase = some (.ready opened.installed) ∧
    markerContents afterMarker cell = some (some (marker, selected)) := by
  have worker : WAL.TwoSlot.reopenAcquiredWith acquire prepare stabilize finish probed =
      .ok (opened, marker, selected) before := by
    simp only [WAL.TwoSlot.reopenAcquiredWith_reports, markerRead, WAL.TwoSlot.reopenWith_reports, readWal, markerSynced, repaired]
  obtain ⟨_, references, ready⟩ := observed.installs constructor
  exact ⟨by simp only [TwoSlotDiskTable.installWithMarker, Bind.bind, EStateM.bind, found, Option.isSome_some, ↓reduceIte, worker, installReady, observed.phaseAllocated, observed.tokenAllocated, markerAllocated, Pure.pure, EStateM.pure],
    references, keepsPhase.trans ready, initializedMarker⟩

end OpenReferenceAllocations

variable {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- For either successful native open route, the shared installation
callbacks place the exact recovered writer in the phase cell of the
returned DiskTable. The live cells and held handle use the identities
of the same ready read prefix. The premise reports just the two
allocation effects at the reported installer suffix. Reference identity
projections apply within that reported process heap. -/
theorem NativeOpenSuccessReports.returnsReadyWithReferences
    (report : NativeOpenSuccessReports input directory history log recorded)
    {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
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
      db.UsesOpenReferences directory lock syncFiles allocation.phase allocation.token ∧
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
