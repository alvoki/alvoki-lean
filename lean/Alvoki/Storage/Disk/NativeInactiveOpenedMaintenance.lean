import Alvoki.Storage.Disk.NativeInactiveOpenedSnapshots
import Alvoki.Storage.Disk.NativeOpenedWalCollection
import Alvoki.Storage.Disk.NativeOpenObsoleteRunCollection
import Alvoki.Storage.Disk.NativeOpenRotation
import Alvoki.Storage.Disk.NativeOpenRunMaintenance

namespace Alvoki.Storage.DiskSession.NativeOpenedHandle

open System

variable {heap : Type} (opened : NativeOpenedHandle heap)
  {before : heap} {mode : NativeInactivePhase}

/-- A rejected phase read leaves the original caller heap unchanged and
ends WAL planning before any metadata or directory callback. -/
theorem rejectsInactiveWalPlan
    (stored : opened.contents before opened.phase = some mode.phase) (calls : WalCollectionReads) :
    opened.table.UsesOpenWalPlanningSchedule opened.directory opened.phase ∧
    ((do
      let installed ← opened.loadInstalled
      liftExcept (calls.plan opened.directory installed) : EStateM IO.Error heap (List Nat)) before) =
        .error mode.error before := by
  refine ⟨opened.uses.planWalCollection, ?_⟩
  simp only [Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

/-- The original WAL collector rejects before its read-only planner or
the first poisoning store. Its linked file projection is unchanged. -/
theorem rejectsInactiveWalCollection
    (stored : opened.contents before opened.phase = some mode.phase) (calls : WalCollectionReads)
    (files : CensusDirectoryCache × WalSealedUnlinkImage)
    (publish : List Nat → EStateM IO.Error (CensusDirectoryCache × WalSealedUnlinkImage) Unit) :
    opened.table.UsesOpenWalCollectionSchedule opened.directory opened.files opened.phase ∧
    calls.collectOnOpenPhase opened publish (before, files) = .error mode.error (before, files) := by
  have rejected : (mode.phase.installed : Except IO.Error Installed) = .error mode.error := by
    cases mode <;> rfl
  exact ⟨opened.uses.collectCoveredWal, calls.rejectsInactiveCollection opened before _ _ stored rejected files publish⟩

theorem rejectsInactiveRotation
    (stored : opened.contents before opened.phase = some mode.phase) (calls : OpenRotationCallbacks heap)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {cachedDirectory : IO.Ref (Option IO.FS.Handle)}
    (references : opened.files.UsesCacheReferences active pending cachedDirectory)
    (cachePath : opened.files.AtDirectory opened.directory.path) :
    UsesRotationSchedule opened.table opened.directory opened.phase active pending cachedDirectory ∧
    calls.run opened lookup active before = .error mode.error before := by
  refine ⟨rotationSchedule opened.uses references cachePath, ?_⟩
  change (rotateWalSchedule opened.loadInstalled _ _ _ _) before = _
  simp only [rotateWalSchedule, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

theorem rejectsInactiveObsoleteRunCollection
    (stored : opened.contents before opened.phase = some mode.phase) (calls : OpenObsoleteRunCallbacks heap)
    (held : List UInt64)
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {cachedDirectory : IO.Ref (Option IO.FS.Handle)}
    (references : opened.files.UsesCacheReferences active pending cachedDirectory)
    (cachePath : opened.files.AtDirectory opened.directory.path) :
    UsesObsoleteRunCollectionSchedule opened.table opened.directory opened.phase active pending cachedDirectory held ∧
    calls.run opened held cachedDirectory active pending before = .error mode.error before :=
  ⟨obsoleteRunCollectionSchedule opened.uses references cachePath held,
    calls.rejectsInactiveCollection opened before _ held (opened.rejectsInstalled stored) cachedDirectory active pending⟩

/-- Inactive compaction and retention both reject before applying the
given rewrite or recording a new table in the original phase cell. -/
theorem rejectsInactiveRunMaintenance
    (stored : opened.contents before opened.phase = some mode.phase) (request : RunMaintenance) :
    request.publicCall opened.table = rewriteRunWith (m := IO) (do (← opened.phase.get).installed)
      opened.phase.set request.update ∧
    rewriteRunWith (m := EStateM IO.Error heap) opened.loadInstalled (opened.set opened.phase)
      request.update before = .error mode.error before := by
  refine ⟨opened.uses.rewriteRun request, ?_⟩
  simp only [rewriteRunWith, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

/-- A repeated public close sees the old table's closed phase and returns
before touching its lock or cache, even if another table now owns the database. -/
theorem reclosesWithoutEffects
    (stored : opened.contents before opened.phase = some .closed) (calls : OpenCloseCallbacks heap) :
    ∃ (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
      (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle)),
      opened.files.UsesCacheReferences active pending directory ∧
      opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
        (active.set none) (pending.set []) (directory.set none) (opened.phase.set .closed) ∧
      closeSchedule (opened.get opened.phase) (fun _ => calls.unlock opened.lock)
        (calls.set active none) (calls.set pending []) (calls.set directory none)
        (opened.set opened.phase .closed) before = .ok () before := by
  obtain ⟨active, pending, directory, references, source⟩ := opened.uses.close
  have loaded := opened.phaseEffects.reads before opened.phase .closed stored
  refine ⟨active, pending, directory, references, source, ?_⟩
  simp only [closeSchedule, Bind.bind, EStateM.bind, loaded, Phase.close, Pure.pure, EStateM.pure]

end Alvoki.Storage.DiskSession.NativeOpenedHandle
