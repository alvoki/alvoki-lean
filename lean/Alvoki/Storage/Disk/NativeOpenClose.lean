import Alvoki.Storage.Disk.ClientCachedClose

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev CloseState (image : Type) := CachedCloseState CheckpointOpenHandle image

/-- At the observed heaps, capture the raw cell contents and project
their file handles to the same descriptor and file-state observations
used by the cached close proof. -/
structure OpenCloseHeapView (heap image : Type) where
  phase : heap → IO.Ref (Phase Installed) → Option (Phase Installed)
  active : heap → IO.Ref (Option (FilePath × IO.FS.Handle)) → Option (FilePath × IO.FS.Handle)
  pending : heap → IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle)
  directory : heap → IO.Ref (Option IO.FS.Handle) → Option IO.FS.Handle
  handle : heap → IO.FS.Handle → CheckpointOpenHandle
  files : heap → LockedFileState image
  descriptors : heap → DescriptorInventory

def OpenCloseHeapView.Matches (view : OpenCloseHeapView heap image)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle))
    (reached : heap) (state : CloseState image) : Prop :=
  let entry := fun (value : FilePath × IO.FS.Handle) => (value.1, view.handle reached value.2)
  view.phase reached phase = some state.phase ∧
  Cache.mk ((view.directory reached directory).map (view.handle reached))
    ((view.active reached active).map entry) ((view.pending reached pending).map entry) = state.files.image.1 ∧
  view.files reached = ⟨state.files.image.2, state.files.owners⟩ ∧ view.descriptors reached = state.descriptors

structure OpenCloseCallbacks (heap : Type) where
  getPhase : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  unlock : IO.FS.Handle → EStateM IO.Error heap Unit
  set : {α : Type} → IO.Ref α → α → EStateM IO.Error heap Unit

variable {heap image : Type} {directory : DiskDirectory} {writer : Nat} {start : CloseState image}
  {lock : IO.FS.Handle} {phase : IO.Ref (Phase Installed)}
  {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {cachedDirectory : IO.Ref (Option IO.FS.Handle)}

/-- Each successful clear starts in the heap reached by the preceding
operation and projects to its corresponding reported slot drops. -/
structure OpenCloseClears (report : CachedCloseReports directory writer start)
    (view : OpenCloseHeapView heap image) (calls : OpenCloseCallbacks heap)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (unlocked : heap) where
  afterActive : heap
  afterPending : heap
  afterDirectory : heap
  afterPhase : heap
  activeCleared : calls.set active none unlocked = .ok () afterActive
  activeView : view.Matches phase active pending cachedDirectory afterActive
    ((start.release directory writer).drop .active (report.drops .active))
  pendingCleared : calls.set pending [] afterActive = .ok () afterPending
  pendingView : view.Matches phase active pending cachedDirectory afterPending
    (((start.release directory writer).drop .active (report.drops .active)).drop .pending (report.drops .pending))
  directoryCleared : calls.set cachedDirectory none afterPending = .ok () afterDirectory
  directoryView :
    let afterActive := (start.release directory writer).drop .active (report.drops .active)
    let afterPending := afterActive.drop .pending (report.drops .pending)
    view.Matches phase active pending cachedDirectory afterDirectory (afterPending.drop .directory (report.drops .directory))
  closed : calls.set phase .closed afterDirectory = .ok () afterPhase
  closedView : view.Matches phase active pending cachedDirectory afterPhase report.finished

theorem OpenCloseClears.emptyCache {report : CachedCloseReports directory writer start}
    {view : OpenCloseHeapView heap image} {calls : OpenCloseCallbacks heap} {unlocked : heap}
    (seen : OpenCloseClears report view calls phase active pending cachedDirectory unlocked) :
    view.phase seen.afterPhase phase = some .closed ∧ view.active seen.afterPhase active = none ∧
      view.pending seen.afterPhase pending = [] ∧ view.directory seen.afterPhase cachedDirectory = none := by
  have cleared := seen.closedView.2.1
  rw [show report.finished.files.image.1 = ⟨none, none, []⟩ from rfl] at cleared
  simp only [Cache.mk.injEq, Option.map_eq_none_iff, List.map_eq_nil_iff] at cleared
  exact ⟨seen.closedView.1, cleared.2.1, cleared.2.2, cleared.1⟩

/-- The raw phase read and unlock, with the slot and three cache
references of the same table. The error projection is local to this
reported unlock. A successful unlock supplies the observed clears. -/
structure OpenCloseObservation (report : CachedCloseReports directory writer start)
    (view : OpenCloseHeapView heap image) (calls : OpenCloseCallbacks heap)
    (lock : IO.FS.Handle) (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (before : heap) where
  afterUnlock : heap
  reached : view.Matches phase active pending cachedDirectory before start
  loaded : calls.getPhase phase before = .ok start.phase before
  sameLock : (view.handle before lock).2.1 = report.slot
  returned : calls.unlock lock before = match report.result with
    | .ok () => .ok () afterUnlock
    | .error cause => .error cause afterUnlock
  unlockedView : view.Matches phase active pending cachedDirectory afterUnlock
    (match report.result with
    | .ok () => start.release directory writer
    | .error _ => start)
  clears : report.result = .ok () →
    Nonempty (OpenCloseClears report view calls phase active pending cachedDirectory afterUnlock)

namespace OpenCloseObservation

variable {report : CachedCloseReports directory writer start} {view : OpenCloseHeapView heap image}
  {calls : OpenCloseCallbacks heap} {before : heap}

def Reached (seen : OpenCloseObservation report view calls lock phase active pending cachedDirectory before) : Prop :=
  let run := closeSchedule (calls.getPhase phase) (fun _ => calls.unlock lock)
    (calls.set active none) (calls.set pending []) (calls.set cachedDirectory none)
    (calls.set phase .closed) before
  match report.result with
  | .error cause => run = .error cause seen.afterUnlock ∧
    view.Matches phase active pending cachedDirectory seen.afterUnlock start
  | .ok () => ∃ clears : OpenCloseClears report view calls phase active pending cachedDirectory seen.afterUnlock,
    run = .ok () clears.afterPhase ∧ view.Matches phase active pending cachedDirectory clears.afterPhase report.finished

/-- Evaluate the production close schedule with the reported concrete
phase/cache references and raw effects. An unlock error returns before
the first clear. Successful unlock reaches all four setters in order. -/
theorem returns (seen : OpenCloseObservation report view calls lock phase active pending cachedDirectory before)
    (openPhase : start.phase ≠ .closed) : seen.Reached := by
  unfold Reached
  intro run
  cases outcome : report.result with
  | error cause =>
    have returned := seen.returned
    have projected := seen.unlockedView
    rw [outcome] at returned projected
    refine ⟨?_, projected⟩
    cases reached : start.phase <;>
      simp_all [run, closeSchedule, Phase.close, Bind.bind, EStateM.bind, seen.loaded]
  | ok value =>
    cases value
    obtain ⟨clears⟩ := seen.clears outcome
    have returned := seen.returned
    rw [outcome] at returned
    refine ⟨clears, ?_, clears.closedView⟩
    cases reached : start.phase <;>
      simp_all [run, closeSchedule, Phase.close, Bind.bind, EStateM.bind, seen.loaded,
        clears.activeCleared, clears.pendingCleared, clears.directoryCleared, clears.closed]

end OpenCloseObservation

/-- Attach raw close observations to the same concrete table's
production schedule and to the old cached close contract. -/
theorem CachedCloseReports.closesViaOpenReferences
    (report : CachedCloseReports directory writer start) {db : DiskTable} {files : DiskTable.OpenSyncFiles}
    {token : IO.Ref Unit} (uses : db.UsesOpenReferences directory lock files phase token)
    (held : start.files.owners.Owns directory writer) (openPhase : start.phase ≠ .closed) {before : heap}
    (view : OpenCloseHeapView heap image) (calls : OpenCloseCallbacks heap)
    (observe : ∀ active pending cachedDirectory, files.UsesCacheReferences active pending cachedDirectory →
      Nonempty (OpenCloseObservation report view calls lock phase active pending cachedDirectory before)) :
    report.Reached ∧
    ∃ active pending cachedDirectory, files.UsesCacheReferences active pending cachedDirectory ∧
      db.close = closeSchedule phase.get (fun _ => lock.unlock) (active.set none) (pending.set [])
        (cachedDirectory.set none) (phase.set .closed) ∧
      ∃ seen : OpenCloseObservation report view calls lock phase active pending cachedDirectory before, seen.Reached := by
  obtain ⟨active, pending, cachedDirectory, references, source⟩ := uses.close
  obtain ⟨seen⟩ := observe active pending cachedDirectory references
  exact ⟨report.reaches openPhase held, active, pending, cachedDirectory, references, source, seen, seen.returns openPhase⟩

end Alvoki.Storage.DiskSession
