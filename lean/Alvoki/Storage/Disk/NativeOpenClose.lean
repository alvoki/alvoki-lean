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

/-- Change only the projected file-state model, preserving the same
reference contents and descriptor observations. -/
def OpenCloseHeapView.withFileProjection (view : OpenCloseHeapView heap image)
    (files : heap → LockedFileState nextImage) : OpenCloseHeapView heap nextImage :=
  ⟨view.phase, view.active, view.pending, view.directory, view.handle, files, view.descriptors⟩

def OpenCloseHeapView.cacheAt (view : OpenCloseHeapView heap image) (reached : heap)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : Cache CheckpointOpenHandle :=
  let entry := fun (value : FilePath × IO.FS.Handle) => (value.1, view.handle reached value.2)
  ⟨(view.directory reached directory).map (view.handle reached),
    (view.active reached active).map entry, (view.pending reached pending).map entry⟩

def OpenCloseHeapView.Matches (view : OpenCloseHeapView heap image)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle))
    (reached : heap) (state : CloseState image) : Prop :=
  view.phase reached phase = some state.phase ∧
  view.cacheAt reached directory active pending = state.files.image.1 ∧
  view.files reached = ⟨state.files.image.2, state.files.owners⟩ ∧ view.descriptors reached = state.descriptors

structure OpenCloseCallbacks (heap : Type) where
  getPhase : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  unlock : IO.FS.Handle → EStateM IO.Error heap Unit
  set : {α : Type} → IO.Ref α → α → EStateM IO.Error heap Unit

variable {heap image : Type} {directory : DiskDirectory} {writer : Nat} {start : CloseState image}
  {lock : IO.FS.Handle} {phase : IO.Ref (Phase Installed)}
  {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {cachedDirectory : IO.Ref (Option IO.FS.Handle)}

/-- A close's reached heap has the original live image, released lock,
empty cache, and precisely the observed cache-clear drops. -/
def OpenCloseHeapView.ClosedFrom (view : OpenCloseHeapView heap image)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (directory : DiskDirectory) (drops : CloseCacheField → List LockReferenceDrop) (before after : heap) : Prop :=
  view.Matches phase active pending cachedDirectory after
    ⟨.closed, ⟨(⟨none, none, []⟩, (view.files before).image), (view.files before).owners.set (directory.file .lock) none⟩,
      (view.descriptors before).afterDrops (drops .active ++ drops .pending ++ drops .directory)⟩

/-- One reached cache setter clears its own field and records its slot
drops. The phase and live file image are carried from its input heap. -/
abbrev OpenCloseHeapView.ClearsCache (view : OpenCloseHeapView heap image)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (field : CloseCacheField) (drops : List LockReferenceDrop) (before after : heap) : Prop :=
  ∀ {prior : CloseState image}, view.Matches phase active pending cachedDirectory before prior →
    view.Matches phase active pending cachedDirectory after (prior.drop field drops)

/-- Each setter starts at the preceding callback's return. The last
one stores the phase and frames the cache, files and descriptors. -/
structure OpenCloseClears (drops : CloseCacheField → List LockReferenceDrop)
    (view : OpenCloseHeapView heap image) (calls : OpenCloseCallbacks heap)
    (phase : IO.Ref (Phase Installed)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle))
    (unlocked : heap) where
  afterActive : heap
  afterPending : heap
  afterDirectory : heap
  afterPhase : heap
  activeCleared : calls.set active none unlocked = .ok () afterActive
  activeView : view.ClearsCache phase active pending cachedDirectory .active (drops .active) unlocked afterActive
  pendingCleared : calls.set pending [] afterActive = .ok () afterPending
  pendingView : view.ClearsCache phase active pending cachedDirectory .pending (drops .pending) afterActive afterPending
  directoryCleared : calls.set cachedDirectory none afterPending = .ok () afterDirectory
  directoryView : view.ClearsCache phase active pending cachedDirectory .directory (drops .directory) afterPending afterDirectory
  closed : calls.set phase .closed afterDirectory = .ok () afterPhase
  closedPhase : view.phase afterPhase phase = some .closed
  phaseFrame : view.cacheAt afterPhase cachedDirectory active pending = view.cacheAt afterDirectory cachedDirectory active pending ∧
    view.files afterPhase = view.files afterDirectory ∧ view.descriptors afterPhase = view.descriptors afterDirectory

namespace OpenCloseClears

variable {view : OpenCloseHeapView heap image} {calls : OpenCloseCallbacks heap}
  {drops : CloseCacheField → List LockReferenceDrop} {unlocked : heap}

private theorem projectsClosed (seen : OpenCloseClears drops view calls phase active pending cachedDirectory unlocked)
    (atUnlock : view.Matches phase active pending cachedDirectory unlocked start) :
    view.Matches phase active pending cachedDirectory seen.afterPhase (start.finishClears drops) := by
  have atDirectory := seen.directoryView (seen.pendingView (seen.activeView atUnlock))
  exact ⟨seen.closedPhase, seen.phaseFrame.1.trans atDirectory.2.1,
    seen.phaseFrame.2.1.trans atDirectory.2.2.1, seen.phaseFrame.2.2.trans atDirectory.2.2.2⟩

theorem emptyCache (seen : OpenCloseClears drops view calls phase active pending cachedDirectory unlocked)
    (atUnlock : view.Matches phase active pending cachedDirectory unlocked start) :
    view.phase seen.afterPhase phase = some .closed ∧ view.active seen.afterPhase active = none ∧
      view.pending seen.afterPhase pending = [] ∧ view.directory seen.afterPhase cachedDirectory = none := by
  have cleared := (seen.projectsClosed atUnlock).2.1
  rw [show (start.finishClears drops).files.image.1 = ⟨none, none, []⟩ from rfl] at cleared
  simp only [OpenCloseHeapView.cacheAt, Cache.mk.injEq, Option.map_eq_none_iff, List.map_eq_nil_iff] at cleared
  exact ⟨seen.closedPhase, cleared.2.1, cleared.2.2, cleared.1⟩

/-- Compose the raw unlock and reached setters. The final file state
and census follow from their projections and the phase setter's frame. -/
theorem returnsAfterUnlock {before : heap}
    (seen : OpenCloseClears drops view calls phase active pending cachedDirectory unlocked)
    (loaded : calls.getPhase phase before = .ok start.phase before) (openPhase : start.phase ≠ .closed)
    (returned : calls.unlock lock before = .ok () unlocked)
    (atUnlock : view.Matches phase active pending cachedDirectory unlocked start) :
    closeSchedule (calls.getPhase phase) (fun _ => calls.unlock lock)
      (calls.set active none) (calls.set pending []) (calls.set cachedDirectory none)
      (calls.set phase .closed) before = .ok () seen.afterPhase ∧
    view.Matches phase active pending cachedDirectory seen.afterPhase (start.finishClears drops) := by
  refine ⟨?_, seen.projectsClosed atUnlock⟩
  cases opened : start.phase <;>
    simp_all [closeSchedule, Phase.close, Bind.bind, EStateM.bind, seen.activeCleared,
      seen.pendingCleared, seen.directoryCleared, seen.closed]

end OpenCloseClears

/-- Reindex the reported drops to the literal starting heap. An
explicit unlock releases the old lock even if an alias remains live. -/
theorem OpenCloseHeapView.Matches.closedFrom {view : OpenCloseHeapView heap image} {before after : heap}
    {drops : CloseCacheField → List LockReferenceDrop}
    (atStart : view.Matches phase active pending cachedDirectory before start)
    (atClose : view.Matches phase active pending cachedDirectory after ((start.release directory writer).finishClears drops))
    (held : start.files.owners.Owns directory writer) :
    view.ClosedFrom phase active pending cachedDirectory directory drops before after := by
  obtain ⟨phaseClosed, empty, files, inventory⟩ := atClose
  refine ⟨phaseClosed, empty, ?_, ?_⟩
  · rw [atStart.2.2.1]
    simpa only [CachedCloseState.finishClears, CachedCloseState.drop, CachedCloseState.release,
      LockOwners.release_owned held] using files
  · rw [atStart.2.2.2]
    simpa only [CachedCloseState.finishClears, CachedCloseState.drop, CachedCloseState.release,
      DescriptorInventory.afterDrops_append, List.append_assoc] using inventory

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
    Nonempty (OpenCloseClears report.drops view calls phase active pending cachedDirectory afterUnlock)

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
  | .ok () => ∃ clears : OpenCloseClears report.drops view calls phase active pending cachedDirectory seen.afterUnlock,
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
    have projected := seen.unlockedView
    rw [outcome] at returned projected
    obtain ⟨schedule, finalView⟩ :=
      clears.returnsAfterUnlock (start := start.release directory writer) seen.loaded openPhase returned projected
    exact ⟨clears, schedule, finalView⟩

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
