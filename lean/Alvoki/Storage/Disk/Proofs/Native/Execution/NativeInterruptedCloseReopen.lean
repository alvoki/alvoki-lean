import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeCloseUnlockInterruption
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeCloseUnlockInterruption

variable {handle image : Type} {directory : DiskDirectory} {writer : Nat}
  {before : CachedCloseState handle image}

theorem releasedReopenFiles (cut : NativeCloseUnlockInterruption directory writer before)
    (drops : List LockReferenceDrop)
    (released : cut.effective = true ∨ (cut.afterDrops drops).descriptors.references writer = []) :
    cut.reopenFiles drops = ⟨before.files.image.2, before.files.owners.set (directory.file .lock) none⟩ := by
  change cut.effective = true ∨ (cut.issueCensus.afterDrops drops).references writer = [] at released
  simp only [reopenFiles, cut.filesAfterDrops drops, ite_eq_left released]

/-- A reported exit removes all slots from the issuing process table,
while an inherited slot in a different process can still survive. -/
theorem excludesExitedProcess (cut : NativeCloseUnlockInterruption directory writer before)
    {drops : List LockReferenceDrop} {process : Nat} (exited : LockReferenceDrop.exited process ∈ drops) :
    ∀ slot ∈ (cut.afterDrops drops).descriptors.slots, slot.reference.process ≠ process := by
  intro slot present same
  have kept := (List.mem_filter.mp present).2
  have stayed := List.all_eq_true.mp kept (.exited process) exited
  simp [LockReferenceDrop.removes, same] at stayed

end NativeCloseUnlockInterruption

/-- A reported process exit follows the stopped unlock. Later observed
slot drops reach vacancy even when the issued explicit unlock had no
effect. An effective unlock can leave inherited lock slots open. -/
structure NativeInterruptedCloseReopenObservation (state : NativeReadyState) (input : FilePath) where
  cut : NativeCloseUnlockInterruption state.session.directory state.session.descriptor state.closeState
  owner : cut.slot = state.owner
  drops : List LockReferenceDrop
  exited : LockReferenceDrop.exited cut.slot.reference.process ∈ drops
  released : cut.effective = true ∨ (cut.afterDrops drops).descriptors.references state.session.descriptor = []
  files : NativeCloseFiles state
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
    Nonempty (NativeCloseAlignedReads files input (cut.afterDrops drops).descriptors plan.layout selected)

namespace NativeInterruptedCloseReopenObservation

variable {state : NativeReadyState} {input : FilePath}

/-- The final attempt sees the same selected files and now-vacant owner
map. The issued slot is gone even when another process keeps an alias. -/
theorem followsExit (seen : NativeInterruptedCloseReopenObservation state input) :
    (∀ slot ∈ (seen.cut.afterDrops seen.drops).descriptors.slots, slot.reference.process ≠ state.owner.reference.process) ∧
    (seen.cut.afterDrops seen.drops).descriptors.inode = state.census.inode ∧
    seen.cut.bindings (state.session.directory.file .lock) = seen.files.names (state.session.directory.file .lock) ∧
    seen.cut.reopenFiles seen.drops = state.releasedFiles ∧
    TryLockObserves (seen.cut.reopenFiles seen.drops).owners state.session.directory (.ok true) := by
  have inodes := seen.cut.issued.reached.2.1
  have original := seen.cut.lockObject
  rw [inodes, seen.owner] at original
  exact ⟨seen.owner ▸ seen.cut.excludesExitedProcess seen.exited, inodes,
    original.trans seen.files.lock.symm, seen.cut.releasedReopenFiles seen.drops seen.released,
    (seen.cut.admitsAfterDrops seen.drops).mpr seen.released⟩

/-- The reached cutoff and exact release before the healthy open. -/
def Reached (seen : NativeInterruptedCloseReopenObservation state input) : Prop :=
  (∀ clear, seen.cut.run clear = .error state.owner seen.cut.atCut) ∧
  seen.cut.atCut.phase = .ready state.writer.installed ∧
  seen.cut.atCut.files.image = (state.cache, state.files.image) ∧
  seen.cut.atCut.descriptors = seen.cut.issueCensus ∧ state.owner ∈ seen.cut.atCut.descriptors.slots ∧
  (∀ slot ∈ (seen.cut.afterDrops seen.drops).descriptors.slots, slot.reference.process ≠ state.owner.reference.process) ∧
  (seen.cut.afterDrops seen.drops).descriptors.inode = state.census.inode ∧
  seen.cut.bindings (state.session.directory.file .lock) = seen.files.names (state.session.directory.file .lock) ∧
  seen.cut.reopenFiles seen.drops = state.releasedFiles ∧
  TryLockObserves (seen.cut.reopenFiles seen.drops).owners state.session.directory (.ok true)

end NativeInterruptedCloseReopenObservation

/-- The interrupted call issued the original unlock and returned no IO
diagnostic. Its later reference drops supply the actual healthy opener's
inventory and files. The same selected reads and aligned barriers yield
the exact fresh session and preserve the previous client replay. -/
theorem NativeReadPosition.reopensAfterInterruptedClose (current : NativeReadPosition history log)
    (seen : NativeInterruptedCloseReopenObservation current.state input) :
    seen.Reached ∧
    NativeCloseAlignedResult seen.files input (seen.cut.afterDrops seen.drops).descriptors history log current.reads := by
  let stopped := current.stopsDuringClose seen.cut seen.owner
  have atCut := stopped (fun _ => pure ())
  obtain ⟨_, phase, cache, census, live, _, _, _, _⟩ := atCut
  obtain ⟨absent, inodes, lock, files, vacant⟩ := seen.followsExit
  exact ⟨⟨fun clear => (stopped clear).1, phase, cache, census, live, absent, inodes, lock, files, vacant⟩,
    current.readPrefix.reopensReleasedAligned seen.files seen.observe⟩

/-- Continue the same client ledger in the exact new session. The
prescribed input is the one used by the next reported admission. -/
structure NativeInterruptedCloseReopenContinuation (current next : NativeReadPosition history log)
    {input : FilePath} (seen : NativeInterruptedCloseReopenObservation current.state input) : Prop where
  stopped : seen.Reached
  exited : LockReferenceDrop.exited current.state.owner.reference.process ∈ seen.drops
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  pair : next.state.files.image.directory.active = current.state.files.image.directory.active
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (opened : NativeCloseAlignedReads seen.files input (seen.cut.afterDrops seen.drops).descriptors plan.layout selected),
    opened.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = opened.run ∧ next.initial = next.state ∧
    next.state.owner = opened.opening.admission.owner ∧ next.state.directorySlot = opened.opening.admission.cached ∧
    next.state.cache = opened.opening.admission.cache ∧ next.state.census = opened.opening.finish.census ∧
    NativeCloseSelectedReads opened

theorem NativeReadPosition.recoversInterruptedClose (current : NativeReadPosition history log)
    (seen : NativeInterruptedCloseReopenObservation current.state input) :
    ∃ next, NativeInterruptedCloseReopenContinuation current next seen := by
  obtain ⟨stopped, aligned⟩ := current.reopensAfterInterruptedClose seen
  obtain ⟨plan, selected, opened, state, continued, directory, owner, directorySlot, cache, census,
    sessionFresh, phaseFresh, lock, root, pair, kept, target, checkpoint, durable, manifestMissing, manifest,
    runs, marker, wal, _⟩ := aligned
  let next : NativeReadPosition history log := ⟨opened.run, state, state, current.reads, continued⟩
  exact ⟨next, stopped, seen.owner ▸ seen.exited, rfl, ⟨directory, root, lock, target, checkpoint, durable⟩,
    sessionFresh, phaseFresh,
    pair, kept, plan, selected, opened, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census,
    ⟨manifestMissing, manifest, runs, marker, wal⟩⟩

end Alvoki.Storage.DiskSession
