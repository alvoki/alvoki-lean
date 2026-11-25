import Alvoki.Storage.Disk.NativeExecutionPendingWrite
import Alvoki.Storage.Disk.NativeReadyClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- The native unlock callback is issued on a live slot for the stable
lock inode. Its effect is observed separately from the interrupted IO
return. The outer error marks the stopped call, and an inner error
would instead be a diagnostic returned to the caller. -/
structure NativeCloseUnlockInterruption {handle image : Type} (directory : DiskDirectory) (writer : Nat)
    (before : CachedCloseState handle image) where
  slot : DescriptorSlot
  description : slot.description = writer
  enteredLive : slot ∈ before.descriptors.slots
  issueCensus : DescriptorInventory
  issued : LockCensusTrace directory writer before.descriptors before.files issueCensus before.files
  issuedLive : slot ∈ issueCensus.slots
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (issueCensus.inode slot.description)
  effective : Bool
  unlock : DescriptorSlot → ExceptT IO.Error (EStateM DescriptorSlot (CachedCloseState handle image)) Unit
  stops :
    let reached := { before with descriptors := issueCensus }
    (unlock slot).run before = .error slot (if effective then reached.release directory writer else reached)

namespace NativeCloseUnlockInterruption

variable {handle image : Type} {directory : DiskDirectory} {writer : Nat}
  {before : CachedCloseState handle image}

def atCut (cut : NativeCloseUnlockInterruption directory writer before) : CachedCloseState handle image :=
  let reached := { before with descriptors := cut.issueCensus }
  if cut.effective then reached.release directory writer else reached

def run (cut : NativeCloseUnlockInterruption directory writer before)
    (clear : CloseCacheField → ExceptT IO.Error (EStateM DescriptorSlot (CachedCloseState handle image)) Unit) :
    EStateM.Result DescriptorSlot (CachedCloseState handle image) (Except IO.Error Unit) :=
  (closeSchedule (ExceptT.lift (fun reached => .ok reached.phase reached))
    (fun _ => cut.unlock cut.slot) (clear .active) (clear .pending) (clear .directory)
    (ExceptT.lift (modify fun reached => { reached with phase := .closed }))).run before

/-- The production close schedule stops at its original unlock call.
The phase and cache still belong to the session that issued it. The
issued census includes any reported slot events during the callback,
such as a private fork before the raw unlock effect. -/
theorem reachesUnlock (cut : NativeCloseUnlockInterruption directory writer before)
    (openPhase : before.phase ≠ .closed)
    (clear : CloseCacheField → ExceptT IO.Error (EStateM DescriptorSlot (CachedCloseState handle image)) Unit) :
    cut.run clear = .error cut.slot cut.atCut ∧ cut.atCut.phase = before.phase ∧
    cut.atCut.files.image = before.files.image ∧ cut.atCut.descriptors = cut.issueCensus ∧
    cut.slot ∈ before.descriptors.slots ∧ cut.slot ∈ cut.atCut.descriptors.slots := by
  have stops : cut.unlock cut.slot before = .error cut.slot cut.atCut := cut.stops
  refine ⟨?_, ?_, ?_, ?_, cut.enteredLive, ?_⟩
  · cases phase : before.phase with
    | closed => exact False.elim (openPhase phase)
    | ready | poisoned =>
      simp [run, closeSchedule, phase, Phase.close, ExceptT.lift, Bind.bind, ExceptT.bind, ExceptT.bindCont,
        ExceptT.mk, ExceptT.run, Functor.map, EStateM.map, EStateM.bind, stops]
  · simp only [atCut]; split <;> rfl
  · simp only [atCut]; split <;> rfl
  · simp only [atCut]; split <;> rfl
  · simp only [atCut]; split <;> exact cut.issuedLive

/-- After the interrupted call, account for observed close, exec and
process exit events on the same census. If the explicit unlock already
took effect, slot drops leave that lock vacant. Otherwise the old
description keeps ownership until its last reference is gone.
The interval keeps the lock binding fixed and has only slot drops. -/
def afterDrops (cut : NativeCloseUnlockInterruption directory writer before) (drops : List LockReferenceDrop) :
    CachedCloseState handle image :=
  { cut.atCut with
    descriptors := cut.issueCensus.afterDrops drops
    files := if cut.effective then cut.atCut.files
      else cut.issueCensus.dropLockState writer drops directory before.files }

/-- The reported effect and exact remaining reference list determine
ownership. Neither choice changes the cached handles or physical bytes. -/
theorem filesAfterDrops (cut : NativeCloseUnlockInterruption directory writer before)
    (drops : List LockReferenceDrop) :
    (cut.afterDrops drops).files =
      if cut.effective = true ∨ (cut.issueCensus.afterDrops drops).references writer = [] then
        ⟨before.files.image, before.files.owners.set (directory.file .lock) none⟩
      else before.files := by
  cases effect : cut.effective
  · have trace := LockCensusTrace.drops cut.issued drops
    simpa only [afterDrops, effect, Bool.false_eq_true, ite_false, false_or] using trace.reached.2.2
  · simp only [afterDrops, atCut, effect, ite_true, true_or, CachedCloseState.release,
      LockOwners.release_owned cut.issued.reached.1]

theorem admitsAfterDrops (cut : NativeCloseUnlockInterruption directory writer before)
    (drops : List LockReferenceDrop) :
    TryLockObserves (cut.afterDrops drops).files.owners directory (.ok true) ↔
      cut.effective = true ∨ (cut.afterDrops drops).descriptors.references writer = [] := by
  rw [cut.filesAfterDrops drops]
  change _ ↔ cut.effective = true ∨ (cut.issueCensus.afterDrops drops).references writer = []
  split
  · simp [TryLockObserves, LockOwners.set, *]
  · have held := cut.issued.reached.1
    simp only [TryLockObserves, LockOwners.Owns] at held ⊢
    simp [*]

/-- Reopen consumes the selected physical image and owner, without
passing the stopped session's cache to the new attempt. -/
def reopenFiles (cut : NativeCloseUnlockInterruption directory writer before) (drops : List LockReferenceDrop) :
    LockedFileState image :=
  let files := (cut.afterDrops drops).files
  ⟨files.image.2, files.owners⟩

theorem reopenFiles_image (cut : NativeCloseUnlockInterruption directory writer before)
    (drops : List LockReferenceDrop) :
    (cut.reopenFiles drops).image = before.files.image.2 := by
  simp only [reopenFiles, cut.filesAfterDrops drops]
  split <;> rfl

/-- If the old lock is still held, a reported acquisition on the same
lock cannot enter recovery. Its exact reached files survive the call. -/
theorem blocksOpen (cut : NativeCloseUnlockInterruption directory writer before)
    (drops : List LockReferenceDrop)
    (notEffective : cut.effective = false) (aliased : (cut.afterDrops drops).descriptors.references writer ≠ [])
    (descriptor : Nat) (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (recover : EStateM IO.Error image α)
    (reported : TryLockObserves (cut.reopenFiles drops).owners directory acquired) :
    ∃ cause, runOpenWithImage directory descriptor acquired unlock recover (cut.reopenFiles drops) =
      .error cause (cut.reopenFiles drops) := by
  apply runOpenWithImage_notAcquired
  intro took
  obtain effective | gone := (cut.admitsAfterDrops drops).mp (took ▸ reported)
  · simp [notEffective] at effective
  · exact aliased gone

end NativeCloseUnlockInterruption

/-- The interrupted ordinary close uses the owner of the exact reached
ready session. The old history explains every recorded response. -/
theorem NativeReadPosition.stopsDuringClose (current : NativeReadPosition history log)
    (cut : NativeCloseUnlockInterruption current.state.session.directory current.state.session.descriptor current.state.closeState)
    (owner : cut.slot = current.state.owner)
    (clear : CloseCacheField → ExceptT IO.Error
      (EStateM DescriptorSlot (CachedCloseState CheckpointOpenHandle FileImage)) Unit) :
    cut.run clear = .error current.state.owner cut.atCut ∧ cut.atCut.phase = .ready current.state.writer.installed ∧
    cut.atCut.files.image = (current.state.cache, current.state.files.image) ∧
    cut.atCut.descriptors = cut.issueCensus ∧ current.state.owner ∈ cut.atCut.descriptors.slots ∧
    cut.issueCensus.inode = current.state.census.inode ∧
    cut.bindings (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description) ∧
    PendingClientReplay log current.reads history ∧ ∀ read ∈ current.reads, read.BoundedBy history.length := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨stopped, phase, files, inventory, _, live⟩ := cut.reachesUnlock
    (by change current.state.session.phase ≠ .closed; rw [valid.phase]; simp) clear
  have inodes := cut.issued.reached.2.1
  have binding := cut.lockObject
  rw [inodes, owner] at binding
  exact ⟨owner ▸ stopped, phase.trans valid.phase, files, inventory, owner ▸ live, inodes, binding, replay,
    current.readPrefix.readsBounded⟩

/-- The interrupted poisoned close issues on the owner of the returned
unknown write. The same physical write cut retains its old-or-whole
marker selection and earlier bounded responses. -/
theorem NativePendingWrite.stopsDuringClose {current : NativeReadPosition history log}
    (pending : NativePendingWrite current)
    (cut : NativeCloseUnlockInterruption current.state.session.directory current.state.session.descriptor pending.poisoned)
    (owner : cut.slot = current.state.owner)
    (clear : CloseCacheField → ExceptT IO.Error
      (EStateM DescriptorSlot (CachedCloseState CheckpointOpenHandle WriteFiles)) Unit) :
    cut.run clear = .error current.state.owner cut.atCut ∧ cut.atCut.phase = .poisoned ∧
    cut.atCut.files.image = (pending.cache, pending.write.failure.failed) ∧
    cut.atCut.descriptors = cut.issueCensus ∧ current.state.owner ∈ cut.atCut.descriptors.slots ∧
    cut.issueCensus.inode = pending.observed.reached.inode ∧
    cut.bindings (current.state.session.directory.file .lock) =
      pending.observed.bindings (current.state.session.directory.file .lock) ∧
    ∃ chosen,
      (chosen = history ∨ chosen = history ++ pending.write.failure.batch) ∧
      pending.files.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      PendingClientReplay pending.submissions current.reads chosen ∧
      ∀ read ∈ current.reads, read.BoundedBy chosen.length := by
  obtain ⟨stopped, phase, files, inventory, _, live⟩ :=
    cut.reachesUnlock (by simp [poisoned, ObservedBatchFailure.closeState]) clear
  have inodes := cut.issued.reached.2.1
  have binding := cut.lockObject
  rw [inodes, owner] at binding
  exact ⟨owner ▸ stopped, phase, files, inventory, owner ▸ live, inodes, binding.trans pending.observed.lockBound.symm,
    pending.selectsAtReturn⟩

end Alvoki.Storage.DiskSession
