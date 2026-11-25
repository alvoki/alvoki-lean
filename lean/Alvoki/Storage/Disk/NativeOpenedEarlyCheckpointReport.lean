import Alvoki.Storage.Disk.NativeStoppedRunDirectoryTableOpen
import Alvoki.Storage.Disk.NativeStoppedRunFileTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The original opened checkpoint issues either the selected run fsync
or the first directory fsync. Each case fixes the logical reboot to the
same raw cut. -/
inductive RawEarlyCheckpointStop (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage) :
    NativeEarlyCheckpointReboot current.current.ready.state → Type where
  | file {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
      {stop : NativeCheckpointRunFileStop (image := heap) current.current.ready.state cut}
      {reboot : NativeCheckpointRunFileReboot stop} (raw : RawCheckpointRunFileStop current stop view) :
      RawEarlyCheckpointStop current view (.file reboot)
  | directory {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
      {stop : NativeCheckpointRunDirectoryStop (image := heap) current.current.ready.state cut}
      {reboot : NativeCheckpointRunDirectoryReboot stop} (raw : RawCheckpointRunDirectoryStop current stop view) :
      RawEarlyCheckpointStop current view (.directory reboot)

namespace RawEarlyCheckpointStop

variable {current : NativeOpenedPosition opened} {view : OpenCloseHeapView heap FileImage}
  {recovery : NativeEarlyCheckpointReboot current.current.ready.state} (seen : RawEarlyCheckpointStop current view recovery)

def stoppedHeap : heap :=
  match seen with
  | .file (stop := stop) _ => stop.effect.after
  | .directory (stop := stop) _ => stop.reached

def census : DescriptorInventory :=
  match seen with
  | .file (stop := stop) _ => stop.effect.handle.1
  | .directory _ => current.current.ready.state.census

def files : LockedFileState FileImage :=
  match seen with
  | .file _ => current.current.ready.state.files
  | .directory (stop := stop) _ => ⟨stop.runs.files stop.reached, current.current.ready.state.files.owners⟩

include seen in
theorem samePhase : view.phase = opened.contents := by
  cases seen with
  | file raw => exact raw.samePhase
  | directory raw => exact raw.samePhase

/-- The actual raw sync group uses either the consumed pending run slot
or the cached directory slot. Their outer stops issue no public return. -/
def Issued : Prop :=
  match seen with
  | .file (stop := stop) raw =>
    stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
      .error stop.effect.path (stop.effect.prior.atRun 0, current.current.ready.state.cache, stop.effect.after) ∧
    (∀ getDirectory getActive openRead, raw.group getDirectory getActive openRead stop.effect.flushed =
      .error stop.effect.path stop.effect.after) ∧
    view.cacheAt raw.afterConsume raw.directory raw.active raw.pending = current.current.ready.state.cache ∧
    view.descriptors raw.afterConsume = stop.effect.handle.1 ∧
    stop.effect.handle.2.1 ∈ (view.descriptors stop.effect.after).slots
  | .directory (stop := stop) raw =>
    stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
      .error current.current.ready.state.session.directory.path
        (stop.runs.atRun 0, current.current.ready.state.cache, stop.reached) ∧
    (∀ pending setPending active openRead, raw.group pending setPending active openRead stop.atIssue =
      .error current.current.ready.state.session.directory.path stop.reached)

/-- The old table is poisoned and still holds its lock at the actual
issued stop, with the cut's exact descriptor census and files. -/
structure Reached : Prop where
  source : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory opened.files opened.phase
  phase : view.phase seen.stoppedHeap opened.phase = some .poisoned
  oldLock : (view.handle seen.stoppedHeap opened.lock).2.1 = current.current.ready.state.owner
  stoppedFiles : (view.descriptors seen.stoppedHeap, view.files seen.stoppedHeap) = (seen.census, seen.files)
  issued : seen.Issued

theorem reaches : seen.Reached := by
  cases seen with
  | @file _ stop _ raw =>
    obtain ⟨source, phase, outer, lock, files⟩ := raw.reached
    have live := (stop.custody current.current.ready.readPrefix.refines.1).2.1
    rw [← raw.census] at live
    exact ⟨source, phase, lock, files, outer, raw.stopsGroup, raw.cleared, raw.stillHeld, live⟩
  | directory raw =>
    obtain ⟨source, phase, outer, lock, files⟩ := raw.reached
    exact ⟨source, phase, lock, files, outer, raw.stopsGroup⟩

end RawEarlyCheckpointStop

/-- One selected reader and one raw reopening after the actual early
checkpoint stop. The retained checkpoint remains the old selection. -/
structure NativeOpenedEarlyCheckpointReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  recovery : NativeEarlyCheckpointReboot current.current.ready.state
  stopped : RawEarlyCheckpointStop current view recovery
  layout : CanonicalKeeperLayout (recovery.observed current.current.ready.readPrefix.refines.1).retry.image
    current.current.ready.state.writer.history
  target : layout.target = current.current.ready.state.writer.target
  keeper : layout.keeper = current.current.ready.state.writer.wal.active
  descriptors : layout.sealed ++ [layout.keeper] = current.current.ready.state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared (recovery.observed current.current.ready.readPrefix.refines.1).retry.image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
    (recovery.observed current.current.ready.readPrefix.refines.1).retry.image.directory.active.manifest
    current.current.ready.state.writer.checkpoint
  reader : NativeReadyRestartReads (recovery.observed current.current.ready.readPrefix.refines.1) input layout selected
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  raw : RawQuietRestartEffects reader view calls init names bytes stopped.stoppedHeap rebooted phaseIdentity tokenIdentity
    allocatePhase allocateToken stream stopped.census
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

namespace NativeOpenedEarlyCheckpointReport

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  (seen : NativeOpenedEarlyCheckpointReport current input view names bytes)

def event : NativeExecutionEvent := seen.recovery.event input

/-- The next trace uses the literal handle and position produced by the
shared aligned opener. Both cut branches enter the same continuation. -/
inductive Returned : {handle : NativeOpenedHandle heap} → NativeOpenedPosition handle → Prop where
  | selected (stopped : seen.stopped.Reached)
      (reopened : RawQuietRestartEffects.ReopenedSelected current.current.ready seen.raw seen.remove seen.write seen.rename
        seen.bootstrap seen.assemble opened.get opened.set opened.ptrEq)
      (step : NativeExecutionStep current.current seen.event reopened.installed.start.current) :
      Returned reopened.installed.start

theorem Returned.common {handle : NativeOpenedHandle heap} {start : NativeOpenedPosition handle}
    (returned : seen.Returned start) : NativeExecutionStep current.current seen.event start.current := by
  cases returned with
  | selected _ _ step => exact step

theorem reaches : ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  let effects : OpenPhaseCellEffects view.phase opened.get opened.set := seen.stopped.samePhase.symm ▸ opened.phaseEffects
  obtain ⟨reopened⟩ := RawQuietRestartEffects.reopensSelected current.current.ready seen.raw seen.remove seen.write
    seen.rename seen.bootstrap seen.assemble opened.ptrEq seen.target seen.keeper seen.descriptors seen.offsets seen.prepared
    seen.constructs effects
  have step : NativeExecutionStep current.current seen.event reopened.installed.start.current := by
    rw [reopened.installed.position]
    exact .recoverInterruptedEarlyCheckpoint current.current seen.recovery (valid := current.current.ready.readPrefix.refines.1)
      seen.reader reopened.next reopened.sameReader reopened.session reopened.sameReads
  exact ⟨reopened.installed.handle, reopened.installed.start, .selected seen.stopped.reaches reopened step⟩

end NativeOpenedEarlyCheckpointReport
end Alvoki.Storage.DiskSession
