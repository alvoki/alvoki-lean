import Alvoki.Storage.Disk.NativeEarlyCheckpointStop

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

namespace RawEarlyCheckpointStop

variable {current : NativeOpenedPosition opened} {view : OpenCloseHeapView heap FileImage}
  (seen : RawEarlyCheckpointStop current view)

/-- A continuation may select a survivor of this particular stopped effect. -/
def Reboot : Type :=
  match seen with
  | .file (stop := stop) _ => NativeCheckpointRunFileReboot stop
  | .directory (stop := stop) _ => NativeCheckpointRunDirectoryReboot stop

def recovery : seen.Reboot → NativeEarlyCheckpointReboot current.current.ready.state :=
  match seen with
  | .file _ => fun selected => .file selected
  | .directory _ => fun selected => .directory selected

end RawEarlyCheckpointStop

/-- One selected reader and one raw reopening after the actual early
checkpoint stop. The retained checkpoint remains the old selection. -/
structure NativeOpenedEarlyCheckpointReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  stopped : RawEarlyCheckpointStop current view
  survivor : stopped.Reboot
  layout : CanonicalKeeperLayout ((stopped.recovery survivor).observed current.current.ready.readPrefix.refines.1).retry.image
    current.current.ready.state.writer.history
  target : layout.target = current.current.ready.state.writer.target
  keeper : layout.keeper = current.current.ready.state.writer.wal.active
  descriptors : layout.sealed ++ [layout.keeper] = current.current.ready.state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared ((stopped.recovery survivor).observed current.current.ready.readPrefix.refines.1).retry.image
    layout.target layout.plan
  selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
    ((stopped.recovery survivor).observed current.current.ready.readPrefix.refines.1).retry.image.directory.active.manifest
    current.current.ready.state.writer.checkpoint
  reader : NativeReadyRestartReads ((stopped.recovery survivor).observed current.current.ready.readPrefix.refines.1)
    input layout selected
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

def recovery : NativeEarlyCheckpointReboot current.current.ready.state := seen.stopped.recovery seen.survivor

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
