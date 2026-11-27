import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.WAL.Boundary

open Storage

/-- An interrupted fresh-stage write can leave the previous scratch alone
or leave observable unsynced bytes at the staging name. -/
inductive StagedWriteInterruption where
  | unchanged
  | unsynced (contents : Option ByteArray)

/-- The marker primitive reached after the frame append completed. These
observations describe effects before a power loss while that callback is
still in flight. -/
inductive MarkerInterruption where
  | stage (effect : StagedWriteInterruption)
  | groupSync (wal : WalSyncEffect) (stagedSynced : Bool)
  | rename (applied : Bool)
  | directorySync (applied : Bool)

namespace MarkerInterruption

def action : MarkerInterruption → Publication.Step
  | .stage _ => .writeStaged
  | .groupSync _ _ => .syncStaged
  | .rename _ => .renameStaged
  | .directorySync _ => .syncDirectory

def index : MarkerInterruption → Nat
  | .stage _ => 0
  | .groupSync _ _ => 1
  | .rename _ => 2
  | .directorySync _ => 3

theorem actionAt (cut : MarkerInterruption) :
    Publication.steps[cut.index]? = some cut.action := by
  cases cut <;> rfl

private def completedEffects (appendCrashTails : List ByteArray) : WriteEffects :=
  ⟨.ok (), appendCrashTails, .ok (), .ok (), .success, .success⟩

private def stopAfter (applied : Bool) : OperationResult :=
  if applied then .errorAfterEffect else .errorBeforeEffect

/-- Encode the same cut in the existing effect interpreter. Its stopping
tags are consumed only to project physical file effects. -/
def writeEffects (cut : MarkerInterruption) (appendCrashTails : List ByteArray)
    (scratch : Option (ByteArray × Bool)) : WriteEffects :=
  let completed := completedEffects appendCrashTails
  match cut with
  | .stage .unchanged => { completed with stage := .error (scratch.map Prod.fst) }
  | .stage (.unsynced bytes) => { completed with stage := .error bytes }
  | .groupSync wal stagedSynced => { completed with sync := .error ⟨wal, stagedSynced⟩ }
  | .rename applied => { completed with rename := stopAfter applied }
  | .directorySync applied => { completed with directorySync := stopAfter applied }

/-- Interpret the completed append and the marker steps before the
interrupted callback. Single writes and batches share this prefix. -/
def reachedWith (cut : MarkerInterruption) (history : List WAL.Write) (marker : ByteArray)
    (appendCrashTails : List ByteArray) (scratch : Option (ByteArray × Bool))
    (append : WriteEffects → EStateM Unit WriteFiles Unit) : WriteFiles :=
  let completed := completedEffects appendCrashTails
  writeFilesAfter (commit (append completed)
    ((Publication.steps.take cut.index).forM (completed.markerStep marker)) (WriteFiles.initial history scratch))

/-- The single-frame append and the marker primitives preceding the
interrupted callback have taken effect. -/
def reached (cut : MarkerInterruption) (history : List WAL.Write) (event : WAL.Write)
    (appendCrashTails : List ByteArray) (scratch : Option (ByteArray × Bool)) : WriteFiles :=
  let marker := encode (WAL.encode (history ++ [event])).size.toUInt64
  cut.reachedWith history marker appendCrashTails scratch (·.appendFrame event)

/-- Apply the possible physical effect of the reached callback. The
unchanged stage case keeps any existing scratch bytes and their sync bit. -/
def interrupt (cut : MarkerInterruption) (marker : ByteArray) (before : WriteFiles) : WriteFiles :=
  match cut with
  | .stage .unchanged => before
  | _ => writeFilesAfter ((cut.writeEffects [] none).markerStep marker cut.action before)

/-- The exact reached prefix and optional in-flight effects have the
same live and crash WAL candidates and marker bindings as one cut in the
write-effect model. Power loss drops the marker scratch. No outcome from
the interrupted callback or from the write is required. -/
theorem matchesWriteEffects (cut : MarkerInterruption) (history : List WAL.Write) (event : WAL.Write)
    (appendCrashTails : List ByteArray) (scratch : Option (ByteArray × Bool)) :
    let marker := encode (WAL.encode (history ++ [event])).size.toUInt64
    let reached := cut.reached history event appendCrashTails scratch
    let actual := cut.interrupt marker reached
    let modeled := writeFilesAfter (runWriteEffects history event (cut.writeEffects appendCrashTails scratch) scratch)
    actual.visibleTail = modeled.visibleTail ∧ actual.crashTails = modeled.crashTails ∧
      actual.marker.active = modeled.marker.active ∧ actual.marker.crashImages = modeled.marker.crashImages := by
  cases cut with
  | stage impact => cases impact <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | groupSync wal stagedSynced => cases wal <;> cases stagedSynced <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | rename applied => cases applied <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | directorySync applied => cases applied <;> exact ⟨rfl, rfl, rfl, rfl⟩

end MarkerInterruption

end Alvoki.WAL.Boundary
