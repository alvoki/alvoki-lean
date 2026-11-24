import Alvoki.Storage.Disk.WalBatchCommitEffects
import Alvoki.Storage.Disk.WalSegmentMarkerPowerLoss

namespace Alvoki.WAL.Boundary.MarkerInterruption

open Storage WalSegmentCommit

/-- The complete batch append and the marker callbacks before the
interrupted step have taken effect. The staged marker is for the whole batch. -/
def reachedBatch (cut : MarkerInterruption) (history batch : List WAL.Write)
    (appendCrashTails : List ByteArray) (scratch : Option (ByteArray × Bool)) : WriteFiles :=
  let marker := encode (WAL.encode (history ++ batch)).size.toUInt64
  cut.reachedWith history marker appendCrashTails scratch (appendBatch · batch)

/-- A stopped batch publication has the same WAL tails and marker choices
as the corresponding cut in the batch effect interpreter. The projection
uses the completed prefix and the in-flight effects before any return.
The marker bindings and tails supply the candidates for power loss. -/
theorem matchesBatchEffects (cut : MarkerInterruption) (history batch : List WAL.Write)
    (appendCrashTails : List ByteArray) (scratch : Option (ByteArray × Bool)) :
    let marker := encode (WAL.encode (history ++ batch)).size.toUInt64
    let reached := cut.reachedBatch history batch appendCrashTails scratch
    let actual := cut.interrupt marker reached
    let modeled := writeFilesAfter (runBatchEffects history batch (cut.writeEffects appendCrashTails scratch) scratch)
    actual.visibleTail = modeled.visibleTail ∧ actual.crashTails = modeled.crashTails ∧
      actual.marker.active = modeled.marker.active ∧ actual.marker.crashImages = modeled.marker.crashImages := by
  cases cut with
  | stage impact => cases impact <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | groupSync wal stagedSynced => cases wal <;> cases stagedSynced <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | rename applied => cases applied <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | directorySync applied => cases applied <;> exact ⟨rfl, rfl, rfl, rfl⟩

end Alvoki.WAL.Boundary.MarkerInterruption
