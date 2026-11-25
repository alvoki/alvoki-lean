import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeInactiveSessionCalls
import Alvoki.Storage.Disk.NativeOpenSnapshotControls
import Alvoki.Storage.Disk.NativeOpenedFinalizedRetryReport

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotPin)

namespace NativeOpenedHandle

variable {heap : Type} (opened : NativeOpenedHandle heap)
  {before : heap} {mode : NativeInactivePhase}

def loadInstalled : EStateM IO.Error heap Installed := do
  (← opened.get opened.phase).installed

private theorem rejectsInstalled (stored : opened.contents before opened.phase = some mode.phase) :
    opened.loadInstalled before = .error mode.error before := by
  have loaded := opened.phaseEffects.reads before opened.phase _ stored
  simp only [loadInstalled, Bind.bind, EStateM.bind, loaded]
  cases mode <;> rfl

/-- A point or range request reads the original handle's phase. An
inactive phase returns its error before inspecting the supplied token or table. -/
theorem rejectsInactiveSnapshotRead
    (stored : opened.contents before opened.phase = some mode.phase)
    {pin : DiskSnapshotPin} {issuer : IO.Ref Unit} {issued : SnapshotPin}
    (owns : pin.UsesOpenToken issuer issued) (request : SnapshotReadRequest α) :
    (match request with
     | .lookup key => opened.table.lookup pin.handle key =
         readSnapshotWith (m := IO) (do (← opened.phase.get).installed)
           (issuer.ptrEq opened.token) (fun table => table.lookup issued.handle key)
     | .range lo hi => opened.table.range pin.handle lo hi =
         readSnapshotWith (m := IO) (do (← opened.phase.get).installed)
           (issuer.ptrEq opened.token) (fun table => table.range issued.handle lo hi)) ∧
    readSnapshotWith opened.loadInstalled (opened.ptrEq issuer opened.token)
      (request.read issued.handle) before = .error mode.error before := by
  refine ⟨?_, ?_⟩
  · cases request with
    | lookup key => exact opened.uses.lookupIssuedPin owns key
    | range lo hi => exact opened.uses.rangeIssuedPin owns lo hi
  · simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

/-- Releasing a supplied snapshot on an inactive handle leaves its
original phase cell untouched. -/
theorem rejectsInactiveSnapshotRelease
    (stored : opened.contents before opened.phase = some mode.phase)
    {pin : DiskSnapshotPin} {issuer : IO.Ref Unit} {issued : SnapshotPin}
    (owns : pin.UsesOpenToken issuer issued) :
    opened.table.release pin.handle = releaseSnapshotWith (m := IO) (do (← opened.phase.get).installed)
      (issuer.ptrEq opened.token) opened.phase.set issued.handle ∧
    releaseSnapshotWith opened.loadInstalled (opened.ptrEq issuer opened.token)
      (opened.set opened.phase) issued.handle before = .error mode.error before := by
  refine ⟨opened.uses.releasePin owns, ?_⟩
  simp only [releaseSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

/-- An inactive handle cannot issue a snapshot. The first phase read
ends both public acquisition schedules at the entered heap. -/
theorem rejectsInactiveSnapshotAcquire
    (stored : opened.contents before opened.phase = some mode.phase) (sequence : UInt64) :
    ∃ issue : SnapshotPin → DiskSnapshotPin,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO) (do (← opened.phase.get).installed)
        opened.phase.set issue sequence ∧
      opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
        (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) ∧
      acquireSnapshotWith opened.loadInstalled (opened.set opened.phase) issue sequence before =
        .error mode.error before ∧
      acquireLatestWith opened.loadInstalled
        (acquireSnapshotWith opened.loadInstalled (opened.set opened.phase) issue) before = .error mode.error before := by
  obtain ⟨issue, _, first, latest⟩ := opened.uses.snapshotAcquisitions
  exact ⟨issue, first sequence, latest, by
    simp only [acquireSnapshotWith, Bind.bind, EStateM.bind, opened.rejectsInstalled stored], by
    simp only [acquireLatestWith, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]⟩

theorem rejectsInactiveFloorUpdate
    (stored : opened.contents before opened.phase = some mode.phase) (floor : UInt64) :
    opened.table.advanceFloor floor = advanceFloorWith (m := IO) (do (← opened.phase.get).installed)
      opened.phase.set floor ∧
    advanceFloorWith opened.loadInstalled (opened.set opened.phase) floor before = .error mode.error before := by
  refine ⟨opened.uses.advanceFloor floor, ?_⟩
  simp only [advanceFloorWith, Bind.bind, EStateM.bind, opened.rejectsInstalled stored]

end NativeOpenedHandle

/-- The actual close at the start of a retry sequence already makes
the old reader inactive at the first retry heap. The original receiver
returns the closed error even if a pin with a different issuer is supplied. -/
theorem NativeOpenedFinalizedRetryReport.Returned.rejectsClosedRead
    {heap : Type} {old nextHandle : NativeOpenedHandle heap} {current : NativeOpenedPosition old}
    {inputs : List System.FilePath} {input : System.FilePath}
    {view : OpenCloseHeapView heap WalSegmentRepair.FileImage} {report : NativeOpenedFinalizedRetryReport current inputs input view}
    {next : NativeOpenedPosition nextHandle} {errors : List (System.FilePath × IO.Error)}
    (returned : report.Returned next errors)
    {pin : DiskSnapshotPin} {issuer : IO.Ref Unit} {issued : SnapshotPin}
    (owns : pin.UsesOpenToken issuer issued) (request : SnapshotReadRequest α) :
    ∃ after,
      current.closeOnOpenedCells report.closeCalls report.active report.pending report.directory = .ok () after ∧
      readSnapshotWith old.loadInstalled (old.ptrEq issuer old.token) (request.read issued.handle) after =
        .error (NativeInactivePhase.closed.error) after := by
  obtain ⟨after, _, _, _, _, _, _, _, close, phase, _⟩ := returned.witnessed
  exact ⟨after, close, (old.rejectsInactiveSnapshotRead (mode := .closed) phase owns request).2⟩

end Alvoki.Storage.DiskSession
