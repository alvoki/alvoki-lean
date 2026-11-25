import Alvoki.Storage.Disk.NativeExplicitSnapshotRead

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

variable {heap : Type}

/-- The actual public lookup or range reads the same phase cell as
snapshot acquisition and compares the exact raw pin token. The
comparison is reported within that process heap. The unchanged heap
and the replay-backed response are the result of the same call. -/
theorem NativeReadPosition.readsOpenPin {history log α}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {pin : DiskSnapshotPin} {issued : SnapshotPin} (owns : pin.UsesOpenToken token issued)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {before : heap} (readsCell : ∀ value, contents before phase = some value → get phase before = .ok value before)
    (stored : contents before phase = some current.state.session.phase)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compared : ptrEq token token before = .ok true before) (request : SnapshotReadRequest α) :
    let observed : NativeSnapshotHandleObservation current.state.session :=
      ⟨issued.handle, current.state.session.sessionRef, true, by simp⟩
    (match request with
      | .lookup key => db.lookup pin.handle key = readSnapshotWith (m := IO) (do (← phase.get).installed)
          (token.ptrEq token) (fun table => table.lookup issued.handle key)
      | .range lo hi => db.range pin.handle lo hi = readSnapshotWith (m := IO) (do (← phase.get).installed)
          (token.ptrEq token) (fun table => table.range issued.handle lo hi)) ∧
    ∃ response recorded next,
      NativeSnapshotHandleRead current observed request response recorded next ∧
      readSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq token token)
        (request.read issued.handle) before = .ok response before ∧
      InstalledClientReplay log next.reads history next.state.writer.installed next.state.session := by
  intro observed
  constructor
  · cases request with
    | lookup key => exact uses.lookupPin owns key
    | range lo hi => exact uses.rangePin owns lo hi
  obtain ⟨response, recorded, next, read⟩ := current.readsHandle observed request
  have ready := current.readPrefix.refines.1.phase
  have loaded := readsCell current.state.session.phase stored
  have expected := (observed.reader current.readPrefix.refines.1).readResult (request.read issued.handle)
  have value : request.read issued.handle current.state.writer.installed.table = response := by
    have result := EStateM.Result.ok.inj (expected.symm.trans read.result.returned)
    simpa only [observed, NativeSnapshotHandleObservation.reader, ↓reduceIte] using result.1
  refine ⟨response, recorded, next, read, ?_, next.readPrefix.guardedReplay⟩
  simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded, compared, ready,
    Phase.installed, Pure.pure, EStateM.pure, ↓reduceIte, value]

end Alvoki.Storage.DiskSession
