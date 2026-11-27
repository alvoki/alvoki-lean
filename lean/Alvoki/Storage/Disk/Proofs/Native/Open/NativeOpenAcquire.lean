import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenReferences
import Alvoki.Storage.Disk.Proofs.Read.NativeSnapshotExecution

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

variable {heap : Type}

/-- The primitive phase-cell effects, interpreted within one reported
process heap. A read returns the reached contents and a write updates
the very cell named by the callback. -/
structure OpenPhaseCellEffects
    (contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) : Prop where
  reads : ∀ heap reference phase, contents heap reference = some phase → get reference heap = .ok phase heap
  writes : ∀ heap reference phase updated, contents heap reference = some phase →
    ∃ after, set reference updated heap = .ok () after ∧ contents after reference = some updated

/-- The public snapshot acquisition reads the phase cell allocated by
open. On success it writes the new pins into that same cell and issues a
snapshot handle carrying the same raw session reference. An unsupported
sequence returns none with no setter effect. The same outcomes continue
the existing ready execution proof. -/
theorem NativeReadPosition.acquiresViaOpenReferences {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {before : heap}
    (stored : contents before phase = some current.state.session.phase) (snapshot : UInt64) :
    ∃ (issue : SnapshotPin → DiskSnapshotPin) (next : NativeReadPosition history log)
      (normalized : Option (Nat × SnapshotPin)) (after : heap),
      (∀ pin, (issue pin).UsesOpenToken token pin) ∧
      db.acquireAt snapshot = acquireSnapshotWith (m := IO) (do (← phase.get).installed) phase.set issue snapshot ∧
      NativeSnapshotUpdateContinuation current (.acquireAt snapshot) next ∧
      current.state.session.runAcquireAt snapshot = .ok normalized next.state.session ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (set phase) issue snapshot before =
        .ok (normalized.map (fun (_, pin) => issue pin)) after ∧
      contents after phase = some next.state.session.phase ∧
      (normalized = none → after = before) := by
  obtain ⟨issue, usingToken, source⟩ := uses.acquireAt snapshot
  let request : NativeSnapshotUpdateObservation current.state (Option (Nat × SnapshotPin)) := .acquireAt snapshot
  obtain ⟨next, transition⟩ := current.updatesSnapshot request
  have ready := current.readPrefix.refines.1.phase
  have loaded := effects.reads before phase current.state.session.phase stored
  have returned := transition.returned
  have reached := transition.reached
  cases acquired : current.state.writer.installed.table.acquireAt snapshot with
  | none =>
    simp only [request, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, acquired] at returned reached
    refine ⟨issue, next, none, before, usingToken, source, transition, returned, ?_, ?_, fun _ => rfl⟩
    · simp only [acquireSnapshotWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure,
        EStateM.pure, acquired, Option.map_none]
    · rw [reached]
      exact stored
  | some result =>
    obtain ⟨pin, table⟩ := result
    simp only [request, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, acquired] at returned reached
    let updated := Phase.ready { current.state.writer.installed with table }
    obtain ⟨after, wrote, kept⟩ := effects.writes before phase current.state.session.phase updated stored
    refine ⟨issue, next, some (current.state.session.sessionRef, pin), after, usingToken, source, transition,
      returned, ?_, ?_, by simp⟩
    · simp only [acquireSnapshotWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure,
        EStateM.pure, acquired, Option.map_some, wrote, updated]
    · rw [reached]
      exact kept

/-- Run acquisition on the object and heap returned by the same
reported installer. The first public call uses that initialized cell,
and any subsequent call can start from the reported reached contents. -/
theorem OpenReferenceAllocations.acquiresAfterInstall
    (current : NativeReadPosition history log)
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {beforeInstall : heap}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken contents
      current.state.writer.installed beforeInstall)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly current.state.session.directory lock files assemble)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) (snapshot : UInt64) :
    ∃ (db : DiskTable) (issue : SnapshotPin → DiskSnapshotPin) (next : NativeReadPosition history log)
      (normalized : Option (Nat × SnapshotPin)) (after : heap),
      installReady current.state.writer.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token))
        beforeInstall = .ok db allocation.afterToken ∧
      db.UsesOpenReferences current.state.session.directory lock files allocation.phase allocation.token ∧
      (∀ pin, (issue pin).UsesOpenToken allocation.token pin) ∧
      db.acquireAt snapshot =
        acquireSnapshotWith (m := IO) (do (← allocation.phase.get).installed) allocation.phase.set issue snapshot ∧
      NativeSnapshotUpdateContinuation current (.acquireAt snapshot) next ∧
      current.state.session.runAcquireAt snapshot = .ok normalized next.state.session ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← get allocation.phase).installed) (set allocation.phase)
        issue snapshot allocation.afterToken = .ok (normalized.map (fun (_, pin) => issue pin)) after ∧
      contents after allocation.phase = some next.state.session.phase ∧
      (normalized = none → after = allocation.afterToken) := by
  let db := assemble allocation.phase allocation.token
  obtain ⟨installed, uses, initial⟩ := allocation.installs constructor
  have stored : contents allocation.afterToken allocation.phase = some current.state.session.phase :=
    current.readPrefix.refines.1.phase.symm ▸ initial
  obtain ⟨issue, next, normalized, after, usingToken, source, transition, returned, executed, reached, unchanged⟩ :=
    current.acquiresViaOpenReferences db uses effects stored snapshot
  exact ⟨db, issue, next, normalized, after, installed, uses, usingToken, source, transition, returned,
    executed, reached, unchanged⟩

end Alvoki.Storage.DiskSession
