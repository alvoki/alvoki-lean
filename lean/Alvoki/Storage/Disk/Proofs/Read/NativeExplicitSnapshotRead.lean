import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle)

/-- The supplied handle and the native pointer comparison for the
reached session. Logical identities justify the comparison's result. -/
structure NativeSnapshotHandleObservation (session : SegmentedSession) where
  handle : SnapshotHandle
  issuer : Nat
  sameSession : Bool
  compared : sameSession = decide (issuer = session.sessionRef)

def NativeSnapshotHandleObservation.reader {state : NativeReadyState}
    (seen : NativeSnapshotHandleObservation state.session) (valid : state.Valid) :
    ObservedSnapshotReader state.session.directory state.session.descriptor state.writer :=
  ⟨state.session, rfl, rfl, valid.phase, seen.issuer, seen.sameSession, seen.compared⟩

/-- The original request, its native return, and the recorded response
advance the read ledger at the same returned session and file state. -/
structure NativeSnapshotHandleRead (current : NativeReadPosition history log)
    (seen : NativeSnapshotHandleObservation current.state.session) (request : SnapshotReadRequest α)
    (response : Option α) (recorded : RecordedSnapshotRead) (next : NativeReadPosition history log) : Prop where
  result : request.HandleReturn (seen.reader current.readPrefix.refines.1) seen.handle response recorded
  state : next.state = current.state
  initial : next.initial = current.initial
  opened : next.opened = current.opened
  reads : next.reads = current.reads ++ [recorded]

/-- Run the native lookup or range guard at the currently reached
session. The output covers both a registered pin's response and a
foreign or inactive handle's denial. -/
theorem NativeReadPosition.readsHandle (current : NativeReadPosition history log)
    (seen : NativeSnapshotHandleObservation current.state.session) (request : SnapshotReadRequest α) :
    ∃ response recorded next, NativeSnapshotHandleRead current seen request response recorded next := by
  obtain ⟨response, recorded, result⟩ := request.returnsForHandle
    (seen.reader current.readPrefix.refines.1) seen.handle
  let next : NativeReadPosition history log :=
    { current with reads := current.reads ++ [recorded], readPrefix := .readHandle current.readPrefix rfl result }
  exact ⟨response, recorded, next, result, rfl, rfl, rfl, rfl⟩

end Alvoki.Storage.DiskSession
