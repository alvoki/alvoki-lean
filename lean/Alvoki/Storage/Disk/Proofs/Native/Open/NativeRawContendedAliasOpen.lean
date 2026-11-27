import Alvoki.Storage.Disk.Proofs.Native.Open.NativeContendedAliasAdmission
import Alvoki.Storage.Disk.Proofs.Append.NativeStoppedAppendFinalizedRetry

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type}

section

variable {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stop : NativeFirstAppendStop prepared}
  {exit : NativeFirstAppendExit stop} {view : OpenCloseHeapView heap FileImage}
  {calls : RawOpenAdmissionCallbacks heap} {release : IO.FS.Handle → heap → heap} {input : FilePath}

/-- The contender preserves the old ownership and returns its own
diagnostic before the old alias's later observed release. -/
structure RawStoppedFirstAppendExitEffects.ContendedReturn
    (seen : RawStoppedFirstAppendExitEffects current stop exit view)
    (attempt : RawContendedAliasOpen view calls release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor stop.view stop.root input seen.afterExit) : Prop where
  returned : attempt.Returned
  aliasProcess : attempt.alias.reference.process ≠ stop.handle.2.1.reference.process
  sameLock : (view.descriptors attempt.blocked).inode attempt.slot.description =
    (view.descriptors seen.afterExit).inode current.current.ready.state.session.descriptor
  laterCensus : view.descriptors seen.released =
    (view.descriptors attempt.finalized.reached).afterDrops exit.later
  laterFiles : view.files seen.released = (view.descriptors attempt.finalized.reached).dropLockState
    current.current.ready.state.session.descriptor exit.later current.current.ready.state.session.directory
    (view.files attempt.finalized.reached)

/-- The contender runs from the issuer's reached exit heap. Its own
descriptor closes. The later drops can therefore use the caller-visible
result's census and files, with no requirement on the old cached
directory handle. -/
theorem RawStoppedFirstAppendExitEffects.finalizesContendedOpen
    (seen : RawStoppedFirstAppendExitEffects current stop exit view)
    (attempt : RawContendedAliasOpen view calls release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor stop.view stop.root input seen.afterExit) :
    seen.ContendedReturn attempt := by
  let state := current.current.ready.state
  have valid := current.current.ready.readPrefix.refines.1
  have pending := current.current.ready.stopsAtFirstAppend stop
  have live : (view.descriptors seen.cut).references state.session.descriptor ≠ [] := by
    rw [seen.cutCensus]
    exact List.ne_nil_of_mem (stop.cutFiles.1.mem_references.mpr
      ⟨exit.issuerLock, exit.issuerLockLive, rfl, exit.issuerLockDescription⟩)
  have held : (view.files seen.cut).owners.Owns state.session.directory state.session.descriptor := by
    rw [seen.cutFiles]
    exact valid.retained.held
  have first : LockCensusTrace state.session.directory state.session.descriptor
      (view.descriptors seen.cut) (view.files seen.cut) (view.descriptors seen.afterExit) (view.files seen.afterExit) := by
    rw [seen.exitCensus, seen.exitFiles]
    exact .drops (.start held live) [exit.exit]
  have surviving : (view.descriptors seen.afterExit).references state.session.descriptor ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors seen.afterExit).mem_references.mpr
      ⟨attempt.alias, attempt.aliasLive, rfl, attempt.aliasDescription⟩)
  have same := first.reached.2.2
  rw [ite_eq_right surviving] at same
  have returned := attempt.returns (same.symm ▸ held)
  refine ⟨returned, ?_, ?_, returned.census.symm ▸ seen.dropCensus, ?_⟩
  · intro sameProcess
    have remains := attempt.aliasLive
    rw [seen.exitCensus] at remains
    have observed := (List.mem_filter.mp remains).2
    simp [exit.reported, LockReferenceDrop.removes, sameProcess] at observed
  · have bound := stop.lock.binds
    rw [stop.lock.atRoot, stop.lock.atName] at bound
    rw [returned.checkedInode, attempt.checkedChild.child_eq bound, stop.lockIdentity, valid.owner,
      seen.exitCensus, seen.cutCensus]
    exact congrFun pending.inodes.symm _
  · rw [returned.census, returned.files]
    exact seen.dropFiles

end

/-- The same released projection starts the finalized read-only
retries and the selected healthy return. The contended open's own
diagnostic remains available alongside that later execution. -/
theorem NativeStoppedAppendFinalizedRetry.reachesAfterContention
    {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
    {request : WriteRequest} {inputs : List FilePath} {input contended : FilePath}
    {view : OpenCloseHeapView heap FileImage}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes)
    (attempt : RawContendedAliasOpen view seen.calls seen.release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor seen.stop.view seen.stop.root contended seen.rawExit.afterExit) :
    seen.rawExit.ContendedReturn attempt ∧
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start :=
  ⟨seen.rawExit.finalizesContendedOpen attempt, seen.reaches⟩


/-- The finite execution retains the actual path and caller-visible
contention diagnostic before the later finalized open failures. -/
theorem NativeStoppedAppendFinalizedRetry.recordsContendedRetry
    {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
    {request : WriteRequest} {inputs : List FilePath} {input contended : FilePath}
    {view : OpenCloseHeapView heap FileImage}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes)
    (attempt : RawContendedAliasOpen view seen.calls seen.release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor seen.stop.view seen.stop.root contended seen.rawExit.afterExit) :
    seen.rawExit.ContendedReturn attempt ∧
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      seen.Returned start (some (contended, attempt.diagnostic)) := by
  have returned := seen.rawExit.finalizesContendedOpen attempt
  refine ⟨returned, seen.reachesWithAccess (.contended contended attempt ?_ ?_ returned.returned returned.sameLock
    returned.laterCensus returned.laterFiles)⟩
  · rw [seen.rawExit.exitCensus, seen.rawExit.cutCensus]
  · rw [seen.rawExit.exitFiles, seen.rawExit.cutCensus, seen.rawExit.cutFiles]


/-- Reify the ordinary contention branch from the fixed source's
returned append handle and false flock. The contender's other reports
supply only physical effects, custody and finalization. -/
theorem NativeStoppedAppendFinalizedRetry.recordsContentionFromCallbacks
    {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
    {request : WriteRequest} {inputs : List FilePath} {input contended : FilePath}
    {view : OpenCloseHeapView heap FileImage}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes)
    (effects : RawContendedAliasEffects view seen.calls seen.release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor seen.stop.view seen.stop.root contended seen.rawExit.afterExit)
    (appended : seen.calls.beforeFlock contended seen.rawExit.afterExit =
      .ok (current.current.ready.state.session.directory, effects.lock) effects.afterAppend)
    (busy : seen.calls.flock effects.lock effects.afterAppend = .ok false effects.blocked) :
    let attempt : RawContendedAliasOpen view seen.calls seen.release current.current.ready.state.session.directory
      current.current.ready.state.session.descriptor seen.stop.view seen.stop.root contended seen.rawExit.afterExit :=
      ⟨effects, appended, busy⟩
    seen.rawExit.ContendedReturn attempt ∧
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      seen.Returned start (some (contended, attempt.diagnostic)) :=
  seen.recordsContendedRetry ⟨effects, appended, busy⟩

end Alvoki.Storage.DiskSession
