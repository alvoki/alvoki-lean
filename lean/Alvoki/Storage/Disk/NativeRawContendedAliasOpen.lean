import Alvoki.Storage.Disk.NativeRawFlockOutcome
import Alvoki.Storage.Disk.NativeStoppedAppendFinalizedRetry

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type}

/-- The contender resolves the canonical lock while a different
description still has a live alias. Nonblocking contention returns
before recovery or cache initialization. -/
structure RawContendedAliasOpen (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (directory : DiskDirectory) (description : Nat)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode) (input : FilePath) (entry : heap) where
  alias : DescriptorSlot
  aliasLive : alias ∈ (view.descriptors entry).slots
  aliasDescription : alias.description = description
  stat : FilePath → EStateM IO.Error heap (Except IO.Error (IO.FS.Metadata × DeviceInode))
  sameLookup : ∀ path, calls.lookup path = (do
    let result ← stat path
    pure (result.map Prod.fst))
  resolved : calls.realPath input entry = .ok directory.path entry
  flatAbsent : optionalMetadataWith (calls.lookup (directory.file .wal)) entry = .ok none entry
  checkedChild : RunChildLookup root "LOCK" namespaceView
  metadata : IO.FS.Metadata
  checked : stat (directory.file .lock) entry = .ok (.ok (metadata, checkedChild.child)) entry
  privateLock : (metadata.type == .file && metadata.numLinks == 1) = true
  lock : IO.FS.Handle
  slot : DescriptorSlot
  free : ∀ prior ∈ (view.descriptors entry).slots, prior.address ≠ slot.address
  fresh : (view.descriptors entry).references slot.description = []
  appendedChild : RunChildLookup root "LOCK" namespaceView
  inode : (view.descriptors entry).inode slot.description = namespaceView.modelObject appendedChild.child
  afterAppend : heap
  appended : calls.openAppend (directory.file .lock) entry = .ok lock afterAppend
  openedHandle : view.handle afterAppend lock = ((view.descriptors entry).insert slot free, slot, 0)
  openedCensus : view.descriptors afterAppend = (view.handle afterAppend lock).1
  openedFiles : view.files afterAppend = view.files entry
  blocked : heap
  busy : calls.flock lock afterAppend = .ok false blocked
  busyCensus : view.descriptors blocked = view.descriptors afterAppend
  busyFiles : view.files blocked = view.files afterAppend
  finalized : RawOpenErrorLockFinalization view directory release lock slot blocked

namespace RawContendedAliasOpen

variable {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {directory : DiskDirectory} {description : Nat}
  {namespaceView : DirectoryReadNamespace} {root : DeviceInode} {input : FilePath} {entry : heap}
  (seen : RawContendedAliasOpen view calls release directory description namespaceView root input entry)

def diagnostic (_seen : RawContendedAliasOpen view calls release directory description namespaceView root input entry) :
    IO.Error := IO.userError s!"database already open: {directory.path}"

structure Returned : Prop where
  ran : ∀ (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable),
    finishFailedOpen (calls.runOpen input init makeCache recover) release seen.lock entry =
      .error seen.diagnostic seen.finalized.reached
  checkedInode : (view.descriptors seen.blocked).inode seen.slot.description =
    namespaceView.modelObject seen.checkedChild.child
  differentDescription : seen.slot.description ≠ description
  retired : (view.descriptors seen.finalized.reached).references seen.slot.description = []
  census : view.descriptors seen.finalized.reached = view.descriptors entry
  files : view.files seen.finalized.reached = view.files entry
  held : (view.files seen.finalized.reached).owners.Owns directory description
  live : seen.alias ∈ (view.descriptors seen.finalized.reached).slots

/-- The source reaches the exact failed contender. Its finalizer
retires only its slot and keeps the old lock alias and files. -/
theorem returns (held : (view.files entry).owners.Owns directory description) : seen.Returned := by
  have guard : optionalMetadataWith (calls.lookup (directory.file .lock)) entry = .ok (some seen.metadata) entry := by
    simp [seen.sameLookup, optionalMetadataWith, Bind.bind, EStateM.bind, seen.checked, Pure.pure, EStateM.pure, Except.map]
  have opened : calls.beforeFlock input entry = .ok (directory, seen.lock) seen.afterAppend := by
    unfold RawOpenAdmissionCallbacks.beforeFlock
    rw [DiskTable.withOpenAdmission_lockOpen _ _ _ _ seen.resolved seen.flatAbsent guard
      (fun _ same => Option.some.inj same ▸ seen.privateLock), seen.appended]
    rfl
  have busyCensus : view.descriptors seen.blocked = (view.descriptors entry).insert seen.slot seen.free :=
    seen.busyCensus.trans (seen.openedCensus.trans (congrArg Prod.fst seen.openedHandle))
  have busyFiles := seen.busyFiles.trans seen.openedFiles
  have distinct : seen.slot.description ≠ description := by
    intro same
    have present := (view.descriptors entry).mem_references.mpr
      ⟨seen.alias, seen.aliasLive, rfl, seen.aliasDescription.trans same.symm⟩
    rw [seen.fresh] at present
    contradiction
  have bound := seen.checkedChild.binds
  rw [seen.checkedChild.atRoot, seen.checkedChild.atName] at bound
  have sameChild := seen.appendedChild.child_eq bound
  have exactSlot : view.descriptors seen.finalized.reached = view.descriptors entry := by
    have closed := DescriptorInventory.insert_thenClose (view.descriptors entry) seen.slot seen.free []
    simp only [List.nil_append] at closed
    rw [seen.finalized.census, busyCensus, closed]
    have kept : ∀ prior ∈ (view.descriptors entry).slots, (!seen.slot.closeEvent.removes prior.reference) = true := by
      intro prior present
      have free := seen.free prior present
      cases dropped : seen.slot.closeEvent.removes prior.reference with
      | false => rfl
      | true =>
        simp only [DescriptorSlot.closeEvent, LockReferenceDrop.removes, Bool.and_eq_true, beq_iff_eq] at dropped
        exact False.elim (free (Prod.ext dropped.1 dropped.2))
    generalize view.descriptors entry = inventory at kept ⊢
    cases inventory with
    | mk slots distinct inode =>
      simp only [DescriptorInventory.afterDrops, List.all_cons, List.all_nil, Bool.and_true,
        List.filter_eq_self.mpr kept]
  have spot : (view.descriptors seen.blocked).references seen.slot.description ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors seen.blocked).mem_references.mpr
      ⟨seen.slot, seen.finalized.live, rfl, rfl⟩)
  have untouched : view.files seen.finalized.reached = view.files entry := by
    have unowned : (view.files seen.blocked).owners (directory.file .lock) ≠ some seen.slot.description := by
      rw [busyFiles, show (view.files entry).owners (directory.file .lock) = some description from held]
      exact fun same => distinct (Option.some.inj same).symm
    rw [seen.finalized.files, DescriptorInventory.dropLockState, dite_eq_left spot,
      HeldLockReferences.afterFileDrops_unowned _ unowned]
    exact busyFiles
  refine ⟨?_, ?_, distinct, exactSlot.symm ▸ seen.fresh, exactSlot, untouched,
    untouched.symm ▸ held, exactSlot.symm ▸ seen.aliasLive⟩
  · intro init makeCache recover
    simp only [finishFailedOpen, calls.runsAfterFlock input opened init makeCache recover, seen.busy, seen.finalized.finalized,
      diagnostic]
  · rw [busyCensus]
    exact seen.inode.trans (congrArg namespaceView.modelObject sameChild)

end RawContendedAliasOpen

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

end Alvoki.Storage.DiskSession
