import Alvoki.Storage.Disk.NativeRawFlockOutcome
import Alvoki.Storage.Disk.NativeOpenErrorLockFinalization
import Alvoki.Storage.Disk.NativeFirstAppendExitReopen

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


/-- Admission to the read-only retry sequence can begin just after
release, or after a real contended open on the still-held description.
The latter starts in the issuer's exact exit projection and uses the
contender's finalized return as the start of the later release. -/
inductive NativeFirstAppendRetryAccess {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}
    {stop : NativeFirstAppendStop prepared} (exited : NativeFirstAppendExit stop)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (released : heap) : Option (FilePath × IO.Error) → Prop where
  | direct : NativeFirstAppendRetryAccess exited view calls release released none
  | contended {entry : heap} (input : FilePath)
      (attempt : RawContendedAliasOpen view calls release state.session.directory state.session.descriptor
        stop.view stop.root input entry)
      (exitCensus : view.descriptors entry = stop.cutFiles.1.afterDrops [exited.exit])
      (exitFiles : view.files entry = stop.cutFiles.1.dropLockState state.session.descriptor
        [exited.exit] state.session.directory ⟨stop.files, state.files.owners⟩)
      (returned : attempt.Returned)
      (sameLock : (view.descriptors attempt.blocked).inode attempt.slot.description =
        (view.descriptors entry).inode state.session.descriptor)
      (laterCensus : view.descriptors released = (view.descriptors attempt.finalized.reached).afterDrops exited.later)
      (laterFiles : view.files released = (view.descriptors attempt.finalized.reached).dropLockState
        state.session.descriptor exited.later state.session.directory (view.files attempt.finalized.reached)) :
      NativeFirstAppendRetryAccess exited view calls release released (some (input, attempt.diagnostic))

end Alvoki.Storage.DiskSession
