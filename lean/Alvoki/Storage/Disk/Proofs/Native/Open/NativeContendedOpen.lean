import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeReadyCheckpoint

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Another opener reaches the same canonical LOCK while the writer still
holds it. Its temporary description is distinct from that writer's
description. The reported failed acquisition leaves the old owner held. -/
structure NativeContendedOpen (state : NativeReadyState) (input : FilePath) where
  realPath : FilePath → EStateM IO.Error CensusOpenState FilePath
  stat : FilePath → EStateM IO.Error CensusOpenState (Except IO.Error (IO.FS.Metadata × DeviceInode))
  append : FilePath → EStateM IO.Error CensusOpenState DescriptorSlot
  tryLock : DescriptorSlot → EStateM IO.Error CensusOpenState Bool
  unlock : DescriptorSlot → EStateM IO.Error CensusOpenState Unit
  slot : DescriptorSlot
  free : ∀ old ∈ state.census.slots, old.address ≠ slot.address
  fresh : state.census.references slot.description = []
  view : DirectoryReadNamespace
  root : DeviceInode
  directoryObject : view.modelObject root = state.census.inode state.directorySlot.description
  statLookup : RunChildLookup root "LOCK" view
  appendLookup : RunChildLookup root "LOCK" view
  lockObject : view.modelObject statLookup.child = state.census.inode state.owner.description
  appendedObject : state.census.inode slot.description = view.modelObject appendLookup.child
  resolved : realPath input (state.census, state.files) = .ok state.session.directory.path (state.census, state.files)
  flatName : String
  flatMessage : String
  flatAbsent : stat (state.session.directory.file .wal) (state.census, state.files) =
    .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) (state.census, state.files)
  metadata : IO.FS.Metadata
  probed : stat (state.session.directory.file .lock) (state.census, state.files) =
    .ok (.ok (metadata, statLookup.child)) (state.census, state.files)
  privateLock : (metadata.type == .file && metadata.numLinks == 1) = true
  opened : append (state.session.directory.file .lock) (state.census, state.files) =
    .ok slot (state.census.insert slot free, state.files)
  contended : tryLock slot (state.census.insert slot free, state.files) =
    .ok false (state.census.insert slot free, state.files)

namespace NativeContendedOpen

variable {state : NativeReadyState} {input : FilePath}

def diagnostic (_report : NativeContendedOpen state input) : IO.Error :=
  IO.userError s!"database already open: {state.session.directory.path}"

/-- The scheduled no-follow lookup returns the metadata component of
the same reported stat that identifies the physical child. -/
def lookup (report : NativeContendedOpen state input) (path : FilePath) :
    EStateM IO.Error CensusOpenState (Except IO.Error IO.FS.Metadata) := do
  let result ← report.stat path
  pure (result.map Prod.fst)

def run (report : NativeContendedOpen state input)
    (recover : DiskDirectory → DescriptorSlot → EStateM IO.Error CensusOpenState α) :
    EStateM.Result IO.Error CensusOpenState α :=
  DiskTable.withOpenAdmission input report.realPath report.lookup report.append
    (fun directory slot => openWithLock (report.tryLock slot)
      (fun _ => IO.userError s!"database already open: {directory.path}")
      (fun _ => report.unlock slot) (fun _ => recover directory slot)) (state.census, state.files)

/-- Contention stops at the returned flock result. The recovery or
unlock callback can be arbitrary since neither is reached. -/
theorem returns (report : NativeContendedOpen state input)
    (recover : DiskDirectory → DescriptorSlot → EStateM IO.Error CensusOpenState α) :
    report.run recover = .error report.diagnostic (state.census.insert report.slot report.free, state.files) := by
  have flat : optionalMetadataWith (report.lookup (state.session.directory.file .wal)) (state.census, state.files) =
      .ok none (state.census, state.files) := by
    simp [lookup, optionalMetadataWith, Bind.bind, EStateM.bind, report.flatAbsent, Pure.pure, EStateM.pure, Except.map]
  have probed : optionalMetadataWith (report.lookup (state.session.directory.file .lock)) (state.census, state.files) =
      .ok (some report.metadata) (state.census, state.files) := by
    simp [lookup, optionalMetadataWith, Bind.bind, EStateM.bind, report.probed, Pure.pure, EStateM.pure, Except.map]
  unfold run
  rw [DiskTable.withOpenAdmission_lockOpen _ _ _ _ report.resolved flat probed
    (fun _ same => Option.some.inj same ▸ report.privateLock), report.opened]
  simp [openWithLock, Bind.bind, EStateM.bind, report.contended, diagnostic,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem keepsAuthority (report : NativeContendedOpen state input) (valid : state.Valid) :
    report.slot.description ≠ state.session.descriptor ∧
    report.statLookup.child = report.appendLookup.child ∧
    state.census.inode report.slot.description = state.census.inode state.owner.description ∧
    report.view.modelObject report.root = state.census.inode state.directorySlot.description ∧
    state.owner ∈ (state.census.insert report.slot report.free).slots ∧
    state.directorySlot ∈ (state.census.insert report.slot report.free).slots ∧
    state.files.owners.Owns state.session.directory state.session.descriptor := by
  have binding : report.view.child report.root "LOCK" = some report.statLookup.child := by
    simpa only [report.statLookup.atRoot, report.statLookup.atName] using report.statLookup.binds
  have sameChild := report.appendLookup.child_eq binding
  have sameLock := report.appendedObject.trans ((congrArg report.view.modelObject sameChild).trans report.lockObject)
  refine ⟨?_, sameChild.symm, sameLock, report.directoryObject, List.mem_cons_of_mem _ valid.ownerLive,
    List.mem_cons_of_mem _ valid.directoryLive, valid.retained.held⟩
  intro shared
  have live := state.census.mem_references.mpr ⟨state.owner, valid.ownerLive, rfl, valid.owner.trans shared.symm⟩
  rw [report.fresh] at live
  contradiction

end NativeContendedOpen

/-- The contender's observed descriptor drop restores the original
census. The current writer and read ledger then seed the next operation. -/
theorem NativeReadPosition.refusesContendedOpen (current : NativeReadPosition history log)
    (report : NativeContendedOpen current.state input)
    (drop : LockReferenceDrop) (retired : drop = report.slot.closeEvent)
    (recover : DiskDirectory → DescriptorSlot → EStateM IO.Error CensusOpenState α) :
    report.run recover =
      .error report.diagnostic (current.state.census.insert report.slot report.free, current.state.files) ∧
    (current.state.census.insert report.slot report.free).afterDrops [drop] = current.state.census ∧
    report.slot.description ≠ current.state.session.descriptor ∧
    current.state.census.inode report.slot.description = current.state.census.inode current.state.owner.description ∧
    InstalledClientReplay log current.reads history current.state.writer.installed current.state.session := by
  obtain ⟨distinct, _, inode, _, _, _, _⟩ := report.keepsAuthority current.readPrefix.refines.1
  exact ⟨report.returns recover, retired.symm ▸ checkpointTemporaryClose _ _ _, distinct, inode,
    current.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
