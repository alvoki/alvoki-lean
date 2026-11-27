import Alvoki.Storage.Disk.Proofs.Rotation.RotationCreateInterruption
import Alvoki.Storage.Disk.Proofs.Recovery.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System WalSegmentRotation WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev successor (before : SegmentedWriterState) := before.installed.walBytes / WAL.frameSize
private abbrev successorName (before : SegmentedWriterState) := renderWalSegmentName (successor before)
private abbrev keeperName (before : SegmentedWriterState) := renderWalSegmentName before.installed.activeFirst
private abbrev successorPath (directory : DiskDirectory) (before : SegmentedWriterState) :=
  directory.file (.walSegment (successor before))

/-- The observed live namespace and the possible surviving names and bytes. -/
structure RotationCreateFiles where
  view : DirectoryReadNamespace
  inodes : WalInodeImage
  crashNames : String → List (Option DeviceInode)

/-- The absent successor was checked in the same held parent as the old
WAL keeper and marker. The probe report belongs to the issued no-follow
lookup on the canonical successor path. -/
structure RotationCreateParent (directory : DiskDirectory) (before : SegmentedWriterState)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) (inventory : DescriptorInventory) where
  nonempty : before.installed.activeFirst < successor before
  absent : ∃ path message, lookup (successorPath directory before) = .error (.noFileOrDirectory path 2 message)
  root : DeviceInode
  files : RotationCreateFiles
  owner : DescriptorSlot
  ownerHeld : before.owners.Owns directory owner.description
  ownerLive : owner ∈ inventory.slots
  lock : RunChildLookup root "LOCK" files.view
  lockObject : files.view.modelObject lock.child = inventory.inode owner.description
  probe : FilePath → DeviceInode × String × Except IO.Error IO.FS.Metadata
  issuedProbe : probe (successorPath directory before) =
    (root, successorName before, lookup (successorPath directory before))
  missing : files.view.child root (successorName before) = none
  absentAfterCrash : files.crashNames (successorName before) = [none]
  keeper : RunChildLookup root (keeperName before) files.view
  marker : RunChildLookup root "WAL.commit" files.view
  keeperBytes : files.inodes.visible (files.view.modelObject keeper.child) = before.wal.active.bytes
  keeperCrash : files.inodes.crashBytes (files.view.modelObject keeper.child) = [before.wal.active.bytes]
  keeperNameCrash : files.crashNames (keeperName before) = [some keeper.child]
  markerBytes : before.wal.directory.active.walBoundary = some (files.inodes.visible (files.view.modelObject marker.child))
  markerCrash : files.inodes.crashBytes (files.view.modelObject marker.child) =
    [files.inodes.visible (files.view.modelObject marker.child)]
  markerNameCrash : files.crashNames "WAL.commit" = [some marker.child]

theorem RotationCreateParent.probeAbsent {directory : DiskDirectory} {before : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    (parent : RotationCreateParent directory before lookup inventory) :
    ∃ path message, parent.probe (successorPath directory before) =
      (parent.root, successorName before, .error (.noFileOrDirectory path 2 message)) ∧
      parent.files.view.child parent.root (successorName before) = none := by
  obtain ⟨path, message, absent⟩ := parent.absent
  exact ⟨path, message, parent.issuedProbe.trans (by rw [absent]), parent.missing⟩

private abbrev CreateState := DescriptorInventory × RotationCreateFiles

/-- The raw exclusive open has allocated a slot and installed a new empty
inode in the checked parent. At this cut the runtime can still be wrapping
the descriptor. Object life and crash survivors are primitive reports. -/
structure RotationRawSuccessor {directory : DiskDirectory} {before : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    (parent : RotationCreateParent directory before lookup inventory) where
  raw : DescriptorSlot
  free : ∀ old ∈ inventory.slots, old.address ≠ raw.address
  fresh : inventory.references raw.description = []
  sameProcess : raw.reference.process = parent.owner.reference.process
  closeOnExec : raw.reference.closeOnExec = true
  files : RotationCreateFiles
  objects : files.view.modelObject = parent.files.view.modelObject
  child : RunChildLookup parent.root (successorName before) files.view
  inode : files.view.modelObject child.child = inventory.inode raw.description
  freshObject : ∀ name object, parent.files.view.child parent.root name = some object →
    parent.files.view.modelObject object ≠ inventory.inode raw.description
  empty : files.inodes.visible (inventory.inode raw.description) = ByteArray.empty
  emptySurvivors : ∀ bytes ∈ files.inodes.crashBytes (inventory.inode raw.description), bytes = ByteArray.empty
  successorSurvivors : ∀ name ∈ files.crashNames (successorName before), name = none ∨ name = some child.child
  names : ∀ name, name ≠ successorName before → files.view.child parent.root name = parent.files.view.child parent.root name
  crashFrame : ∀ name, name ≠ successorName before → files.crashNames name = parent.files.crashNames name
  bytes : ∀ inode, inode ≠ inventory.inode raw.description →
    files.inodes.visible inode = parent.files.inodes.visible inode ∧
    files.inodes.crashBytes inode = parent.files.inodes.crashBytes inode

def RotationCreateParent.project {directory : DiskDirectory} {before : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    (parent : RotationCreateParent directory before lookup inventory) (files : RotationCreateFiles) :
    State :=
  ⟨before.wal.directory, if (files.view.child parent.root (successorName before)).isSome then .created else .absent⟩

/-- The physical effects before or after raw exclusive allocation. The
caller separately supplies the runtime return or interruption. -/
inductive RotationRawCreateEffect {directory : DiskDirectory} {before : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    (parent : RotationCreateParent directory before lookup inventory) : CreateState → Prop where
  | beforeEffect : RotationRawCreateEffect parent (inventory, parent.files)
  | afterOpen (created : RotationRawSuccessor parent) :
    RotationRawCreateEffect parent (inventory.insert created.raw created.free, created.files)

private def projectRawOpen {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : RotationInFlightCut directory before} {handle : Type} {observed : ObservedRotationCreateStop cut handle}
    {inventory : DescriptorInventory} (parent : RotationCreateParent directory before observed.lookup inventory)
    (openExclusive : FilePath → ExceptT IO.Error (EStateM FilePath CreateState) handle) :
    EStateM.Result FilePath (Cache handle × State) (Except IO.Error handle) :=
  match (openExclusive (successorPath directory before)).run (inventory, parent.files) with
  | .ok value reached => .ok value (observed.cache, parent.project reached.2)
  | .error stopped reached => .error stopped (observed.cache, parent.project reached.2)

/-- The report projects the same `IO.FS.Handle.mk path .writeNew`
invocation used by rotation, before the pending-cache callback. -/
structure RotationRawCreateStop {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : RotationInFlightCut directory before} {handle : Type} {observed : ObservedRotationCreateStop cut handle}
    {inventory : DescriptorInventory} (parent : RotationCreateParent directory before observed.lookup inventory) (reached : CreateState) where
  openExclusive : FilePath → ExceptT IO.Error (EStateM FilePath CreateState) handle
  stopped : (openExclusive (successorPath directory before)).run (inventory, parent.files) =
    .error (successorPath directory before) reached
  projects : (observed.openNew (successorPath directory before)).run (observed.cache, .initial before.wal) =
    projectRawOpen parent openExclusive
  effect : RotationRawCreateEffect parent reached

namespace RotationRawCreateEffect

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : RotationInFlightCut directory before}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
  {parent : RotationCreateParent directory before lookup inventory} {reached : CreateState}

private theorem onName {view root name} (child : RunChildLookup root name view) :
    view.child root name = some child.child := by
  simpa only [child.atRoot, child.atName] using child.binds

/-- The reached census keeps the original lock reference and, in the
after-open branch, contains the new slot for the inode named by the same
canonical exclusive open. The modeled cut follows the physical binding. -/
theorem reachedSlot (effect : RotationRawCreateEffect parent reached) :
    parent.owner ∈ reached.1.slots ∧
    ((reached.1 = inventory ∧ reached.2.view.child parent.root (successorName before) = none ∧
      parent.project reached.2 = .initial before.wal) ∨
    ∃ raw : DescriptorSlot, ∃ child : DeviceInode,
      raw ∈ reached.1.slots ∧ reached.1.references raw.description = [raw.reference] ∧
      raw.reference.process = parent.owner.reference.process ∧ raw.reference.closeOnExec = true ∧
      reached.2.view.child parent.root (successorName before) = some child ∧
      reached.2.view.modelObject child = reached.1.inode raw.description ∧
      reached.2.inodes.visible (reached.1.inode raw.description) = ByteArray.empty ∧
      parent.project reached.2 = ⟨before.wal.directory, .created⟩) := by
  cases effect with
  | beforeEffect =>
    exact ⟨parent.ownerLive, .inl ⟨rfl, parent.missing, by simp [RotationCreateParent.project, State.initial, parent.missing]⟩⟩
  | afterOpen created =>
    have named := onName created.child
    exact ⟨List.mem_cons_of_mem _ parent.ownerLive, .inr
      ⟨created.raw, created.child.child, List.mem_cons_self, by simp [DescriptorInventory.references_insert, created.fresh],
        created.sameProcess, created.closeOnExec, named, created.inode, created.empty, by simp [RotationCreateParent.project, named]⟩⟩

/-- The same private lock description remains live on the canonical
lock inode. The fresh slot belongs to a different description. -/
theorem keepsLock (effect : RotationRawCreateEffect parent reached) :
    before.owners.Owns directory parent.owner.description ∧
    reached.2.view.child parent.root "LOCK" = some parent.lock.child ∧
    reached.2.view.modelObject parent.lock.child = reached.1.inode parent.owner.description ∧
    reached.1.references parent.owner.description = inventory.references parent.owner.description := by
  have name := onName parent.lock
  refine ⟨parent.ownerHeld, ?_⟩
  cases effect with
  | beforeEffect => exact ⟨name, parent.lockObject, rfl⟩
  | afterOpen created =>
    have distinct : "LOCK" ≠ successorName before := by
      intro same
      have firstChars := congrArg (fun name : String => name.toList.take 4) same
      simp [renderWalSegmentName, String.toList_append] at firstChars
    have live := inventory.mem_references.mpr ⟨parent.owner, parent.ownerLive, rfl, rfl⟩
    have separate : created.raw.description ≠ parent.owner.description := by
      intro same
      rw [← same, created.fresh] at live
      exact List.not_mem_nil live
    refine ⟨(created.names _ distinct).trans name, ?_,
      (DescriptorInventory.references_insert inventory created.raw created.free _).trans (ite_eq_right separate)⟩
    change created.files.view.modelObject parent.lock.child = inventory.inode parent.owner.description
    rw [created.objects]
    exact parent.lockObject

/-- The preceding keeper and marker stay bound to their original objects
with the same live and durable bytes. -/
theorem keepsKeeperMarker (effect : RotationRawCreateEffect parent reached) :
    reached.2.view.modelObject = parent.files.view.modelObject ∧
    reached.2.view.child parent.root (keeperName before) = some parent.keeper.child ∧
    reached.2.view.child parent.root "WAL.commit" = some parent.marker.child ∧
    reached.2.crashNames (keeperName before) = [some parent.keeper.child] ∧
    reached.2.crashNames "WAL.commit" = [some parent.marker.child] ∧
    reached.2.inodes.visible (parent.files.view.modelObject parent.keeper.child) = before.wal.active.bytes ∧
    reached.2.inodes.crashBytes (parent.files.view.modelObject parent.keeper.child) = [before.wal.active.bytes] ∧
    before.wal.directory.active.walBoundary = some (reached.2.inodes.visible (parent.files.view.modelObject parent.marker.child)) ∧
    reached.2.inodes.crashBytes (parent.files.view.modelObject parent.marker.child) =
      [reached.2.inodes.visible (parent.files.view.modelObject parent.marker.child)] := by
  have keeper := onName parent.keeper
  have marker := onName parent.marker
  cases effect with
  | beforeEffect =>
    exact ⟨rfl, keeper, marker, parent.keeperNameCrash, parent.markerNameCrash, parent.keeperBytes, parent.keeperCrash,
      parent.markerBytes, parent.markerCrash⟩
  | afterOpen created =>
    have distinctKeeper : keeperName before ≠ successorName before := by
      intro same
      exact (Nat.ne_of_lt parent.nonempty)
        (by simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName same)
    have distinctMarker : "WAL.commit" ≠ successorName before := by
      intro same
      have firstChars := congrArg (fun name : String => name.toList.take 4) same
      simp [renderWalSegmentName, String.toList_append] at firstChars
    have keepBytes := created.bytes _ (created.freshObject _ _ keeper)
    have markerBytes := created.bytes _ (created.freshObject _ _ marker)
    exact ⟨created.objects, (created.names _ distinctKeeper).trans keeper, (created.names _ distinctMarker).trans marker,
      (created.crashFrame _ distinctKeeper).trans parent.keeperNameCrash,
      (created.crashFrame _ distinctMarker).trans parent.markerNameCrash, keepBytes.1.trans parent.keeperBytes,
      keepBytes.2.trans parent.keeperCrash, parent.markerBytes.trans (congrArg some markerBytes.1.symm),
      markerBytes.2.trans (parent.markerCrash.trans (congrArg (fun payload => [payload]) markerBytes.1.symm))⟩

/-- Physical successor survivors are admitted at the projected cut. A
surviving successor has exactly the raw inode's empty bytes. -/
theorem survivor (effect : RotationRawCreateEffect parent reached) {name : Option DeviceInode}
    (survived : name ∈ reached.2.crashNames (successorName before)) :
    (parent.project reached.2).successor.MaySurvive name.isSome ∧
    ∀ child, name = some child → ∀ bytes ∈ reached.2.inodes.crashBytes (reached.2.view.modelObject child),
      bytes = ByteArray.empty := by
  cases effect with
  | beforeEffect =>
    rw [parent.absentAfterCrash] at survived
    have absent := List.mem_singleton.mp survived
    subst name
    exact ⟨by simp [RotationCreateParent.project, parent.missing, Binding.MaySurvive], by simp⟩
  | afterOpen created =>
    have named := onName created.child
    refine ⟨by simp [RotationCreateParent.project, named, Binding.MaySurvive], ?_⟩
    intro child bound bytes contained
    rcases created.successorSurvivors _ survived with absent | found
    · rw [bound] at absent
      contradiction
    · have same := Option.some.inj (bound.symm.trans found)
      rw [same, created.inode] at contained
      exact created.emptySurvivors bytes contained

/-- The crash observation supplies bytes for the inode that becomes the
keeper. If the successor name is absent, the old durable keeper supplies
those bytes. A named successor supplies the empty payload of the new inode. -/
theorem selectedKeeperPayload (effect : RotationRawCreateEffect parent reached) {name : Option DeviceInode}
    (survived : name ∈ reached.2.crashNames (successorName before)) {payload : ByteArray}
    (bytes : payload ∈ reached.2.inodes.crashBytes (reached.2.view.modelObject (name.getD parent.keeper.child))) :
    (cut.survivingWal before.wal.directory.active name.isSome).active.bytes = payload ∧
    payload = match name with
      | none => before.wal.active.bytes
      | some _ => ByteArray.empty := by
  cases name with
  | none =>
    obtain ⟨objects, _, _, _, _, _, keeperCrash, _, _⟩ := effect.keepsKeeperMarker
    change payload ∈ reached.2.inodes.crashBytes (reached.2.view.modelObject parent.keeper.child) at bytes
    rw [objects, keeperCrash] at bytes
    have old := List.mem_singleton.mp bytes
    exact ⟨old.symm, old⟩
  | some child =>
    have empty := (effect.survivor survived).2 child rfl payload bytes
    exact ⟨empty.symm, empty⟩

end RotationRawCreateEffect

/-- The exact raw observation supplies the modeled cut in the same
nonreturning public rotation schedule, with the original owner and cache. -/
theorem RotationRawCreateStop.reaches {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : RotationInFlightCut directory before} {handle : Type}
    {observed : ObservedRotationCreateStop cut handle} {inventory : DescriptorInventory}
    {parent : RotationCreateParent directory before observed.lookup inventory} {reached : CreateState}
    (report : RotationRawCreateStop (observed := observed) parent reached) (sync) :
    cut.image = parent.project reached.2 ∧
    observed.runUntilCreate sync = .error (successorPath directory before)
      (.poisoned, ⟨(observed.cache, parent.project reached.2), before.owners⟩) := by
  have raw := report.projects
  rw [projectRawOpen, report.stopped] at raw
  have same : cut.image = parent.project reached.2 :=
    congrArg Prod.snd (EStateM.Result.error.inj (observed.stopped.symm.trans raw)).2
  exact ⟨same, by rw [← same]; exact observed.stopsSchedule sync⟩

/-- The reported surviving name and its payload determine the fixed
keeper used by the retry prefix. The old durable marker chooses the
pre-rotation WAL before any later open succeeds. -/
theorem RotationRawCreateStop.refinesReopenPrefix {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : RotationInFlightCut directory before} {handle : Type}
    {observed : ObservedRotationCreateStop cut handle} {inventory : DescriptorInventory}
    {parent : RotationCreateParent directory before observed.lookup inventory} {reached : CreateState}
    (report : RotationRawCreateStop (observed := observed) parent reached) (ready : before.RetainedReady directory parent.owner.description)
    (barrier : FilePath → ExceptT IO.Error (EStateM FilePath (Cache handle × State)) Unit)
    {name : Option DeviceInode} (survived : name ∈ reached.2.crashNames (successorName before))
    {payload : ByteArray}
    (bytes : payload ∈ reached.2.inodes.crashBytes (reached.2.view.modelObject (name.getD parent.keeper.child)))
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix directory
      (cut.survivingWal before.wal.directory.active name.isSome).active.first
      (cut.crashedFiles before.wal.directory.active name.isSome) retry) :
    let keeper := (cut.survivingWal before.wal.directory.active name.isSome).active
    BoundedReopenTrace directory (CheckpointRetryTarget before.history keeper.first)
      (cut.crashedFiles before.wal.directory.active name.isSome) retry ∧
    retry.image.directory.active = before.target.pair ∧
    payload = (match name with | none => before.wal.active.bytes | some _ => ByteArray.empty) ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = keeper ∧ layout.keeper.bytes = payload ∧ Prepared retry.image layout.target layout.plan := by
  have metadata : before.wal.directory.active ∈ (parent.project reached.2).metadata.crashImages := by
    change before.wal.directory.active ∈ before.wal.directory.crashImages
    simp [ready.walDirectorySettled]
  obtain ⟨trace, pair, layout, selected, prepared⟩ := observed.refinesReopenPrefix ready barrier
    (report.reaches barrier).2 metadata (report.effect.survivor survived).1 reported
  obtain ⟨keeperBytes, payloadBytes⟩ := report.effect.selectedKeeperPayload survived bytes
  refine ⟨trace, pair, ?_, layout, selected, (congrArg WalSegment.bytes selected).trans keeperBytes, prepared⟩
  cases name <;> exact payloadBytes

end Alvoki.Storage.DiskSession
