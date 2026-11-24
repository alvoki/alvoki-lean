import Alvoki.Storage.Disk.CachedWalChunkReports

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting

/-- The directory barrier after an aligned keeper read uses the directory
description already in the cache. Its observed live slot and inode binding
identify the directory whose names settle. The syscall report distinguishes
an error before settlement from one after settlement. The keeper entry stays
pending in either case. -/
theorem readWalKeeperWithChunks_syncCapturedDirectory
    {reads : CheckpointRunChunkReads} (directory : DiskDirectory) (keeper : Nat)
    {selectedBytes tail : ByteArray}
    (seen : reads.ObservesFile (directory.file (.walSegment keeper)) (selectedBytes ++ tail))
    (fits : selectedBytes.size < USize.size) (aligned : selectedBytes.size = seen.metadata.byteSize.toNat)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (inventory : DescriptorInventory) (slot : DescriptorSlot) (offset : Nat)
    (hasDirectory : cache.directory = some (inventory, slot, offset)) (drops : List LockReferenceDrop)
    (issuing : slot.reference ∈ (inventory.afterDrops drops).references slot.description)
    (bindings : FilePath → Option Nat) (boundAtSync : bindings directory.path = some (inventory.inode slot.description))
    (outcome : DelayedDirectorySyncOutcome) (initial : LockedFileState FileImage)
    (openRead : FilePath → EStateM IO.Error (LockedFileState FileImage) (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error (LockedFileState FileImage) Unit) :
    let path := directory.file (.walSegment keeper)
    let remembered := cache.remember path (seen.inventory, seen.slot, 0)
    let report := inventory.delayedDirectorySync drops directory slot.description slot.reference issuing
      bindings boundAtSync outcome
    fsync (inventory, slot, offset) initial = report.run initial →
    readWalKeeperWithChunks reads path selectedBytes.size seen.metadata.byteSize.toNat (cache, initial) =
        .ok selectedBytes (remembered, initial) ∧
      sync directory.path openRead fsync directory.path (remembered, initial) =
        withCache remembered (report.run initial) ∧
      SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path] (remembered, initial) =
        SyncPathGroup.run (m := EStateM IO.Error (Cache _ × LockedFileState FileImage))
          (fun _ (current, before) => withCache current (report.run before))
          #[directory.path] (remembered, initial) := by
  intro path remembered report effect
  have routed : sync directory.path openRead fsync directory.path (remembered, initial) =
      withCache remembered (report.run initial) := by
    simp [sync, Cache.resolve, remembered, Cache.remember, hasDirectory, effect]
  refine ⟨?_, routed, ?_⟩
  · simpa [remembered, Cache.captureKeeper, aligned] using readWalKeeperWithChunks_exact seen fits cache initial
  · rw [SyncPathGroup.run_single, routed]
    let reportSync (_ : FilePath) :
        EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × LockedFileState FileImage) Unit :=
      fun (current, before) => withCache current (report.run before)
    exact (SyncPathGroup.run_single reportSync directory.path (remembered, initial)).symm

/-- A successful aligned keeper read records its exact open description.
The directory barrier leaves that cache entry untouched. The keeper barrier
uses the entry, consumes it on every result, and acts on the observed inode.
Slot survival, the effect-time binding, and both syscall effects come from
the native report. -/
theorem readWalKeeperWithChunks_syncAligned
    {state : Type} {reads : CheckpointRunChunkReads} {dir path : FilePath}
    {selectedBytes tail : ByteArray} (seen : reads.ObservesFile path (selectedBytes ++ tail))
    (fits : selectedBytes.size < USize.size) (aligned : selectedBytes.size = seen.metadata.byteSize.toNat)
    (separate : path ≠ dir) (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    {directoryHandle : DescriptorInventory × DescriptorSlot × Nat}
    (hasDirectory : cache.directory = some directoryHandle)
    (openRead : FilePath → EStateM IO.Error state (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error state Unit)
    {initial authorized : state} (directoryEffect : fsync directoryHandle initial = .ok () authorized)
    (drops : List LockReferenceDrop)
    (issuing : seen.slot.reference ∈ (seen.inventory.afterDrops drops).references seen.slot.description)
    (bindings : FilePath → Option Nat) (boundAtSync : bindings path = some seen.object)
    (persist : Nat → state → state) {effective : Bool}
    (effect : FsyncResult authorized (persist seen.object authorized) effective
      (fsync (seen.inventory, seen.slot, 0) authorized)) :
    let captured := (seen.inventory, seen.slot, 0)
    let remembered := cache.remember path captured
    readWalKeeperWithChunks reads path selectedBytes.size seen.metadata.byteSize.toNat (cache, initial) =
        .ok selectedBytes (remembered, initial) ∧
      sync dir openRead fsync dir (remembered, initial) = .ok () (remembered, authorized) ∧
      sync dir openRead fsync path (remembered, authorized) =
        withCache (cache.consume path) (fsync captured authorized) ∧
      ∃ observed : FsyncObservation (fun handle => handle.2.1.description)
          (fun handle => handle.1.inode handle.2.1.description) captured authorized persist (fsync captured authorized),
        observed.issuer = seen.slot.reference ∧ observed.effective = effective ∧
        bindings path = some observed.effectInode := by
  intro captured remembered
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [remembered, captured, Cache.captureKeeper, aligned] using
      readWalKeeperWithChunks_exact seen fits cache initial
  · simp [sync, Cache.resolve, remembered, Cache.remember, hasDirectory, directoryEffect, withCache]
  · rw [show remembered = cache.remember path captured from rfl,
      syncRemembered separate captured openRead fsync authorized]
    cases fsync captured authorized <;> rfl
  · have observedEffect : FsyncResult authorized (persist (seen.inventory.inode seen.slot.description) authorized)
        effective (fsync captured authorized) := by
      rw [seen.sameObject]
      exact effect
    let observed := FsyncObservation.ofInventory seen.inventory drops
      (fun handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
      captured seen.slot.reference issuing rfl authorized persist observedEffect
    refine ⟨observed, rfl, rfl, ?_⟩
    change bindings path = some (seen.inventory.inode seen.slot.description)
    simpa only [seen.sameObject] using boundAtSync

private abbrev KeeperOpen := DescriptorInventory × DescriptorSlot × Nat
private abbrev KeeperRepairState := Cache KeeperOpen × LockedFileState FileImage

/-- The two singleton barriers reached by aligned recovery, with their
exact returned outcomes and cache changes. -/
def alignedWalRepairEffects {directory : DiskDirectory} (path : FilePath)
    (report : DelayedDirectorySync directory) (initial : LockedFileState FileImage)
    (cache : Cache KeeperOpen) (captured : KeeperOpen)
    (fsync : KeeperOpen → EStateM IO.Error (LockedFileState FileImage) Unit) (selected : ByteArray) :
    EStateM.Result IO.Error KeeperRepairState ByteArray :=
  (do
    SyncPathGroup.run (fun _ (current, files) => withCache current (report.run files)) #[directory.path]
    SyncPathGroup.run (fun _ (_, files) => withCache (cache.consume path) (fsync captured files)) #[path]
    pure selected : EStateM IO.Error KeeperRepairState ByteArray) (cache.remember path captured, initial)

/-- A single aligned read supplies the byte callback used by WAL selection
and the handle consumed by the actual bounded finisher. The directory
barrier keeps that pending handle. Only a successful directory callback
reaches the keeper callback, and each singleton barrier preserves its
own reached success or failure state. -/
theorem readWalKeeperWithChunks_finishAligned
    {reads : CheckpointRunChunkReads} (directory : DiskDirectory) (plan : Plan) {tail : ByteArray}
    (seen : reads.ObservesFile (directory.file (.walSegment plan.keeper)) (plan.keeperBytes ++ tail))
    (valid : plan.valid = true) (bytes : plan.keeperBytes.size = plan.keeperSize) (noLater : plan.newer = [])
    (fits : plan.keeperBytes.size < USize.size) (aligned : plan.keeperBytes.size = seen.metadata.byteSize.toNat)
    (separate : directory.file (.walSegment plan.keeper) ≠ directory.path)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (inventory : DescriptorInventory) (slot : DescriptorSlot) (offset : Nat)
    (hasDirectory : cache.directory = some (inventory, slot, offset))
    (directoryDrops : List LockReferenceDrop)
    (directoryLive : slot.reference ∈ (inventory.afterDrops directoryDrops).references slot.description)
    (directoryBindings : FilePath → Option Nat)
    (directoryBound : directoryBindings directory.path = some (inventory.inode slot.description))
    (directoryOutcome : DelayedDirectorySyncOutcome) (initial : LockedFileState FileImage)
    (openRead : FilePath → EStateM IO.Error (LockedFileState FileImage) (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error (LockedFileState FileImage) Unit)
    (remove : FilePath → EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × LockedFileState FileImage)
      (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error
      (Cache (DescriptorInventory × DescriptorSlot × Nat) × LockedFileState FileImage) Unit)
    (rename : FilePath → FilePath → EStateM IO.Error
      (Cache (DescriptorInventory × DescriptorSlot × Nat) × LockedFileState FileImage) Unit) :
    let path := directory.file (.walSegment plan.keeper)
    let captured := (seen.inventory, seen.slot, 0)
    let report := inventory.delayedDirectorySync directoryDrops directory slot.description slot.reference directoryLive
      directoryBindings directoryBound directoryOutcome
    let grouped := SyncPathGroup.run (sync directory.path openRead fsync)
    fsync (inventory, slot, offset) initial = report.run initial →
    readWalKeeperBytes reads path plan.keeperBytes.size seen.metadata.byteSize.toNat = .ok plan.keeperBytes ∧
      (do
        let selected ← readWalKeeperWithChunks reads path plan.keeperBytes.size seen.metadata.byteSize.toNat
        finishBoundedMarkedOpen directory plan seen.metadata.byteSize.toNat remove write grouped rename
        pure selected : EStateM IO.Error _ ByteArray) (cache, initial) =
      alignedWalRepairEffects path report initial cache captured fsync plan.keeperBytes := by
  intro path captured report grouped directoryEffect
  let remembered := cache.remember path captured
  let directorySync (_ : FilePath) : EStateM IO.Error KeeperRepairState Unit :=
    fun (current, files) => withCache current (report.run files)
  let keeperSync (_ : FilePath) : EStateM IO.Error KeeperRepairState Unit :=
    fun (_, files) => withCache (cache.consume path) (fsync captured files)
  obtain ⟨read, _, directoryGrouped⟩ := readWalKeeperWithChunks_syncCapturedDirectory
    directory plan.keeper seen fits aligned cache inventory slot offset hasDirectory directoryDrops directoryLive
    directoryBindings directoryBound directoryOutcome initial openRead fsync directoryEffect
  have readExact : readWalKeeperWithChunks reads path plan.keeperBytes.size seen.metadata.byteSize.toNat
      (cache, initial) = .ok plan.keeperBytes (remembered, initial) := read
  have alignedSize : seen.metadata.byteSize.toNat = plan.keeperSize := aligned.symm.trans bytes
  have finish : finishBoundedMarkedOpen directory plan seen.metadata.byteSize.toNat remove write grouped rename =
      (do grouped #[directory.path]; grouped #[path]) := by
    simp [finishBoundedMarkedOpen, valid, bytes, noLater, alignedSize, path]
  refine ⟨?_, ?_⟩
  · rw [← readWalKeeperWithChunks_project reads _ _ _ cache initial, readExact]
  · change _ = (do
      SyncPathGroup.run directorySync #[directory.path]
      SyncPathGroup.run keeperSync #[path]
      pure plan.keeperBytes : EStateM IO.Error KeeperRepairState ByteArray) (remembered, initial)
    have directoryRouted : grouped #[directory.path] (remembered, initial) =
        SyncPathGroup.run directorySync #[directory.path] (remembered, initial) := directoryGrouped
    have keeperGrouped (after : LockedFileState FileImage) :
        grouped #[path] (remembered, after) = SyncPathGroup.run keeperSync #[path] (remembered, after) := by
      have route : sync directory.path openRead fsync path (remembered, after) =
          keeperSync path (remembered, after) := by
        change sync directory.path openRead fsync path (cache.remember path captured, after) =
          withCache (cache.consume path) (fsync captured after)
        rw [syncRemembered separate captured openRead fsync after]
        cases fsync captured after <;> rfl
      have groupedReport := SyncPathGroup.run_single keeperSync path (remembered, after)
      rw [← route] at groupedReport
      exact (SyncPathGroup.run_single (sync directory.path openRead fsync) path (remembered, after)).trans
        groupedReport.symm
    simp only [finish, Bind.bind, EStateM.bind, readExact, directoryRouted]
    rw [SyncPathGroup.run_single directorySync]
    cases directoryRan : report.run initial with
    | error cause reached => simp [directorySync, directoryRan, withCache]
    | ok result reached =>
      cases result
      simp only [directorySync, directoryRan, withCache, keeperGrouped]

/-- A reported directory error returns its exact reached image with the
keeper still pending. The keeper syscall has not been reached. -/
theorem alignedWalRepairEffects_directoryError {directory : DiskDirectory} {path : FilePath}
    (report : DelayedDirectorySync directory) (initial : LockedFileState FileImage)
    (cache : Cache KeeperOpen) (captured : KeeperOpen)
    (fsync : KeeperOpen → EStateM IO.Error (LockedFileState FileImage) Unit) (selected : ByteArray)
    {cause : IO.Error} {reached : LockedFileState FileImage}
    (reported : report.run initial = .error cause reached)
    {returned : EStateM.Result IO.Error KeeperRepairState ByteArray}
    (execution : returned = alignedWalRepairEffects path report initial cache captured fsync selected) :
    returned = .error (IO.userError s!"sync failed for '{directory.path}': {cause}")
      (cache.remember path captured, reached) := by
  let directorySync (_ : FilePath) : EStateM IO.Error KeeperRepairState Unit :=
    fun (current, files) => withCache current (report.run files)
  have directoryRan : SyncPathGroup.run directorySync #[directory.path] (cache.remember path captured, initial) =
      .error (IO.userError s!"sync failed for '{directory.path}': {cause}")
        (cache.remember path captured, reached) := by
    rw [SyncPathGroup.run_single]
    simp only [directorySync, reported, withCache]
    rfl
  rw [execution]
  change (do
    SyncPathGroup.run directorySync #[directory.path]
    SyncPathGroup.run (fun _ (_, files) => withCache (cache.consume path) (fsync captured files)) #[path]
    pure selected : EStateM IO.Error KeeperRepairState ByteArray) (cache.remember path captured, initial) = _
  simp only [Bind.bind, EStateM.bind, directoryRan]

/-- After the directory barrier succeeds, classify the reached keeper
syscall on the same open descriptor that supplied the prefix. The native
report states whether the keeper bytes settled, including on error. The
visible binding and live slot identify the inode at effect time. -/
theorem alignedWalRepairEffects_observedKeeper
    {reads : CheckpointRunChunkReads} {directory : DiskDirectory} {path : FilePath} {selected tail : ByteArray}
    (seen : reads.ObservesFile path (selected ++ tail)) (aligned : selected.size = seen.metadata.byteSize.toNat)
    (report : DelayedDirectorySync directory) (completed : report.outcome = .completed)
    (initial : LockedFileState FileImage) (visible : initial.image.keeper.active = some (selected ++ tail))
    (cache : Cache KeeperOpen) (fsync : KeeperOpen → EStateM IO.Error (LockedFileState FileImage) Unit)
    (drops : List LockReferenceDrop)
    (issuing : seen.slot.reference ∈ (seen.inventory.afterDrops drops).references seen.slot.description)
    (bindings : FilePath → Option Nat) (bound : bindings path = some seen.object) {effective : Bool}
    {returned : EStateM.Result IO.Error KeeperRepairState ByteArray} :
    let captured := (seen.inventory, seen.slot, 0)
    let authorized := { initial with image := initial.image.syncDirectory }
    let settled := { authorized with image := authorized.image.syncKeeper }
    returned = alignedWalRepairEffects path report initial cache captured fsync selected →
    FsyncResult authorized settled effective (fsync captured authorized) →
    (∃ observed : FsyncObservation (fun handle => handle.2.1.description)
        (fun handle => handle.1.inode handle.2.1.description) captured authorized
        (fun _ files => { files with image := files.image.syncKeeper }) (fsync captured authorized),
      observed.issuer = seen.slot.reference ∧ observed.effective = effective ∧
      bindings path = some observed.effectInode) ∧
    authorized.image.keeper.active = some selected ∧
    authorized.image.keeper.crashImages = initial.image.keeper.crashImages ∧
    settled.image.keeper.active = some selected ∧ settled.image.keeper.crashImages = [some selected] ∧
    (match fsync captured authorized with
      | .ok () _ =>
        returned = .ok selected (cache.consume path, settled)
      | .error cause _ =>
        returned = .error (IO.userError s!"sync failed for '{path}': {cause}")
          (cache.consume path, if effective then settled else authorized)) := by
  intro captured authorized settled execution effect
  subst returned
  have tailEmpty : tail = ByteArray.empty := by
    rw [seen.extent, ByteArray.size_append] at aligned
    exact ByteArray.size_eq_zero_iff.mp (by omega)
  have active : initial.image.keeper.active = some selected := by
    simpa [tailEmpty] using visible
  let observed := FsyncObservation.ofInventory seen.inventory drops
    (fun handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
    captured seen.slot.reference issuing rfl authorized
    (fun _ files => { files with image := files.image.syncKeeper }) effect
  refine ⟨⟨observed, rfl, rfl, ?_⟩, active, rfl, active, ?_, ?_⟩
  · change bindings path = some (seen.inventory.inode seen.slot.description)
    simpa only [seen.sameObject] using bound
  · change [initial.image.keeper.active] = [some selected]
    rw [active]
  · let remembered := cache.remember path captured
    let directorySync (_ : FilePath) : EStateM IO.Error KeeperRepairState Unit :=
      fun (current, files) => withCache current (report.run files)
    let keeperSync (_ : FilePath) : EStateM IO.Error KeeperRepairState Unit :=
      fun (_, files) => withCache (cache.consume path) (fsync captured files)
    have directoryRan : SyncPathGroup.run directorySync #[directory.path] (remembered, initial) =
        .ok () (remembered, authorized) := by
      rw [SyncPathGroup.run_single]
      simp [directorySync, DelayedDirectorySync.run, completed, withCache, authorized]
    have repair : alignedWalRepairEffects path report initial cache captured fsync selected =
        (do SyncPathGroup.run keeperSync #[path]; pure selected : EStateM IO.Error KeeperRepairState ByteArray)
          (remembered, authorized) := by
      change (do
        SyncPathGroup.run directorySync #[directory.path]
        SyncPathGroup.run keeperSync #[path]
        pure selected : EStateM IO.Error KeeperRepairState ByteArray) (remembered, initial) = _
      simp only [Bind.bind, EStateM.bind, directoryRan]
    simp only [repair, Bind.bind, EStateM.bind, SyncPathGroup.run_single keeperSync, keeperSync]
    generalize resultEq : fsync captured authorized = result at effect ⊢
    cases effect <;> rfl

end Alvoki.Storage.WalSegmentRepair
