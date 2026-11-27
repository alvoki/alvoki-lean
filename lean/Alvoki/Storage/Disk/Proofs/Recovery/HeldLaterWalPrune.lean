import Alvoki.Storage.Disk.Proofs.Recovery.ListedDirectoryAuthorization
import Alvoki.Storage.Disk.LongWalBindingPublication

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}

/-- A reported successful step and a healthy remaining action list
supply the same per-action contract for the combined list. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.ReachesAction.prependHealthy {target : Target} {initial next : FileImage} {head : Step} {rest : List Step}
    {perform : Step → EStateM IO.Error FileImage Unit}
    (effect : initial.effect target head = some next) (run : perform head initial = .ok () next)
    (tail : ∀ action prior next', ReachesAction target next rest action prior →
      prior.effect target action = some next' → perform action prior = .ok () next') :
    ∀ action prior next', ReachesAction target initial (head :: rest) action prior →
      prior.effect target action = some next' → perform action prior = .ok () next' := by
  intro action prior next' reached applied
  obtain ⟨earlier, suffix, schedule, executed⟩ := reached
  cases earlier with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at schedule
    obtain ⟨rfl, _⟩ := schedule
    have same : initial = prior := Option.some.inj executed
    subst prior
    rw [effect] at applied
    exact Option.some.inj applied ▸ run
  | cons first earlier =>
    simp only [List.cons_append, List.cons.injEq] at schedule
    obtain ⟨rfl, ordered⟩ := schedule
    simp only [List.foldlM_cons, effect, Bind.bind, Option.bind] at executed
    exact tail action prior next' ⟨earlier, suffix, ordered, executed⟩ applied

/-- One reached unlink callback and its actual parent resolution. A
successful unlink or a reported absent target clears only the canonical
later name in the observed namespace. -/
structure HeldLaterWalUnlink (held : HeldDirectoryMarkedRetryReports operations published)
    (first : Nat) (initial : FileImage) (bindings reached : FilePath → Option Nat) where
  parent : DeviceInode
  basename : String
  atRoot : parent = held.lifetime.root
  atName : basename = renderWalSegmentName first
  raw : Except IO.Error Unit
  returned : operations.removeFile (directory.file (.walSegment first)) initial =
    .ok raw (initial.unlinkLater first)
  accepted : RunCollection.ownedUnlinkResult raw = .ok ()
  missing : ∀ name message, raw = .error (.noFileOrDirectory name 2 message) →
    bindings (directory.file (.walSegment first)) = none
  removed : reached (directory.file (.walSegment first)) = none
  preserved : ∀ path, path ≠ directory.file (.walSegment first) → reached path = bindings path

/-- The observations follow the actual dispatcher order and the image
left by each unlink. -/
inductive HeldLaterWalUnlinks (held : HeldDirectoryMarkedRetryReports operations published) :
    FileImage → (FilePath → Option Nat) → List Nat → (FilePath → Option Nat) → Prop where
  | done : HeldLaterWalUnlinks held initial bindings [] bindings
  | step (head : HeldLaterWalUnlink held first initial bindings reached)
      (tail : HeldLaterWalUnlinks held (initial.unlinkLater first) reached rest final) :
      HeldLaterWalUnlinks held initial bindings (first :: rest) final

namespace HeldLaterWalUnlinks

variable {initial : FileImage} {bindings final : FilePath → Option Nat} {names : List Nat}

/-- The dispatcher runs each accepted raw callback at its reached file
image. No success of the whole pass is assumed. -/
theorem returned (reports : HeldLaterWalUnlinks held initial bindings names final) (plan : Plan) :
    ((names.map Step.unlink).forM (performPaths directory plan operations.removeFile throw
      (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile)) initial =
      .ok () (names.foldl FileImage.unlinkLater initial) := by
  induction reports with
  | done => rfl
  | step head _ ih =>
    simpa only [List.map_cons, List.foldl_cons, List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, performPaths, RunCollection.performPaths, head.returned, head.accepted] using ih

/-- Prepend the exact ordered unlink callbacks to a healthy tail. -/
theorem prependHealthy {target : Target} {initial : FileImage} {bindings final : FilePath → Option Nat}
    {names : List Nat} (plans : HeldLaterWalUnlinks held initial bindings names final) (plan : Plan) {rest : List Step}
    (tail : ∀ action prior next, ReachesAction target (names.foldl FileImage.unlinkLater initial) rest action prior →
      prior.effect target action = some next →
      performPaths directory plan operations.removeFile throw (operations.write operations.cache)
        (operations.sync operations.cache) operations.renameFile action prior = .ok () next) :
    ∀ action prior next, ReachesAction target initial (names.map Step.unlink ++ rest) action prior →
      prior.effect target action = some next →
      performPaths directory plan operations.removeFile throw (operations.write operations.cache)
        (operations.sync operations.cache) operations.renameFile action prior = .ok () next := by
  induction plans with
  | done => simpa using tail
  | @step first current bindings reached names final head _ ih =>
    have removed : performPaths directory plan operations.removeFile throw (operations.write operations.cache)
        (operations.sync operations.cache) operations.renameFile (.unlink first) current =
          .ok () (current.unlinkLater first) := by
      simp [performPaths, RunCollection.performPaths, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        head.returned, head.accepted]
    exact ReachesAction.prependHealthy rfl removed (ih tail)

theorem keepsBinding (reports : HeldLaterWalUnlinks held initial bindings names final) (path : FilePath)
    (untouched : ∀ first ∈ names, path ≠ directory.file (.walSegment first)) :
    final path = bindings path := by
  induction reports with
  | done => rfl
  | step head _ ih =>
    exact (ih fun first member => untouched first (List.mem_cons_of_mem _ member)).trans
      (head.preserved path (untouched _ List.mem_cons_self))

theorem removesBinding (reports : HeldLaterWalUnlinks held initial bindings names final)
    {first : Nat} (listed : first ∈ names) : final (directory.file (.walSegment first)) = none := by
  induction reports with
  | done => simp at listed
  | @step headStart initial bindings reached rest final head tail ih =>
    rcases List.mem_cons.mp listed with rfl | later
    · by_cases again : first ∈ rest
      · exact ih again
      have kept := tail.keepsBinding (directory.file (.walSegment first)) (by
        intro other member same
        exact again (directory.walSegment_path_injective same ▸ member))
      exact kept.trans head.removed
    · exact ih later

end HeldLaterWalUnlinks

private def heldFiles (before : LockedFileState FileImage) (directory : DiskDirectory)
    (slot : DescriptorSlot) (image : FileImage) : LockedFileState FileImage :=
  { before with image, owners := before.owners.set (directory.file .lock) (some slot.description) }

def _root_.Alvoki.Storage.WalSegmentRepair.FileImage.unlinkVisibleSuffix (image : FileImage) : FileImage :=
  image.later.visible.foldl FileImage.unlinkLater image.syncDirectory

private abbrev keeperCache (authorization : ListedDirectoryAuthorization held) :=
  operations.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
    (authorization.keeper.inventory, authorization.keeper.slot, 0)
    layout.keeper.bytes.size authorization.keeper.metadata.byteSize.toNat

/-- The observed later-name pass starts after successful authorization.
It uses the sorted checked catalog and keeps the original cached
directory and lock through the suffix barrier. -/
structure ListedLaterWalPrune (authorization : ListedDirectoryAuthorization held) where
  authorized : authorization.outcome = .completed
  bindings : FilePath → Option Nat
  projectedListed : ∀ first ∈ before.image.later.visible,
    bindings (directory.file (.walSegment first)) =
      (held.lifetime.namespaceView.child held.lifetime.root (renderWalSegmentName first)).map
        held.lifetime.namespaceView.modelObject
  reached : FilePath → Option Nat
  unlinks : HeldLaterWalUnlinks held before.image.syncDirectory bindings before.image.later.visible reached
  afterAuthorization : List LockReferenceDrop
  directoryRetained : held.lifetime.directorySlot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  lockRetained : operations.slot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  directoryBound : reached directory.path = some (operations.descriptors.inode held.lifetime.directorySlot.description)
  lockBound : reached (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  effect :
    let unlinked := before.image.unlinkVisibleSuffix
    authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0)
      (heldFiles before directory operations.slot unlinked) =
      .ok () (heldFiles before directory operations.slot unlinked.syncDirectory)
  projected :
    operations.sync operations.cache #[directory.path] (before.image.unlinkVisibleSuffix) =
      projectDirectorySync (SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)
        #[directory.path] (keeperCache authorization, heldFiles before directory operations.slot (before.image.unlinkVisibleSuffix)))

namespace ListedLaterWalPrune

variable {authorization : ListedDirectoryAuthorization held}

theorem catalog (prune : ListedLaterWalPrune authorization) :
    before.image.later.visible.Pairwise (· < ·) ∧
    ∀ first ∈ before.image.later.visible,
      renderWalSegmentName first ∈ operations.reported.inventory.names ∧
      (∃ metadata, operations.reported.inventory.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        metadata.type = .file ∧ metadata.numLinks = 1) ∧
      ∃ object, held.lifetime.namespaceView.child held.lifetime.root (renderWalSegmentName first) = some object ∧
        prune.bindings (directory.file (.walSegment first)) = some (held.lifetime.namespaceView.modelObject object) := by
  refine ⟨(List.pairwise_append.mp operations.reported.ordered).2.1, ?_⟩
  intro first listed
  have member : first ∈ operations.reported.older ++ (layout.sealed ++ [layout.keeper]).map WalSegment.first ++
      before.image.later.visible := List.mem_append_right _ listed
  have named := (operations.reported.present first).mpr member
  obtain ⟨object, bound⟩ := (held.lifetime.namespaceView.namesExact _ _).mp
    (held.checkedListing.2.mem_iff.mp named)
  exact ⟨named, operations.reported.regular _ member, object, bound, by rw [prune.projectedListed _ listed, bound]; rfl⟩

/-- The reached name effects exclude the keeper, all selected seals and
every reserved database name. -/
theorem selectedBindings (prune : ListedLaterWalPrune authorization)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    (∀ first ∈ before.image.later.visible, prune.reached (directory.file (.walSegment first)) = none) ∧
    (∀ segment ∈ layout.sealed ++ [layout.keeper],
      prune.reached (directory.file (.walSegment segment.first)) = prune.bindings (directory.file (.walSegment segment.first))) ∧
    ∀ file, (∀ first, file ≠ .walSegment first) → prune.reached (directory.file file) = prune.bindings (directory.file file) := by
  refine ⟨fun _ => prune.unlinks.removesBinding, ?_, ?_⟩
  · intro segment selected
    apply prune.unlinks.keepsBinding
    intro first member same
    have bound := layout.through ▸ layout.chain.startsWithin segment selected
    have newer := later first member
    have offset := directory.walSegment_path_injective same
    omega
  · intro file reserved
    exact prune.unlinks.keepsBinding (directory.file file) (fun first _ same => by
      obtain ⟨start, name⟩ := DiskDirectory.walSegment_exclusive same
      exact reserved start name)

private theorem preservesFileFields (initial : FileImage) (names : List Nat) :
    let reached := names.foldl FileImage.unlinkLater initial
    reached.directory = initial.directory ∧ reached.kept = initial.kept ∧ reached.keeper = initial.keeper := by
  induction names generalizing initial with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons name rest ih => exact ih (initial.unlinkLater name)

private theorem visibleAfter (initial : FileImage) (names : List Nat) (first : Nat) :
    first ∈ (names.foldl FileImage.unlinkLater initial).later.visible ↔
      first ∈ initial.later.visible ∧ first ∉ names := by
  induction names generalizing initial with
  | nil => simp
  | cons name rest ih =>
    rw [List.foldl_cons, ih]
    change (first ∈ initial.later.visible.filter (fun offset => decide (offset ≠ name)) ∧ first ∉ rest) ↔ _
    simp [List.mem_filter, List.mem_cons, and_assoc]

/-- Once the directory barrier returns, covering the visible suffix suffices
in any unlink order. Before the barrier the crash choices can depend on
the prefix that actually ran. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.FileImage.syncAfterCoveringUnlinks
    (initial : FileImage) (names : List Nat)
    (covers : ∀ name ∈ initial.later.visible, name ∈ names) :
    (names.foldl FileImage.unlinkLater initial).syncDirectory =
      { initial.syncDirectory with later := LaterNames.settled [] } := by
  have empty : (names.foldl FileImage.unlinkLater initial).later.visible = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name present
    obtain ⟨visible, missing⟩ := (visibleAfter initial names name).mp present
    exact missing (covers name visible)
  obtain ⟨directory, kept, keeper⟩ := preservesFileFields initial names
  simp only [FileImage.syncDirectory, LaterNames.syncDirectory, directory, kept, keeper, empty]

/-- The complete suffix barrier leaves only the empty later-name choice.
The selected directory pair, sealed bytes and the keeper's old contents
and staging choices are unchanged through pruning. -/
theorem settledImage (initial : FileImage) :
    (initial.unlinkVisibleSuffix).syncDirectory.later.DurablyEmpty ∧
    (initial.unlinkVisibleSuffix).syncDirectory.directory = initial.syncDirectory.directory ∧
    (initial.unlinkVisibleSuffix).syncDirectory.kept = initial.kept ∧
    (initial.unlinkVisibleSuffix).syncDirectory.keeper = initial.keeper := by
  unfold FileImage.unlinkVisibleSuffix
  rw [FileImage.syncAfterCoveringUnlinks initial.syncDirectory initial.later.visible (fun _ present => present)]
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The directory and lock issuers remain live in the same reached census.
The callback settles the suffix through the captured directory handle
without replacing the keeper-cache entry. -/
theorem suffixBarrier (prune : ListedLaterWalPrune authorization) :
    let atBarrier := held.listing.afterClose.afterDrops (authorization.afterListing ++ prune.afterAuthorization)
    held.lifetime.directorySlot ∈ atBarrier.slots ∧ operations.slot ∈ atBarrier.slots ∧
    prune.reached directory.path = some (atBarrier.inode held.lifetime.directorySlot.description) ∧
    prune.reached (directory.file .lock) = some (atBarrier.inode operations.slot.description) ∧
    operations.sync operations.cache #[directory.path] (before.image.unlinkVisibleSuffix) =
      .ok () (before.image.unlinkVisibleSuffix).syncDirectory := by
  intro atBarrier
  refine ⟨prune.directoryRetained, prune.lockRetained, ?_, ?_, ?_⟩
  · simpa only [atBarrier, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using prune.directoryBound
  · simpa only [atBarrier, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using prune.lockBound
  · rw [prune.projected, SyncPathGroup.run_single]
    have captured : (keeperCache authorization).directory =
        some (operations.descriptors, held.lifetime.directorySlot, 0) := by
      simp only [keeperCache, Cache.captureKeeper]
      split <;> exact held.capturedDirectory
    let atUnlink := heldFiles before directory operations.slot (before.image.unlinkVisibleSuffix)
    have routed : sync directory.path authorization.openRead authorization.fsync directory.path
        (keeperCache authorization, atUnlink) =
        withCache (keeperCache authorization) (authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0)
          atUnlink) := by simp [sync, Cache.resolve, captured]
    rw [routed, prune.effect]
    rfl

/-- The reached prefix of the actual long-keeper finisher completes
authorization, the exact ordered unlinks and their directory barrier
before passing the settled image to the staged replacement callbacks. -/
theorem finishAfterPrune (prune : ListedLaterWalPrune authorization)
    (long : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    let run := performPaths directory layout.boundedPlan operations.removeFile throw
      (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    (do
      run (.replace .writeStaged)
      run (.replace .syncStaged)
      run (.replace .renameStaged)
      run (.replace .syncDirectory)
      pure () : EStateM IO.Error FileImage Unit) (before.image.unlinkVisibleSuffix).syncDirectory := by
  intro run
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have valid := layout.boundedPlan_valid later
  have longer : layout.boundedPlan.keeperSize < authorization.keeper.metadata.byteSize.toNat := size ▸ long
  have unlinks :
      ((layout.boundedPlan.newer.map Step.unlink).forM run) before.image.syncDirectory =
        .ok () (before.image.unlinkVisibleSuffix) := prune.unlinks.returned layout.boundedPlan
  have barrier : run .syncPruned (before.image.unlinkVisibleSuffix) =
      .ok () (before.image.unlinkVisibleSuffix).syncDirectory := prune.suffixBarrier.2.2.2.2
  have pruned : (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM run)
      before.image.syncDirectory = .ok () (before.image.unlinkVisibleSuffix).syncDirectory := by
    rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    simp only [Bind.bind, EStateM.bind, unlinks, List.forM_eq_forM, List.forM_cons, List.forM_nil,
      barrier, Pure.pure, EStateM.pure]
  have unfoldFinish := congrFun
    (finishBoundedMarkedOpen_long directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile valid size longer) before.image
  rw [unfoldFinish]
  change (do
    operations.sync operations.cache #[directory.path]
    ((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM run
    run (.replace .writeStaged)
    run (.replace .syncStaged)
    run (.replace .renameStaged)
    run (.replace .syncDirectory)
    pure () : EStateM IO.Error FileImage Unit) before.image = _
  simp only [authorization.settles prune.authorized, Bind.bind, EStateM.bind, pruned]

end ListedLaterWalPrune

/-- With a later name or a long keeper, the bounded finisher executes
the same authorized unlink and suffix-sync prefix. Any error in that
prefix returns immediately, regardless of the eventual keeper action. -/
theorem ListedDirectoryAuthorization.finishAfterPruneError (authorization : ListedDirectoryAuthorization held)
    (completed : authorization.outcome = .completed)
    (prunes : before.image.later.visible ≠ [] ∨ layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first)
    {cause : IO.Error} {reached : FileImage}
    (failed :
      let run := performPaths directory layout.boundedPlan operations.removeFile throw
        (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
      ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) before.image.syncDirectory =
        .error cause reached) :
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error cause reached := by
  let plan := layout.boundedPlan
  let physicalSize := authorization.keeper.metadata.byteSize.toNat
  have size : plan.keeperBytes.size = plan.keeperSize := layout.target.trimmedSize
  have valid : plan.valid = true := layout.boundedPlan_valid later
  have fits : plan.keeperSize ≤ physicalSize := by
    rw [show physicalSize = layout.plan.keeperBytes.size from authorization.keeper.extent, ← size]
    change layout.keeper.bytes.size ≤ (layout.keeper.bytes ++ layout.tail).size
    simp [ByteArray.size_append]
  have full : (plan.newer.isEmpty && (physicalSize == plan.keeperSize)) = false := by
    rcases prunes with names | long
    · have nonempty : plan.newer.isEmpty = false := by
        change before.image.later.visible.isEmpty = false
        cases present : before.image.later.visible with
        | nil => exact False.elim (names present)
        | cons => rfl
      simp [nonempty]
    · have larger : plan.keeperSize < physicalSize := size ▸ long
      simp [Nat.ne_of_gt larger]
  have schedule : steps plan.newer (decide (plan.keeperSize < physicalSize)) =
      (plan.newer.map Step.unlink ++ [Step.syncPruned]) ++
        (if decide (plan.keeperSize < physicalSize) then Publication.steps.map Step.replace else [.syncKeeper]) := by
    simp [steps, List.append_assoc]
  change finishBoundedMarkedOpen directory plan physicalSize operations.removeFile (operations.write operations.cache)
    (operations.sync operations.cache) operations.renameFile before.image = _
  simp only [finishBoundedMarkedOpen, valid, size, beq_self_eq_true, decide_eq_true fits, Bool.and_true,
    ite_true, full, Bool.false_eq_true, ite_false, runRepairPlan, schedule]
  rw [List.forM_eq_forM, List.forM_append]
  simp only [Bind.bind, EStateM.bind, authorization.settles completed]
  rw [← List.forM_eq_forM]
  dsimp only at failed
  rw [failed]

/-- An unlink error that survives the owned-ENOENT rule can be reported
before or after removing its canonical child. -/
structure HeldLaterWalUnlinkFailure (held : HeldDirectoryMarkedRetryReports operations published)
    (first : Nat) (initial : FileImage) where
  parent : DeviceInode
  basename : String
  atRoot : parent = held.lifetime.root
  atName : basename = renderWalSegmentName first
  cause : IO.Error
  reached : FileImage
  reported : operations.removeFile (directory.file (.walSegment first)) initial = .ok (.error cause) reached
  propagated : RunCollection.ownedUnlinkResult (.error cause) = .error cause
  effect : reached = initial ∨ reached = initial.unlinkLater first

/-- A failed reached unlink returns its exact error and file image. The
remaining suffix, its barrier and any keeper action are skipped. -/
theorem ListedDirectoryAuthorization.finishAfterUnlinkError (authorization : ListedDirectoryAuthorization held)
    (completed : authorization.outcome = .completed)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first)
    {earlier rest : List Nat} {first : Nat} {bindings final : FilePath → Option Nat}
    (order : before.image.later.visible = earlier ++ first :: rest)
    (passed : HeldLaterWalUnlinks held before.image.syncDirectory bindings earlier final)
    (failed : HeldLaterWalUnlinkFailure held first (earlier.foldl FileImage.unlinkLater before.image.syncDirectory)) :
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error failed.cause failed.reached := by
  let run := performPaths directory layout.boundedPlan operations.removeFile throw
    (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
  let atError := earlier.foldl FileImage.unlinkLater before.image.syncDirectory
  have reported : run (.unlink first) atError = .error failed.cause failed.reached := by
    simp [run, atError, performPaths, RunCollection.performPaths, Bind.bind, EStateM.bind, failed.reported,
      failed.propagated, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  have stepOrder : (layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]) =
      (earlier.map Step.unlink) ++ (.unlink first :: rest.map Step.unlink ++ [Step.syncPruned]) := by
    change before.image.later.visible.map Step.unlink ++ [Step.syncPruned] = _
    rw [order, List.map_append, List.map_cons, List.append_assoc]
  have listError : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM run)
      before.image.syncDirectory = .error failed.cause failed.reached := by
    rw [stepOrder, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    have prior : ((earlier.map Step.unlink).forM run) before.image.syncDirectory =
        .ok () atError := passed.returned layout.boundedPlan
    simp only [Bind.bind, EStateM.bind, prior, List.cons_append, List.forM_eq_forM, List.forM_cons, reported]
  have nonempty : before.image.later.visible ≠ [] := by rw [order]; simp
  exact authorization.finishAfterPruneError completed (.inl nonempty) later listError

end Alvoki.Storage.DiskSession
