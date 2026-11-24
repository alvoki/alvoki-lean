import Alvoki.Storage.Disk.MarkedWalReopenModel

namespace Alvoki.WAL.Boundary

open Storage

/-- The WAL has an existing inode. Binding choices and byte survival choices
are independent components of the primitive contract. Identities distinguish
objects for the lifetime of retained descriptors, including across rename. -/
structure WalInodeImage where
  active : Nat
  crashBindings : List Nat
  visible : Nat → ByteArray
  crashBytes : Nat → List ByteArray

namespace WalInodeImage

def project (image : WalInodeImage) (directory : DirectoryPublication.Image) : ReopenImage :=
  ⟨directory, ⟨some (image.visible image.active),
    image.crashBindings.flatMap fun inode => (image.crashBytes inode).map some, none⟩⟩

/-- The descriptor's captured identity is compared with the WAL binding
at the effect point. The caller must obtain both identities from the same
stable file-object namespace while the descriptor still refers to its inode. -/
def syncTarget (image : WalInodeImage) (target : Nat) : WalFileSyncTarget :=
  ⟨target, some (image.active, image.visible image.active)⟩

theorem syncTarget_targetsLiveWal_iff (image : WalInodeImage)
    (directory : DirectoryPublication.Image) (target : Nat) :
    (image.syncTarget target).TargetsLiveWal (image.project directory) ↔ target = image.active := by
  simp only [syncTarget, WalFileSyncTarget.TargetsLiveWal, project, Option.some.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨_, ⟨equal, _⟩, _⟩ => equal.symm, fun equal =>
    ⟨image.visible image.active, ⟨equal.symm, rfl⟩, rfl⟩⟩

/-- The new inode was separately written and synced before rename. The old
binding candidates may still survive until the directory barrier. -/
def renameSynced (image : WalInodeImage) (replacement : Nat) (bytes : ByteArray) : WalInodeImage :=
  ⟨replacement, replacement :: image.crashBindings,
    fun inode => if inode = replacement then bytes else image.visible inode,
    fun inode => if inode = replacement then [bytes] else image.crashBytes inode⟩

/-- The directory barrier settles the name. File durability requires its own
contract for each inode. -/
def settleBinding (image : WalInodeImage) : WalInodeImage :=
  { image with crashBindings := [image.active] }

/-- An outstanding descriptor refers to the original inode. Partial sync
reports can supply any remaining crash choices for that inode. A successful
file sync supplies exactly its current visible contents. -/
def reportFileSync (image : WalInodeImage) (target : Nat) (outcomes : List ByteArray) : WalInodeImage :=
  { image with crashBytes := fun inode => if inode = target then outcomes else image.crashBytes inode }

def completeFileSync (image : WalInodeImage) (target : Nat) : WalInodeImage :=
  image.reportFileSync target [image.visible target]

/-- The path model retains all earlier crash byte choices when it allows
the current inode's bytes to survive. Every concrete choice from a live
descriptor report is therefore admitted by the reopen attempt trace. -/
theorem reportLiveFileSync_crashAttempt (image : WalInodeImage)
    (directory : DirectoryPublication.Image) {initial : ReopenImage}
    (path : MarkedReopenAttempts initial (image.project directory))
    {target : Nat} (current : target = image.active) (outcomes : List ByteArray)
    (allowed : ∀ bytes ∈ outcomes, bytes = image.visible target ∨ bytes ∈ image.crashBytes target)
    {pair : DirectoryPublication.Bindings} (pairSurvives : pair ∈ directory.crashImages)
    {bytes : Option ByteArray}
    (walSurvives : bytes ∈ ((image.reportFileSync target outcomes).project directory).wal.crashImages) :
    MarkedReopenAttempts initial (.crash pair bytes) := by
  have live := (image.syncTarget_targetsLiveWal_iff directory target).mpr current
  refine .crash (.delayedWalFileSync path live) pairSurvives ?_
  obtain ⟨inode, binding, survived⟩ := List.mem_flatMap.mp walSurvives
  by_cases same : inode = target
  · subst inode
    have observed : bytes ∈ outcomes.map some := by simpa [reportFileSync] using survived
    obtain ⟨payload, chosen, rfl⟩ := List.mem_map.mp observed
    rcases allowed payload chosen with visible | prior
    · exact List.mem_cons.mpr (.inl (by simp [project, visible, current]))
    · exact List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨target, binding, List.mem_map_of_mem prior⟩)
  · have prior : bytes ∈ (image.crashBytes inode).map some := by
      simpa [reportFileSync, same] using survived
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨inode, binding, prior⟩)

/-- Before the directory barrier a fresh synced replacement refines the
rename cut of the existing path-based WAL repair. -/
theorem project_renameSynced (image : WalInodeImage) (directory : DirectoryPublication.Image)
    (replacement : Nat) (bytes : ByteArray) (fresh : replacement ∉ image.crashBindings) :
    (image.project directory).repairCut bytes 3 = some ((image.renameSynced replacement bytes).project directory) := by
  have priorBindings :
      image.crashBindings.flatMap (fun inode =>
        (if inode = replacement then [bytes] else image.crashBytes inode).map some) =
      image.crashBindings.flatMap (fun inode => (image.crashBytes inode).map some) := by
    generalize image.crashBindings = bindings at fresh ⊢
    induction bindings with
    | nil => rfl
    | cons inode rest ih =>
      simp only [List.mem_cons, not_or] at fresh
      simp [Ne.symm fresh.1, ih fresh.2]
  change some (⟨directory, ⟨some bytes,
      some bytes :: image.crashBindings.flatMap (fun inode => (image.crashBytes inode).map some),
      none⟩⟩ : ReopenImage) = _
  simp [project, renameSynced, priorBindings]

/-- A successful stale sync can make the old inode's visible bytes
survivable at the old binding before the directory settles. -/
theorem oldBinding_canSurvive (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {replacement : Nat} (bytes : ByteArray) (distinct : image.active ≠ replacement)
    (oldBindingPossible : image.active ∈ image.crashBindings) :
    some (image.visible image.active) ∈
      (((image.renameSynced replacement bytes).completeFileSync image.active).project directory).wal.crashImages := by
  apply List.mem_flatMap.mpr
  refine ⟨image.active, List.mem_cons_of_mem _ oldBindingPossible, ?_⟩
  simp [completeFileSync, reportFileSync, renameSynced, distinct]

/-- Before settlement, cover the stale report by allowing the old WAL's
visible bytes before the rename. This accounts for old bytes that were
visible to repair and are newly durable on the still-selectable old inode. -/
private def oldFileSyncCover (image : WalInodeImage) (directory : DirectoryPublication.Image)
    (bytes : ByteArray) : ReopenImage :=
  ⟨directory, ⟨some bytes, some bytes :: (image.project directory).allowVisibleWal.wal.crashImages, none⟩⟩

private theorem reportOldFileSync_crashSubset (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {replacement : Nat} (bytes : ByteArray)
    (distinct : image.active ≠ replacement) (fresh : replacement ∉ image.crashBindings)
    (oldOutcomes : List ByteArray)
    (allowed : ∀ contents ∈ oldOutcomes, contents = image.visible image.active ∨ contents ∈ image.crashBytes image.active) :
    (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).wal.crashImages
      ⊆ (image.oldFileSyncCover directory bytes).wal.crashImages := by
  intro contents survives
  obtain ⟨inode, binding, persisted⟩ := List.mem_flatMap.mp survives
  change inode ∈ replacement :: image.crashBindings at binding
  by_cases old : inode = image.active
  · subst inode
    have priorBinding : image.active ∈ image.crashBindings := (List.mem_cons.mp binding).resolve_left distinct
    have observed : contents ∈ oldOutcomes.map some := by
      simpa [reportFileSync, renameSynced] using persisted
    obtain ⟨payload, chosen, rfl⟩ := List.mem_map.mp observed
    rcases allowed payload chosen with rfl | prior
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨image.active, priorBinding, List.mem_map_of_mem prior⟩))
  · rcases List.mem_cons.mp binding with rfl | prior
    · simp [reportFileSync, renameSynced, old] at persisted
      simp [oldFileSyncCover, persisted]
    · have other : inode ≠ replacement := fun same => fresh (same ▸ prior)
      have oldContents : contents ∈ (image.crashBytes inode).map some := by
        simpa [reportFileSync, renameSynced, old, other] using persisted
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨inode, prior, oldContents⟩))

/-- Delaying a sync on the old inode adds at most its visible bytes to the
pre-rename survival choices, alongside the individually synced replacement. -/
theorem reportOldFileSync_crashImages_subset (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {replacement : Nat} (bytes : ByteArray)
    (distinct : image.active ≠ replacement) (fresh : replacement ∉ image.crashBindings)
    (oldOutcomes : List ByteArray)
    (allowed : ∀ contents ∈ oldOutcomes, contents = image.visible image.active ∨ contents ∈ image.crashBytes image.active) :
    (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).wal.crashImages
      ⊆ some bytes :: some (image.visible image.active) :: (image.project directory).wal.crashImages :=
  image.reportOldFileSync_crashSubset directory bytes distinct fresh oldOutcomes allowed

/-- A crash between rename and the directory barrier remains an admitted
retry. The cover comes from the pre-rename file sync allowance and the
authorized rename cut, while the physical effect occurs on the old inode. -/
theorem reportOldFileSync_crashRetry (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {initial : ReopenImage} (path : ReopenRetry initial (image.project directory))
    {replacement : Nat} {bytes : ByteArray} {length : UInt64}
    (repair : (image.project directory).RepairsTo length bytes)
    (distinct : image.active ≠ replacement) (fresh : replacement ∉ image.crashBindings)
    (oldOutcomes : List ByteArray)
    (allowed : ∀ contents ∈ oldOutcomes, contents = image.visible image.active ∨ contents ∈ image.crashBytes image.active)
    {pair : DirectoryPublication.Bindings} (pairSurvives : pair ∈ directory.crashImages)
    {contents : Option ByteArray}
    (walSurvives : contents ∈
      (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).wal.crashImages) :
    ReopenRetry initial (.crash pair contents) := by
  have covered :
      (image.project directory).allowVisibleWal.repairCut bytes 3 =
        some (image.oldFileSyncCover directory bytes) := rfl
  have widened : (image.project directory).allowVisibleWal.RepairsTo length bytes :=
    ⟨repair.visibleMarker, repair.selected, repair.coversCandidates⟩
  have repaired := ReopenRetry.repair (.allowVisibleWal path) widened covered
  exact .crash repaired pairSurvives
    (image.reportOldFileSync_crashSubset directory bytes distinct fresh oldOutcomes allowed walSurvives)

/-- Before the barrier, a report on the old descriptor can persist its
visible bytes or retain crash candidates still allowed by its initial file
state. Both possibilities refine the path model. The replacement uses the
existing repair proof. -/
theorem reportOldFileSync_valid (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {replacement : Nat} {bytes : ByteArray} {length : UInt64}
    {expected : DirectoryPublication.Bindings → ByteArray}
    (distinct : image.active ≠ replacement) (fresh : replacement ∉ image.crashBindings)
    (valid : (image.project directory).Valid expected)
    (repair : (image.project directory).RepairsTo length bytes)
    (oldOutcomes : List ByteArray)
    (allowed : ∀ contents ∈ oldOutcomes, contents = image.visible image.active ∨ contents ∈ image.crashBytes image.active) :
    (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).Valid expected := by
  have safeRepair : (image.project directory).allowVisibleWal.RepairsTo length bytes :=
    ⟨repair.visibleMarker, repair.selected, repair.coversCandidates⟩
  have cut : (image.project directory).allowVisibleWal.repairCut bytes 3 =
      some (image.oldFileSyncCover directory bytes) := rfl
  have safe := ReopenImage.repairCut_valid (ReopenImage.allowVisibleWal_valid valid) safeRepair 3 cut
  refine ⟨?_, ?_, fun contents survives => safe.crashValid contents
    (image.reportOldFileSync_crashSubset directory bytes distinct fresh oldOutcomes allowed survives)⟩
  · have newSurvives : some bytes ∈
        (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).wal.crashImages :=
      List.mem_flatMap.mpr ⟨replacement, List.mem_cons_self .., by
        simp [reportFileSync, renameSynced, Ne.symm distinct]⟩
    exact List.ne_nil_of_mem newSurvives
  · simpa [project, reportFileSync, renameSynced, oldFileSyncCover] using safe.activeValid

theorem completeOldFileSync_valid (image : WalInodeImage) (directory : DirectoryPublication.Image)
    {replacement : Nat} {bytes : ByteArray} {length : UInt64}
    {expected : DirectoryPublication.Bindings → ByteArray}
    (distinct : image.active ≠ replacement) (fresh : replacement ∉ image.crashBindings)
    (valid : (image.project directory).Valid expected)
    (repair : (image.project directory).RepairsTo length bytes) :
    (((image.renameSynced replacement bytes).completeFileSync image.active).project directory).Valid expected := by
  simpa [completeFileSync, renameSynced, distinct] using
    image.reportOldFileSync_valid directory distinct fresh valid repair [image.visible image.active]
      (by simp)

/-- Once the replacement binding is settled, any report for a distinct,
retained old descriptor is invisible in the WAL projection. This is the
exact post-repair image even if the old inode now has different crash bytes. -/
theorem reportOldFileSync_afterSettlement (image : WalInodeImage)
    (directory : DirectoryPublication.Image) {replacement : Nat} (bytes : ByteArray)
    (distinct : image.active ≠ replacement) (oldOutcomes : List ByteArray) :
    ((image.renameSynced replacement bytes).settleBinding.reportFileSync image.active oldOutcomes).project
      directory.syncDirectory = ⟨directory.syncDirectory, .settled (some bytes)⟩ := by
  simp [project, reportFileSync, settleBinding, renameSynced, Publication.Image.settled, Ne.symm distinct]

/-- A stale effect on a distinct inode preserves the same admitted endpoint
after the directory barrier. The identity check keeps it in the stale branch. -/
theorem reportOldFileSync_afterSettlement_attempt (image : WalInodeImage)
    (directory : DirectoryPublication.Image) {initial : ReopenImage}
    {replacement : Nat} (bytes : ByteArray) (distinct : image.active ≠ replacement)
    (oldOutcomes : List ByteArray)
    (path : MarkedReopenAttempts initial ⟨directory.syncDirectory, .settled (some bytes)⟩) :
    let current := (image.renameSynced replacement bytes).settleBinding
    ¬ (current.syncTarget image.active).TargetsLiveWal (current.project directory.syncDirectory) ∧
      MarkedReopenAttempts initial
        ((current.reportFileSync image.active oldOutcomes).project directory.syncDirectory) := by
  dsimp only
  constructor
  · simpa [syncTarget_targetsLiveWal_iff, settleBinding, renameSynced] using distinct
  · rwa [reportOldFileSync_afterSettlement image directory bytes distinct oldOutcomes]

end WalInodeImage

end Alvoki.WAL.Boundary
