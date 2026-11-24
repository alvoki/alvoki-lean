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
  let widened := (image.project directory).allowVisibleWal
  let repaired : ReopenImage :=
    ⟨directory, ⟨some bytes, some bytes :: widened.wal.crashImages, none⟩⟩
  have safeRepair : widened.RepairsTo length bytes :=
    ⟨repair.visibleMarker, repair.selected, repair.coversCandidates⟩
  have cut : widened.repairCut bytes 3 = some repaired := rfl
  have safe := ReopenImage.repairCut_valid (ReopenImage.allowVisibleWal_valid valid) safeRepair 3 cut
  refine ⟨?_, ?_, ?_⟩
  · have newSurvives : some bytes ∈
        (((image.renameSynced replacement bytes).reportFileSync image.active oldOutcomes).project directory).wal.crashImages :=
      List.mem_flatMap.mpr ⟨replacement, List.mem_cons_self .., by
        simp [reportFileSync, renameSynced, Ne.symm distinct]⟩
    exact List.ne_nil_of_mem newSurvives
  · simpa [project, reportFileSync, renameSynced, repaired] using safe.activeValid
  · intro contents survives
    apply safe.crashValid
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
        simp [repaired, persisted]
      · have other : inode ≠ replacement := fun same => fresh (same ▸ prior)
        have oldContents : contents ∈ (image.crashBytes inode).map some := by
          simpa [reportFileSync, renameSynced, old, other] using persisted
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨inode, prior, oldContents⟩))

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

end WalInodeImage

end Alvoki.WAL.Boundary
