import Alvoki.Storage.Disk.Proofs.Keeper.SegmentedKeeperDescriptor

namespace Alvoki.Storage.WalSegmentRepair

open WAL.Boundary

/-- Before the old keeper disappears as a crash choice, a completed sync
on its retained descriptor may make its checked visible contents durable. -/
def FileImage.allowVisibleKeeper (image : FileImage) : FileImage :=
  { image with keeper := { image.keeper with crashImages := image.keeper.active :: image.keeper.crashImages } }

theorem Prepared.allowVisibleKeeper {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) : Prepared image.allowVisibleKeeper target plan := by
  refine ⟨prepared.pair, ⟨by simp [FileImage.allowVisibleKeeper], prepared.keeperPrefix.activeValid, ?_⟩, prepared.newer,
    prepared.through, prepared.start, prepared.names, prepared.keeperRead⟩
  intro bytes chosen
  rcases List.mem_cons.mp chosen with equal | prior
  · exact equal.symm ▸ prepared.keeperPrefix.activeValid
  · exact prepared.keeperPrefix.crashValid bytes prior

/-- The physical and modeled namespaces have the same live binding,
staged file, sealed contents, and metadata. The model may admit more
crash bytes for the keeper. -/
structure FileImage.KeeperCrashCover (actual modeled : FileImage) : Prop where
  directory : actual.directory = modeled.directory
  kept : actual.kept = modeled.kept
  active : actual.keeper.active = modeled.keeper.active
  staged : actual.keeper.staged = modeled.keeper.staged
  later : actual.later = modeled.later
  crashBytes : actual.keeper.crashImages ⊆ modeled.keeper.crashImages

theorem FileImage.KeeperCrashCover.crash {actual modeled initial : FileImage} {target : Target}
    (cover : actual.KeeperCrashCover modeled) (trace : EffectTrace target initial modeled)
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {names : List Nat}
    (metadata : pair ∈ actual.directory.crashImages) (keeper : bytes ∈ actual.keeper.crashImages)
    (later : names ∈ actual.later.crashImages) :
    EffectTrace target initial (actual.crash pair bytes names) := by
  have reduced := EffectTrace.crash trace (cover.directory ▸ metadata) (cover.crashBytes keeper) (cover.later ▸ later)
  simpa only [FileImage.crash, cover.kept] using reduced

/-- The exact crashed image continues the selected repair lineage from the
source with widened keeper durability. -/
theorem FileImage.KeeperCrashCover.crashLineage {actual modeled source : FileImage}
    {admits : Target → Prop} {target : Target} {plan : Plan}
    (cover : actual.KeeperCrashCover modeled) (trace : EffectTrace target source modeled)
    (admitted : admits target) (prepared : Prepared source target plan)
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {names : List Nat}
    (metadata : pair ∈ actual.directory.crashImages) (keeper : bytes ∈ actual.keeper.crashImages)
    (later : names ∈ actual.later.crashImages) :
    ReopenLineage source admits (actual.crash pair bytes names) :=
  .repairing .live admitted prepared (cover.crash trace metadata keeper later)

/-- A successful delayed sync can make the old object's visible bytes
survive while its binding is still an admitted crash choice. -/
theorem DelayedKeeperSync.oldContentsCanSurvive (report : DelayedKeeperSync)
    (previous : WalInodeImage) (replacement : Nat) (replacementBytes : ByteArray) (before : FileImage)
    (oldTarget : report.captured.inode = previous.active) (distinct : previous.active ≠ replacement)
    (oldBinding : previous.active ∈ previous.crashBindings)
    (synced : report.outcomes = [previous.visible previous.active]) :
    let current := previous.renameSynced replacement replacementBytes
    let actual := (before.withScratch none).withKeeperInodes (report.effect current)
    some (previous.visible previous.active) ∈ actual.keeper.crashImages := by
  change some (previous.visible previous.active) ∈
    ((report.effect (previous.renameSynced replacement replacementBytes)).project before.directory).wal.crashImages
  rw [DelayedKeeperSync.effect, report.sameTarget, oldTarget, synced]
  simpa [WalInodeImage.completeFileSync, WalInodeImage.renameSynced, distinct] using
    previous.oldBinding_canSurvive before.directory replacementBytes distinct oldBinding

/-- A replacement's file sync and rename have taken effect, and the
replacement-name barrier has yet to settle it. The earlier metadata/name
barrier and the original checked keeper bytes establish a valid cover for
an observed sync on the old object. The old sync may report its visible
bytes or a prior durability choice. The actual next bounded read can still
prepare exactly the same target. -/
theorem DelayedKeeperSync.coversUnsettledReplacement (report : DelayedKeeperSync)
    (previous : WalInodeImage) (replacement : Nat) {before : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared before target plan)
    (metadataSettled : before.directory.crashImages = [before.directory.active])
    (pruned : before.later.DurablyEmpty)
    (projected : before.withKeeperInodes previous = before)
    (oldTarget : report.captured.inode = previous.active) (distinct : previous.active ≠ replacement)
    (fresh : replacement ∉ previous.crashBindings)
    (allowed : ∀ bytes ∈ report.outcomes, bytes = previous.visible previous.active ∨
      bytes ∈ previous.crashBytes previous.active) :
    let source := before.allowVisibleKeeper
    let current := previous.renameSynced replacement target.trimmed
    let actual := (before.withScratch none).withKeeperInodes (report.effect current)
    ∃ cover, Prepared source target plan ∧ EffectTrace target source cover ∧ actual.KeeperCrashCover cover ∧
      ∃ retryPlan, Prepared actual target retryPlan := by
  intro source current actual
  let cover := { source.syncDirectory with keeper :=
    ⟨some target.trimmed, some target.trimmed :: source.keeper.crashImages, none⟩ }
  have coverPrepared := prepared.allowVisibleKeeper
  have noLater : source.syncDirectory.later.DurablyEmpty :=
    ⟨pruned.1, congrArg (fun names => [names]) pruned.1⟩
  have trace : EffectTrace target source cover :=
    .replace .authorized noLater (cut := 3) rfl
  have effectInode : report.effectTarget.inode = previous.active := by
    rw [report.sameTarget, oldTarget]
  have oldVisible : some (previous.visible previous.active) = before.keeper.active :=
    congrArg (fun files : FileImage => files.keeper.active) projected
  have oldChoices : (previous.project before.directory).wal.crashImages = before.keeper.crashImages :=
    congrArg (fun files : FileImage => files.keeper.crashImages) projected
  have subset := previous.reportOldFileSync_crashImages_subset before.directory target.trimmed distinct fresh
    report.outcomes allowed
  rw [oldVisible, oldChoices] at subset
  have actualSubset : actual.keeper.crashImages ⊆ cover.keeper.crashImages := by
    change ((report.effect current).project before.directory).wal.crashImages ⊆ _
    rw [DelayedKeeperSync.effect, effectInode]
    exact subset
  have sameDirectory : actual.directory = cover.directory := by
    change before.directory = before.directory.syncDirectory
    unfold DirectoryPublication.Image.syncDirectory
    rw [← metadataSettled]
  have sameLater : actual.later = cover.later := by
    have settled : before.later.crashImages = [before.later.visible] :=
      pruned.2.trans (congrArg (fun names => [names]) pruned.1).symm
    change before.later = before.later.syncDirectory
    unfold LaterNames.syncDirectory LaterNames.settled
    rw [← settled]
  have active : actual.keeper.active = some target.trimmed := by
    simp [actual, current, FileImage.withKeeperInodes, DelayedKeeperSync.effect, WalInodeImage.project,
      WalInodeImage.reportFileSync, WalInodeImage.renameSynced]
  have covers : actual.KeeperCrashCover cover := ⟨sameDirectory, rfl, active, rfl, sameLater, actualSubset⟩
  have keeperSurvives : some target.trimmed ∈ actual.keeper.crashImages := by
    change some target.trimmed ∈ ((report.effect current).project before.directory).wal.crashImages
    rw [DelayedKeeperSync.effect, effectInode]
    apply List.mem_flatMap.mpr
    refine ⟨replacement, List.mem_cons_self .., ?_⟩
    simp [current, WalInodeImage.renameSynced, WalInodeImage.reportFileSync, distinct.symm]
  have valid := trace.valid coverPrepared.pair coverPrepared.keeperPrefix coverPrepared.newer
  have actualKeeper : actual.keeper.Valid target.Accepts :=
    ⟨List.ne_nil_of_mem keeperSurvives, covers.active ▸ valid.keeper.activeValid,
      fun bytes chosen => valid.keeper.crashValid bytes (covers.crashBytes chosen)⟩
  exact ⟨cover, coverPrepared, trace, covers, ⟨target.range.through, target.first, actual.later.visible, target.trimmed⟩,
    ⟨covers.directory ▸ valid.selected, actualKeeper, covers.later ▸ valid.later, rfl, rfl, rfl, active⟩⟩

end Alvoki.Storage.WalSegmentRepair
