import Alvoki.Storage.Disk.NativeLongKeeperRepairPrefix
import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.NativeRetainedOpenStorage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

def WalKeeperRenameEffect.ManagedPath (directory : DiskDirectory) (path : FilePath) : Prop :=
  path = directory.path ∨ ∃ file, path = directory.file file

def WalKeeperRenameEffect.rebind (directory : DiskDirectory) (first replacement : Nat)
    (names : FilePath → Option Nat) (path : FilePath) : Option Nat :=
  if path = directory.file (.walSegment first) then some replacement
  else if path = directory.file .stagedWal then none else names path

/-- Physical observations at a same-directory keeper rename, with or
without a reported effect. One old map supplies all managed bindings
of each survivor. The root's own binding is included in that map. -/
structure WalKeeperRenameEffect (directory : DiskDirectory) (first replacement : Nat)
    (effective : Bool) (before reached : CheckpointStorageObservation)
    (beforeBytes reachedBytes : Nat → ByteArray) : Prop where
  visible : ∀ path, WalKeeperRenameEffect.ManagedPath directory path → reached.files.names path =
    if effective then WalKeeperRenameEffect.rebind directory first replacement before.files.names path else before.files.names path
  survivors : ∀ names ∈ reached.crashNames, ∃ prior ∈ before.crashNames, ∃ moved : Bool,
    (moved = true → effective = true) ∧ ∀ path, WalKeeperRenameEffect.ManagedPath directory path →
      names path = if moved then WalKeeperRenameEffect.rebind directory first replacement prior path else prior path
  liveBytes : ∀ path, WalKeeperRenameEffect.ManagedPath directory path → ∀ inode,
    reached.files.names path = some inode → reachedBytes inode = beforeBytes inode
  durableBytes : ∀ names, names = reached.files.names ∨ names ∈ reached.crashNames →
    ∀ path, WalKeeperRenameEffect.ManagedPath directory path → ∀ inode,
      names path = some inode → reached.files.bytes inode = before.files.bytes inode

namespace WalKeeperRenameEffect

variable {directory : DiskDirectory} {first replacement old : Nat} {effective : Bool}
  {before reached : CheckpointStorageObservation} {beforeBytes reachedBytes : Nat → ByteArray}
  (effect : WalKeeperRenameEffect directory first replacement effective before reached beforeBytes reachedBytes)

private theorem selectedPath {state : NativeReadyState} {path : FilePath}
    (known : state.selectedRetryPath path) : WalKeeperRenameEffect.ManagedPath state.session.directory path :=
  NativeReadyState.crashPath_rootOrChild (NativeReadyState.crashPath_iff_write.mpr
    (known.imp_right Or.inr))

private theorem segmentNeScratch (directory : DiskDirectory) (start : Nat) :
    directory.file (.walSegment start) ≠ directory.file .stagedWal := by
  intro collision
  obtain ⟨_, impossible⟩ := directory.walSegment_exclusive collision.symm
  cases impossible

include effect

private theorem keepsName {path : FilePath} (known : WalKeeperRenameEffect.ManagedPath directory path)
    (notKeeper : path ≠ directory.file (.walSegment first)) (notStage : path ≠ directory.file .stagedWal) :
    reached.files.names path = before.files.names path := by
  simpa [WalKeeperRenameEffect.rebind, notKeeper, notStage] using effect.visible path known

/-- The same pre-rename crash map supplies every untouched binding. -/
theorem framesOffTarget {scope : FilePath → Prop}
    (managed : ∀ path, scope path → WalKeeperRenameEffect.ManagedPath directory path)
    (safe : ∀ path, scope path →
      path ≠ directory.file (.walSegment first) ∧ path ≠ directory.file .stagedWal) :
    before.Frames scope reached := by
  have binds {path} (known : scope path) := effect.keepsName (managed path known)
    (safe path known).1 (safe path known).2
  refine ⟨fun path known => ⟨binds known, fun inode named =>
    effect.durableBytes _ (.inl rfl) path (managed path known) inode ((binds known).trans named)⟩, ?_⟩
  intro names possible
  obtain ⟨prior, earlier, moved, _, map⟩ := effect.survivors names possible
  refine ⟨prior, earlier, fun path known => ?_⟩
  simpa [WalKeeperRenameEffect.rebind, (safe path known).1, (safe path known).2] using map path (managed path known)

theorem framesRetry {state : NativeReadyState} (sameDirectory : state.session.directory = directory)
    (safe : ∀ path, state.selectedRetryPath path →
      path ≠ directory.file (.walSegment first) ∧ path ≠ directory.file .stagedWal) :
    state.SelectedRetryFrame before reached beforeBytes reachedBytes := by
  have canonical {path} (known : state.selectedRetryPath path) : WalKeeperRenameEffect.ManagedPath directory path :=
    sameDirectory ▸ selectedPath known
  have durable := effect.framesOffTarget (fun _ known => canonical known) safe
  refine ⟨fun path known => ⟨(durable.visible path known).1, fun inode named => congrArg (fun bytes => [bytes])
    (effect.liveBytes path (canonical known) inode (((durable.visible path known).1).trans named))⟩,
    durable.visible, durable.weaken (fun _ same => .inr (.inl same))⟩

private theorem liveKeeper (named : before.files.names (directory.file (.walSegment first)) = some old) :
    reached.files.names (directory.file (.walSegment first)) = some (if effective then replacement else old) := by
  cases effective <;> simpa [WalKeeperRenameEffect.rebind, named] using
    effect.visible (directory.file (.walSegment first)) (.inr ⟨.walSegment first, rfl⟩)

theorem walNames (named : before.files.names (directory.file (.walSegment first)) = some old)
    (settled : ∀ names ∈ before.crashNames, names (directory.file (.walSegment first)) = some old)
    (lower upper : Nat) : WalNamePresenceFrame directory lower upper before reached := by
  have present {a b : Nat} (names : FilePath → Option Nat) (named : names (directory.file (.walSegment first)) = some a) :
      (if b = first then some replacement else names (directory.file (.walSegment b))).isSome =
        (names (directory.file (.walSegment b))).isSome := by
    by_cases same : b = first
    · subst b; simp [named]
    · simp [same]
  have preserves {names : FilePath → Option Nat} (named : names (directory.file (.walSegment first)) = some old)
      (applied : Bool) (start : Nat) :
      (if applied then WalKeeperRenameEffect.rebind directory first replacement names (directory.file (.walSegment start))
        else names (directory.file (.walSegment start))).isSome =
        (names (directory.file (.walSegment start))).isSome := by
    cases applied with
    | false => rfl
    | true =>
      have same : directory.file (.walSegment start) = directory.file (.walSegment first) ↔ start = first :=
        ⟨fun h => directory.walSegment_path_injective h, congrArg (fun n => directory.file (.walSegment n))⟩
      simpa [WalKeeperRenameEffect.rebind, segmentNeScratch directory start, same] using present names named (b := start)
  refine ⟨fun start _ _ => (congrArg Option.isSome
    (effect.visible _ (.inr ⟨.walSegment start, rfl⟩))).trans (preserves named effective start), ?_⟩
  intro names possible
  obtain ⟨prior, earlier, moved, _, map⟩ := effect.survivors names possible
  exact ⟨prior, .inr earlier, fun start _ _ => (congrArg Option.isSome
    (map _ (.inr ⟨.walSegment start, rfl⟩))).trans (preserves (settled prior earlier) moved start)⟩

/-- Each survivor chooses the replacement together with its exact
synced bytes, or the original inode together with its prior bytes. -/
theorem keeperSurvivors (settled : ∀ names ∈ before.crashNames,
    names (directory.file (.walSegment first)) = some old) {payload : ByteArray}
    (staged : before.files.bytes replacement = [payload]) :
    ∀ names ∈ reached.crashNames, ∃ moved : Bool, (moved = true → effective = true) ∧
      let selected := if moved then replacement else old
      names (directory.file (.walSegment first)) = some selected ∧
      (reached.files.bytes selected = if moved then [payload] else before.files.bytes old) ∧
      (moved = true → names (directory.file .stagedWal) = none) := by
  intro names possible
  obtain ⟨prior, earlier, moved, permits, map⟩ := effect.survivors names possible
  have kept := map (directory.file (.walSegment first)) (.inr ⟨.walSegment first, rfl⟩)
  have named : names (directory.file (.walSegment first)) = some (if moved then replacement else old) := by
    cases moved <;> simpa [WalKeeperRenameEffect.rebind, settled prior earlier] using kept
  refine ⟨moved, permits, named, ?_, ?_⟩
  · have bytes := effect.durableBytes names (.inr possible) _ (.inr ⟨.walSegment first, rfl⟩) _ named
    cases moved <;> simpa [staged] using bytes
  · intro applied
    have scratch := map (directory.file .stagedWal) (.inr ⟨.stagedWal, rfl⟩)
    simpa [applied, WalKeeperRenameEffect.rebind, Ne.symm (segmentNeScratch directory first)] using scratch

end WalKeeperRenameEffect

/-- The physical outcome of the failed rename determines the logical
repair prefix, keeper and retry frames before any final directory sync. -/
theorem failedLongKeeperRename {heap : Type} (view : OpenCloseHeapView heap FileImage)
    (state : NativeReadyState) (target : Target)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {entry pruned synced reached : heap} {effective : Bool} {old replacement : Nat}
    (prunedTrace : EffectTrace target (view.files entry).image (view.files pruned).image)
    (prunedEmpty : (view.files pruned).image.later.DurablyEmpty)
    (syncedImage : (view.files synced).image = (view.files pruned).image.withScratch (some (target.trimmed, true)))
    (prefixFrame : state.SelectedRetryFrame (storage entry) (storage synced) (visible entry) (visible synced))
    (safe : ∀ path, state.selectedRetryPath path → path ≠ state.session.directory.file (.walSegment target.first) ∧
      path ≠ state.session.directory.file .stagedWal)
    (oldNamed : (storage synced).files.names (state.session.directory.file (.walSegment target.first)) = some old)
    (oldSettled : ∀ names ∈ (storage synced).crashNames,
      names (state.session.directory.file (.walSegment target.first)) = some old)
    (stagedLive : visible synced replacement = target.trimmed)
    (stagedDurable : (storage synced).files.bytes replacement = [target.trimmed])
    (keeper : RawOpenRetryTrace.KeeperAt view state.session.directory target
      (fun atHeap => (storage atHeap).files.names) visible synced)
    (effect : WalKeeperRenameEffect state.session.directory target.first replacement effective
      (storage synced) (storage reached) (visible synced) (visible reached))
    (image : (if effective then (view.files synced).image.effect target (.replace .renameStaged)
      else some (view.files synced).image) = some (view.files reached).image) :
    EffectTrace target (view.files entry).image (view.files reached).image ∧
    state.SelectedRetryFrame (storage entry) (storage reached) (visible entry) (visible reached) ∧
    RawOpenRetryTrace.KeeperAt view state.session.directory target
      (fun atHeap => (storage atHeap).files.names) visible reached ∧
    (RawOpenRetryTrace.LaterWalAt view state.session.directory target
      (fun atHeap => (storage atHeap).files.names) synced →
      RawOpenRetryTrace.LaterWalAt view state.session.directory target
        (fun atHeap => (storage atHeap).files.names) reached) ∧
    (∀ lower upper, WalNamePresenceFrame state.session.directory lower upper (storage synced) (storage reached)) ∧
    (storage reached).files.names (state.session.directory.file (.walSegment target.first)) =
      some (if effective then replacement else old) ∧
    (∀ names ∈ (storage reached).crashNames, ∃ moved : Bool, (moved = true → effective = true) ∧
      let inode := if moved then replacement else old
      names (state.session.directory.file (.walSegment target.first)) = some inode ∧
      ((storage reached).files.bytes inode = if moved then [target.trimmed] else (storage synced).files.bytes old) ∧
      (moved = true → names (state.session.directory.file .stagedWal) = none)) ∧
    (view.files reached).image.later.DurablyEmpty := by
  let directory := state.session.directory
  let keeperPath := directory.file (.walSegment target.first)
  have named := effect.liveKeeper oldNamed
  have oldPayload : (view.files synced).image.keeper.active = some (visible synced old) := by
    simpa [RawOpenRetryTrace.KeeperAt, oldNamed] using keeper
  have visibleBytes := effect.liveBytes keeperPath (.inr ⟨.walSegment target.first, rfl⟩) _ named
  have imageAfter : (view.files reached).image =
      if effective then { (view.files pruned).image with keeper :=
        ⟨some target.trimmed, some target.trimmed :: (view.files pruned).image.keeper.crashImages, none⟩ }
      else (view.files synced).image := by
    cases effective with
    | false => exact (Option.some.inj image).symm
    | true =>
      rw [syncedImage] at image
      simp [FileImage.effect, FileImage.withScratch, Publication.Image.step] at image
      exact image.symm
  have keeperAt : RawOpenRetryTrace.KeeperAt view directory target
      (fun atHeap => (storage atHeap).files.names) visible reached := by
    change (view.files reached).image.keeper.active = ((storage reached).files.names keeperPath).map (visible reached)
    rw [named, Option.map_some, visibleBytes, imageAfter]
    cases effective with
    | false => exact oldPayload
    | true => exact congrArg some stagedLive.symm
  have trace : EffectTrace target (view.files entry).image (view.files reached).image := by
    rw [imageAfter, syncedImage]
    cases effective with
    | false => exact .replace prunedTrace prunedEmpty (cut := 2) rfl
    | true => exact .replace prunedTrace prunedEmpty (cut := 3) rfl
  have sameLater : (view.files reached).image.later.visible = (view.files synced).image.later.visible := by
    rw [imageAfter, syncedImage]
    cases effective <;> rfl
  have laterAt (later : RawOpenRetryTrace.LaterWalAt view directory target
      (fun atHeap => (storage atHeap).files.names) synced) :
      RawOpenRetryTrace.LaterWalAt view directory target (fun atHeap => (storage atHeap).files.names) reached := by
    apply later.frame sameLater
    intro start past
    apply effect.keepsName (.inr ⟨.walSegment start, rfl⟩)
    · exact fun collision => Nat.ne_of_gt (Nat.lt_of_le_of_lt target.firstCovered past)
        (directory.walSegment_path_injective collision)
    · exact WalKeeperRenameEffect.segmentNeScratch directory start
  have absent : (view.files reached).image.later.DurablyEmpty := by
    rw [imageAfter, syncedImage]
    cases effective <;> exact prunedEmpty
  exact ⟨trace, prefixFrame.trans (effect.framesRetry rfl safe), keeperAt, laterAt,
    fun lower upper => effect.walNames oldNamed oldSettled lower upper, named,
    effect.keeperSurvivors oldSettled stagedDurable, absent⟩

end Alvoki.Storage.DiskSession
