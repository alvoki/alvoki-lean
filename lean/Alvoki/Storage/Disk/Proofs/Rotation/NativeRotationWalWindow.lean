import Alvoki.Storage.Disk.Proofs.Rotation.NativeOpenRotation
import Alvoki.Storage.Disk.NativeRawUncertainWrite
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointSourceCrash

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

/-- Rotation can change one canonical WAL binding. Each other name in
the window keeps its presence, including names absent before rotation. -/
abbrev RotationWalNameFrame (directory : DiskDirectory) (first through successor : Nat)
    (before after : CheckpointStorageObservation) : Prop :=
  ∀ start, first ≤ start → start ≤ through → start ≠ successor →
    WalNamePresenceFrame directory start start before after

/-- On a single observed directory map, rotation adds the successor to the
WAL catalog while preserving presence and absence at every other offset. -/
theorem _root_.Alvoki.Storage.WalSegmentImage.namespaceWindowAfterRotation
    {old next : WalSegmentImage} {directory : DiskDirectory} {first through successor : Nat}
    {names : FilePath → Option Nat}
    (starts : next.segments.map WalSegment.first = old.segments.map WalSegment.first ++ [successor])
    (installed : (names (directory.file (.walSegment successor))).isSome = true)
    (other : ∀ start, first ≤ start → start ≤ through → start ≠ successor →
      ((names (directory.file (.walSegment start))).isSome = true ↔ start ∈ old.segments.map WalSegment.first)) :
    next.NamespaceWindow directory first through names := by
  intro start low high
  rw [starts, List.mem_append, List.mem_singleton]
  by_cases same : start = successor
  · subst start
    simp only [installed, or_true]
  · simpa only [same, or_false] using other start low high same

/-- Extend the catalog at a settled successor. The old catalog makes
no claim about that one name, which may already have existed. -/
theorem _root_.Alvoki.Storage.WalSegmentImage.settlesRotatedNamespace
    {old next : WalSegmentImage} {directory : DiskDirectory}
    {first through successor : Nat} {before after : CheckpointStorageObservation}
    (starts : next.segments.map WalSegment.first = old.segments.map WalSegment.first ++ [successor])
    (initial : ∀ start, first ≤ start → start ≤ through → start ≠ successor →
      old.SettledNamespaceWindow directory start start before)
    (kept : RotationWalNameFrame directory first through successor before after)
    (live : (after.files.names (directory.file (.walSegment successor))).isSome = true)
    (survives : ∀ names ∈ after.crashNames, (names (directory.file (.walSegment successor))).isSome = true) :
    next.SettledNamespaceWindow directory first through after := by
  have off (start : Nat) (low : first ≤ start) (high : start ≤ through) (apart : start ≠ successor) :=
    (kept start low high apart).preservesNamespaceWindow (initial start low high apart)
  exact ⟨WalSegmentImage.namespaceWindowAfterRotation starts live (fun start low high apart => (off start low high apart).1 start (Nat.le_refl _) (Nat.le_refl _)),
    fun names chosen => WalSegmentImage.namespaceWindowAfterRotation starts (survives names chosen) (fun start low high apart =>
      (off start low high apart).2 names chosen start (Nat.le_refl _) (Nat.le_refl _))⟩

/-- Project the live and durable presence of the active name from ready storage. -/
theorem NativeReadyStorage.activeWalPresent {state : NativeReadyState} {storage : CheckpointStorageObservation}
    (physical : NativeReadyStorage state storage) :
    let path := state.session.directory.file (.walSegment state.writer.wal.active.first)
    (storage.files.names path).isSome = true ∧ ∀ names ∈ storage.crashNames, (names path).isSome = true := by
  intro path
  obtain ⟨inode, named, _⟩ := physical.keeper
  have bound : storage.files.names path = some inode := named
  refine ⟨by simp only [bound, Option.isSome_some], ?_⟩
  intro names chosen
  rw [physical.settled names chosen path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))]
  simp only [bound, Option.isSome_some]

section Opened

variable {heap : Type} {opened : NativeOpenedHandle heap} {current position : NativeOpenedPosition opened}

local notation "nextState" => position.current.ready.state
local notation "wal" => current.current.ready.state.writer.wal
local notation "directory" => current.current.ready.state.session.directory

/-- Follow the reached rotation callbacks through the final ready
setter. The name frame excludes only the successor; its durable binding
comes from the same ready-storage proof as the next write's entry. -/
theorem OpenRotationObservation.Reached.walWindow
    {read create sync entry settled reset} {seen : OpenRotationObservation current read create sync entry settled reset}
    {lookup} (reached : seen.Reached lookup position)
    {next : NativeReadPosition current.current.history current.current.submissions}
    (samePosition : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    (rotation : NativeRotationFrame current.current.ready next)
    (storage : heap → CheckpointStorageObservation) {first through : Nat}
    (covers : ∀ offset ∈ (wal).segments.map WalSegment.first, first ≤ offset)
    (initial : ∀ start, first ≤ start → start ≤ through → start ≠ (wal).active.last →
      (wal).SettledNamespaceWindow directory start start (storage current.reached))
    (effects : seen.LocalFrames (fun before after =>
      RotationWalNameFrame directory first through (wal).active.last (storage before) (storage after)))
    (successor :
      let path := (nextState).session.directory.file (.walSegment (nextState).writer.wal.active.first)
      ((storage position.reached).files.names path).isSome = true ∧
        ∀ names ∈ (storage position.reached).crashNames, (names path).isSome = true) :
    position.WalWindowAt storage first through := by
  let frame := fun before after => RotationWalNameFrame directory first through (wal).active.last
    (storage before) (storage after)
  have trans {before middle reached : heap} (earlier : frame before middle) (later : frame middle reached) :
      frame before reached :=
    fun start low high apart => (earlier start low high apart).trans (later start low high apart)
  have kept := reached.frames (frame := frame) trans effects
  have priorFacts := current.current.ready.readPrefix.refines
  have onEnd : (wal).active.last = current.current.history.length :=
    priorFacts.1.retained.layout.activeEnd.trans (congrArg List.length priorFacts.2.1)
  have sealed : (nextState).writer.wal.sealed = (wal).sealed ++ [(wal).active] := by
    rw [samePosition]
    exact rotation.sealed
  have active : (nextState).writer.wal.active = ⟨(wal).active.last, (wal).active.last, ByteArray.empty⟩ := by
    rw [onEnd, samePosition]
    exact rotation.keeper
  have starts : (nextState).writer.wal.segments.map WalSegment.first =
      (wal).segments.map WalSegment.first ++ [(wal).active.last] := by
    simp only [WalSegmentImage.segments, sealed, active, List.map_append, List.map_cons, List.map_nil]
  have activeBefore : (wal).active ∈ (wal).segments := by simp [WalSegmentImage.segments]
  have lower : first ≤ (wal).active.last := Nat.le_trans
    (covers _ (List.mem_map.mpr ⟨_, activeBefore, rfl⟩)) (priorFacts.1.retained.layout.forward _ activeBefore)
  have sameDirectory : (nextState).session.directory = directory := position.directory.trans current.directory.symm
  have newFirst : (nextState).writer.wal.active.first = (wal).active.last := congrArg WalSegment.first active
  refine ⟨?_, ?_⟩
  · intro offset belongs
    rw [starts, List.mem_append, List.mem_singleton] at belongs
    exact belongs.elim (covers offset) (fun yes => yes ▸ lower)
  · rw [sameDirectory]
    apply WalSegmentImage.settlesRotatedNamespace starts initial kept
    · simpa only [sameDirectory, newFirst] using successor.1
    · simpa only [sameDirectory, newFirst] using successor.2

end Opened

end Alvoki.Storage.DiskSession
