import Alvoki.Storage.Disk.Proofs.Collection.RunUnlinkSchedule

namespace Alvoki.Storage
open System CheckpointPublication

private theorem olderThanInstalledGeneration {current : Option UInt64}
    {installed generation : UInt64} (matching : current.getD 0 = installed)
    (older : generation < installed) : current ≠ some generation := by
  intro same
  have equal : generation = installed := by simpa [same] using matching
  exact (UInt64.lt_irrefl installed) (equal ▸ older)

/-- The age and hold policy depends on the decoded generation, independently
of the manifest format that recorded it. -/
theorem LockedRunInventory.selectOlderRunsAt_iff {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {installed generation : UInt64} {index : Nat}
    {current : Option UInt64} (held : List UInt64) (matching : current.getD 0 = installed) :
    (generation, index) ∈ selectRunFiles dir current (retainRunGeneration installed held)
      inventory.kindAt inventory.names ↔
    renderRunFileName generation index ∈ inventory.names ∧ generation < installed ∧
      generation ∉ held ∧ inventory.kindAt (dir.file (.run generation index)) = .ok .file := by
  rw [mem_selectRunFiles_iff]
  constructor
  · rintro ⟨listed, _, retained, regular⟩
    obtain ⟨older, unheld⟩ := retainRunGeneration_false_iff.mp retained
    exact ⟨listed, older, unheld, regular⟩
  · rintro ⟨listed, older, unheld, regular⟩
    exact ⟨listed, olderThanInstalledGeneration matching older,
      retainRunGeneration_false_iff.mpr ⟨older, unheld⟩, regular⟩

/-- A complete eligible inventory leaves every older unheld run durably
absent. The barrier also settles names already hidden by an earlier unlink. -/
theorem LockedRunInventory.finishOlderPass_absent {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) (before : RunUnlinkImage)
    {installed : UInt64} {current : Option UInt64} (held : List UInt64) (matching : current.getD 0 = installed)
    (complete : ∀ generation index bytes, before.visible generation index = some bytes →
      generation < installed → generation ∉ held →
      renderRunFileName generation index ∈ inventory.names ∧
        inventory.kindAt (dir.file (.run generation index)) = .ok .file) :
    ∀ generation index, generation < installed → generation ∉ held →
      (before.finishPass (selectRunFiles dir current (retainRunGeneration installed held)
        inventory.kindAt inventory.names)).DurablyAbsent (generation, index) := by
  intro generation index older unheld
  apply (before.finishPass_absent_iff _ (generation, index)).mpr
  cases visible : before.visible generation index with
  | none => exact .inr rfl
  | some bytes =>
    obtain ⟨listed, regular⟩ := complete generation index bytes visible older unheld
    exact .inl
      ((inventory.selectOlderRunsAt_iff held matching).mpr ⟨listed, older, unheld, regular⟩)

/-- The v1 model preflight supplies the matching generation. -/
theorem LockedRunInventory.selectOlderRuns_iff {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {installed generation : UInt64} {index : Nat}
    {manifest : Option ByteArray} {current : Option UInt64} (held : List UInt64)
    (checked : validateRunCollectionGeneration installed manifest = .ok current) :
    (generation, index) ∈ selectRunFiles dir current (retainRunGeneration installed held)
      inventory.kindAt inventory.names ↔
    renderRunFileName generation index ∈ inventory.names ∧ generation < installed ∧
      generation ∉ held ∧ inventory.kindAt (dir.file (.run generation index)) = .ok .file :=
  inventory.selectOlderRunsAt_iff held (validateRunCollectionGeneration_ok_iff.mp checked).2

/-- Interpret the collector after a successful read-only inventory, using
the same selector and unlink schedule as the native method. The namespace
contract fixes the resolved canonical parent and its regular bindings
while the writer owns the lock. Primitive reports describe unlink and
directory sync; the manifest and individually durable run payloads are
unchanged by those callbacks. The approved addresses can span retries. -/
theorem LockedRunInventory.runOlderCollection_outcome {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {before : RunUnlinkImage} {initial : RunFiles}
    {manifest : Publication.Image} {installed : UInt64} {current : Option UInt64} {approved : List RunAddress}
    (held : List UInt64)
    (settled : manifest.crashImages = [manifest.active])
    (checked : validateRunCollectionGeneration installed manifest.active = .ok current)
    (prior : RunUnlinkRetry approved (.settled initial) before)
    (olderUnheld : ∀ address ∈ approved, address.1 < installed ∧ address.1 ∉ held)
    (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit)
    (reports : RunUnlinkEffectContract perform)
    (coversSelected : ∀ address ∈ selectRunFiles dir current (retainRunGeneration installed held)
      inventory.kindAt inventory.names, address ∈ approved) :
    let selected := selectRunFiles dir current (retainRunGeneration installed held) inventory.kindAt inventory.names
    let run : EStateM IO.Error RunUnlinkImage Unit := do
      let addresses ← selectRunFilesWith dir current (retainRunGeneration installed held)
        (fun path => pure (inventory.kindAt path)) inventory.names
      RunCollection.run addresses perform
    match run before with
    | .ok _ after => after = before.finishPass selected ∧ RunUnlinkRetry approved (.settled initial) after ∧
        RunDeletion (fun generation => retainRunGeneration installed held generation = true)
          ⟨manifest, initial⟩ (after.project manifest)
    | .error _ after => RunUnlinkRetry approved (.settled initial) after ∧
        RunDeletion (fun generation => retainRunGeneration installed held generation = true)
          ⟨manifest, initial⟩ (after.project manifest) := by
  dsimp only
  rw [selectRunFilesWith_pure, pure_bind]
  generalize choice : selectRunFiles dir current (retainRunGeneration installed held)
    inventory.kindAt inventory.names = selected at coversSelected ⊢
  have eligible : ∀ address ∈ approved, (⟨manifest, initial⟩ : Image).Collectable
      (fun generation => retainRunGeneration installed held generation = true) address.1 := by
    intro address member
    have observed := (validateRunCollectionGeneration_ok_iff.mp checked).1
    obtain ⟨older, unheld⟩ := olderUnheld address member
    apply ((⟨manifest, initial⟩ : Image).collectable_iff_generation settled observed).mpr
    exact ⟨olderThanInstalledGeneration (validateRunCollectionGeneration_ok_iff.mp checked).2 older,
      by simp [retainRunGeneration_false_iff.mpr ⟨older, unheld⟩]⟩
  have outcome := runUnlinkSchedule_outcome selected before perform reports
  have retries := prior.runSchedule selected coversSelected perform reports
  cases execution : RunCollection.run selected perform before with
  | ok _ after =>
    rw [execution] at outcome retries
    exact ⟨outcome, retries, retries.projectsDeletion manifest _ eligible⟩
  | error _ after =>
    rw [execution] at retries
    exact ⟨retries, retries.projectsDeletion manifest _ eligible⟩

end Alvoki.Storage
