import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.WalSegmentRepairEffects

namespace Alvoki.WAL.TwoSlot

open Alvoki.Storage.DirectoryPublication

/-- Express a successfully decoded physical marker in the logical format
consumed by the shared checkpoint and segmented WAL recovery. -/
def projectBinding (visible : Bindings) (bytes : ByteArray) : Except String Bindings :=
  (decode bytes).map fun selected =>
    visible.replace .walBoundary (Boundary.encode selected.frontier)

theorem projectBinding_decodes {visible : Bindings} {bytes : ByteArray} {selected : Selection}
    (accepted : decode bytes = .ok selected) :
    projectBinding visible bytes = .ok
      ⟨visible.manifest, some (Boundary.encode selected.frontier)⟩ := by
  simp [projectBinding, accepted, Except.map, Bindings.replace]

/-- Model a successful file barrier where every present marker binding
names the held file. Absent bindings can survive a pending bootstrap
rename. The barrier changes neither that choice nor the manifest binding. -/
def settleMarker (image : Image) (selected : Selection) : Image :=
  let publish := fun bindings : Bindings =>
    { bindings with walBoundary := bindings.walBoundary.map fun _ => Boundary.encode selected.frontier }
  { image with active := publish image.active, crashImages := image.crashImages.map publish }

theorem settleMarker_survivor_iff (image : Image) (selected : Selection) (survivor : Bindings) :
    survivor ∈ (settleMarker image selected).crashImages ↔
      ∃ before ∈ image.crashImages, survivor.manifest = before.manifest ∧
        survivor.walBoundary = before.walBoundary.map fun _ => Boundary.encode selected.frontier := by
  simp only [settleMarker, List.mem_map]
  constructor
  · rintro ⟨before, present, rfl⟩
    exact ⟨before, present, rfl, rfl⟩
  · rintro ⟨before, present, manifest, wal⟩
    refine ⟨before, present, ?_⟩
    cases survivor
    simp_all

/-- The shared directory barrier settles the visible manifest and marker
bindings once preparation has observed a present marker. -/
theorem settleMarker_syncDirectory (image : Image) (selected : Selection)
    {bytes : ByteArray} (bound : image.active.walBoundary = some bytes)
    {survivor : Bindings} (present : survivor ∈ (settleMarker image selected).syncDirectory.crashImages) :
    survivor.manifest = image.active.manifest ∧
      survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have chosen := (Image.survives_syncDirectory_iff (settleMarker image selected) survivor).mp present
  rw [chosen]
  simp [settleMarker, bound]

open Alvoki.Storage.WalSegmentRepair

/-- Once the positional marker is settled, each reached shared destructive
repair prefix preserves that exact logical marker, including admitted cuts
while replacing or pruning a keeper. -/
theorem repair_preserves_settledMarker (initial : FileImage) (selected : Selection)
    {target : Target} {after : FileImage} {bytes : ByteArray}
    (bound : initial.directory.active.walBoundary = some bytes)
    (trace : EffectTrace target
      { initial with directory := settleMarker initial.directory selected } after)
    (pair : (settleMarker initial.directory selected).active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts)
    (later : initial.later.Beyond target.range.through)
    {survivor : Bindings} (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have accepted := trace.valid pair keeper later
  have same : survivor = target.pair := by
    simpa [List.mem_cons, accepted.selected, accepted.settled] using chosen
  rw [same, ← pair]
  simp [settleMarker, bound]

/-- Physical image changes admitted after the first successful directory
barrier. A failed validation, lock handoff or other step without file effects
leaves the projected image unchanged. -/
inductive SettledRetries (target : Target) (initial : FileImage) : FileImage → Prop where
  | start : SettledRetries target initial initial
  | repair (prior : SettledRetries target initial before) (effects : EffectTrace target before after) :
      SettledRetries target initial after
  | crash (prior : SettledRetries target initial before)
      (metadata : pair ∈ before.directory.crashImages)
      (keeper : bytes ∈ before.keeper.crashImages) (later : names ∈ before.later.crashImages) :
      SettledRetries target initial (before.crash pair bytes names)

/-- An arbitrary number of admitted attempts preserves the exact selected
manifest and marker, sealed bytes and all required keeper data. -/
theorem SettledRetries.preserves {target : Target} {initial after : FileImage}
    (retries : SettledRetries target initial after) (valid : initial.Valid target) :
    after.Valid target ∧ after.kept = initial.kept := by
  induction retries with
  | start => exact ⟨valid, rfl⟩
  | repair _ effects ih =>
    exact ⟨effects.valid ih.1.selected ih.1.keeper ih.1.later, effects.keepsSealed.trans ih.2⟩
  | @crash before pair bytes names _ metadata keeper later ih =>
    have same := List.mem_singleton.mp (ih.1.settled ▸ metadata)
    exact ⟨⟨same, congrArg (fun pair => [pair]) same,
      Alvoki.Storage.Publication.Image.settled_valid (ih.1.keeper.crashValid _ keeper),
      (fun visible chosen => by
        have eq : visible = names := by simpa [FileImage.crash, LaterNames.settled] using chosen
        subst visible
        exact ih.1.later _ (List.mem_cons_of_mem _ later))⟩, ih.2⟩

/-- Compose the first authorized repair prefix with later attempts. Every
surviving binding still selects the same frontier, even if none of the
attempts has returned a ready writer. -/
theorem SettledRetries.preservesSelectedMarker
    (initial : FileImage) (selected : Selection)
    {target : Target} {first after : FileImage} {bytes : ByteArray}
    (bound : initial.directory.active.walBoundary = some bytes)
    (firstRepair : EffectTrace target
      { initial with directory := settleMarker initial.directory selected } first)
    (pair : (settleMarker initial.directory selected).active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts)
    (later : initial.later.Beyond target.range.through)
    (retries : SettledRetries target first after)
    {survivor : Bindings} (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.walBoundary = some (Boundary.encode selected.frontier) ∧
      after.kept = initial.kept := by
  have initialValid := firstRepair.valid pair keeper later
  have ⟨finalValid, sameSeals⟩ := retries.preserves initialValid
  have same : survivor = target.pair := by
    simpa [finalValid.selected, finalValid.settled] using chosen
  refine ⟨?_, sameSeals.trans firstRepair.keepsSealed⟩
  rw [same, ← pair]
  simp [settleMarker, bound]

end Alvoki.WAL.TwoSlot
