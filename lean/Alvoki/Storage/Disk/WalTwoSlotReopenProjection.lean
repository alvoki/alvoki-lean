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

end Alvoki.WAL.TwoSlot
