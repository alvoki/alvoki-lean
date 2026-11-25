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

/-- The successful marker-file barrier settles the marker independently of
the directory bindings. In particular an earlier manifest replacement
can still have either of its reported outcomes until a directory barrier. -/
def settleMarker (image : Image) (selected : Selection) : Image :=
  let publish := fun bindings : Bindings =>
    bindings.replace .walBoundary (Boundary.encode selected.frontier)
  { image with active := publish image.active, crashImages := image.crashImages.map publish }

theorem settleMarker_survivor_iff (image : Image) (selected : Selection) (survivor : Bindings) :
    survivor ∈ (settleMarker image selected).crashImages ↔
      survivor.walBoundary = some (Boundary.encode selected.frontier) ∧
      ∃ before ∈ image.crashImages, survivor.manifest = before.manifest := by
  simp only [settleMarker, List.mem_map]
  constructor
  · rintro ⟨before, present, rfl⟩
    exact ⟨rfl, before, present, rfl⟩
  · rintro ⟨wal, before, present, manifest⟩
    refine ⟨before, present, ?_⟩
    cases survivor
    simp_all [Bindings.replace]

/-- The shared directory barrier can further settle manifest selection
without changing the marker selected by the successful file barrier. -/
theorem settleMarker_syncDirectory (image : Image) (selected : Selection)
    {survivor : Bindings} (present : survivor ∈ (settleMarker image selected).syncDirectory.crashImages) :
    survivor.manifest = image.active.manifest ∧
      survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have chosen := (Image.survives_syncDirectory_iff (settleMarker image selected) survivor).mp present
  rw [chosen]
  exact ⟨rfl, rfl⟩

open Alvoki.Storage.WalSegmentRepair

/-- Once the positional marker is settled, each reached shared destructive
repair prefix preserves that exact logical marker, including admitted cuts
while replacing or pruning a keeper. -/
theorem repair_preserves_settledMarker (initial : FileImage) (selected : Selection)
    {target : Target} {after : FileImage}
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
  rfl

end Alvoki.WAL.TwoSlot
