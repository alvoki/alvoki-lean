import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented

open Model (Disk DataImage)

private def withName (id : Nat) (present : Bool) (names : List Nat) : List Nat :=
  let rest := names.filter (· != id)
  if present then id :: rest else rest

private theorem mem_withName {id other : Nat} (away : other ≠ id) (present : Bool) (names : List Nat) :
    other ∈ withName id present names ↔ other ∈ names := by
  cases present <;> simp [withName, away]

/-- Observe the live name, durable name and opaque child contents left by
an interrupted preparation or removal. The controls and other files stay fixed. -/
def Model.Disk.withArtifact (disk : Disk) (id : Nat) (image : DataImage) (live durable : Bool) : Disk :=
  { disk with
    liveNames := withName id live disk.liveNames
    durableNames := withName id durable disk.durableNames
    segment := fun other => if other = id then image else disk.segment other }

/-- An artifact can change arbitrarily once neither the visible nor the
durable authority selects its ID. Each recovery choice retains the same
history witness and permitted views. -/
theorem Recoverable.withUnselectedArtifact {known request disk id}
    (unselected : ∀ c, disk.liveControl = some c ∨ disk.durableControl = some c → ¬ c.selects id)
    (image : DataImage) (live durable : Bool) :
    Recoverable known request (disk.withArtifact id image live durable) ↔ Recoverable known request disk := by
  let changed := disk.withArtifact id image live durable
  have choices (c : Control) (authority : disk.liveControl = some c ∨ disk.durableControl = some c) :
      RecoveryChoice known request c changed ↔ RecoveryChoice known request c disk := by
    have away (i : Nat) (selected : c.selects i) : i ≠ id := by
      rintro rfl
      exact unselected c authority selected
    have names (i : Nat) (selected : c.selects i) :
        (i ∈ changed.liveNames ↔ i ∈ disk.liveNames) ∧
        (i ∈ changed.durableNames ↔ i ∈ disk.durableNames) :=
      ⟨mem_withName (away i selected) live _, mem_withName (away i selected) durable _⟩
    have contents (i : Nat) (selected : c.selects i) : changed.segment i = disk.segment i := by
      simp [changed, Disk.withArtifact, away i selected]
    constructor
    · intro chosen
      exact chosen.frame (fun i selected =>
        let ⟨visible, settled⟩ := names i selected
        let ⟨h, p, readable, _⟩ := chosen
        let ⟨seen, saved⟩ := readable.layout.names i selected
        ⟨visible.mp seen, settled.mp saved⟩) (fun i selected => (contents i selected).symm)
    · intro chosen
      exact chosen.frame (fun i selected =>
        let ⟨visible, settled⟩ := names i selected
        let ⟨h, p, readable, _⟩ := chosen
        let ⟨seen, saved⟩ := readable.layout.names i selected
        ⟨visible.mpr seen, settled.mpr saved⟩) contents
  constructor <;> intro prior <;>
    obtain ⟨⟨c, visible, liveChoice⟩, ⟨d, settled, durableChoice⟩⟩ := prior
  · exact ⟨⟨c, visible, (choices c (.inl visible)).mp liveChoice⟩,
      ⟨d, settled, (choices d (.inr settled)).mp durableChoice⟩⟩
  · exact ⟨⟨c, visible, (choices c (.inl visible)).mpr liveChoice⟩,
      ⟨d, settled, (choices d (.inr settled)).mpr durableChoice⟩⟩

end WalRecoverySlice.Segmented
