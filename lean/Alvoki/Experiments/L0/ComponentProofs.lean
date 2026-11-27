import Alvoki.Experiments.L0.Model

namespace ExperimentalL0.Model
open WalRecoverySlice.Segmented

def Image.tables (image : Image) : Catalog := fun id => image.catalog[id.toNat]?

theorem Image.store_preserves (image : Image) (rows : Rows) :
    image.tables.Preserves (image.store rows).tables := by
  intro id existing binds
  have inside := (List.getElem?_eq_some_iff.mp binds).choose
  simpa [Image.tables, Image.store, List.getElem?_append_left inside] using binds

/-- The interpreter allocates a fresh durable binding and frames every old
binding. The native adapter must supply this same guarantee across reboot. -/
theorem table_create_refines (image : Image) (rows : Rows) (outcome : Outcome) :
    match (tableOps outcome).create rows image with
    | .ok id after => image.tables.Created after.tables id rows
    | .error _ after => image.tables.Preserves after.tables := by
  by_cases space : image.catalog.length < UInt64.size
  · have index := UInt64.toNat_ofNat_of_lt' space
    cases outcome <;> simp [tableOps, space, effect]
    · refine ⟨?_, ?_, image.store_preserves rows⟩
      · simp [Image.tables, index]
      · simp [Image.tables, Image.store, index]
    · exact fun _ _ h => h
    · exact image.store_preserves rows
  · simp [tableOps, space, Catalog.Preserves]

theorem table_read_refines (image : Image) (id key : UInt64)
    (bound : image.tables id = some rows) (outcome : Outcome) :
    (tableOps outcome).lookup id key image = .ok (lookupRows rows key) image := by
  simp [tableOps, Image.tables] at bound ⊢
  rw [bound]

/-- The byte WAL changes by exactly the public append request or leaves its
prior view available on an uncertain outcome. -/
theorem append_choice (image : Image) (faults : Faults) (batch : Contract.Batch) :
    match (components faults).append batch image with
    | .ok _ after => (Contract.Request.append batch).apply image.view = some after.view
    | .error _ after => after.view = image.view ∨
        (Contract.Request.append batch).apply image.view = some after.view := by
  cases h : faults.append <;> simp [components, h, effect, Image.append, Contract.Request.apply]

/-- Only the manifest commit changes the selected version. Its failure has
precisely the old-or-proposed choice allowed by the typed manifest contract. -/
theorem publish_choice (image : Image) (faults : Faults) (proposal : L0Manifest.Version) :
    match (components faults).manifest.publish proposal image with
    | .ok _ after => after.version = proposal
    | .error _ after => DurableBlob.Permitted image.version (some proposal) after.version := by
  cases h : faults.publish <;> simp [components, h, effect, Image.select, DurableBlob.Permitted]

end ExperimentalL0.Model
