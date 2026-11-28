import Alvoki.Experiments.L0.Model
import Alvoki.Experiments.L0.ComponentContract

namespace ExperimentalL0.Model

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

def Image.selected (image : Image) : Selected :=
  ⟨image.view, image.version, image.tables⟩

theorem componentLaws (faults : Faults) : ComponentLaws (components faults) Image.selected where
  scan _ := ⟨rfl, rfl⟩
  reopenWal s := by cases h : faults.openWal <;> simp [components, h, Image.selected]
  reopenManifest s := by cases h : faults.openManifest <;> simp [components, h, Image.selected]
  append s batch := by
    cases h : faults.append <;>
      simp [components, h, effect, Image.append, Selected.append, Image.selected] <;> first | rfl | exact Or.inr rfl
  create s rows _ := by
    have bindings := table_create_refines s rows faults.create
    by_cases space : s.catalog.length < UInt64.size
    · cases h : faults.create <;>
        simp [components, tableOps, h, space, effect, Image.store, Image.selected] at bindings ⊢ <;>
        exact bindings
    · simp [components, tableOps, space, Image.selected, Catalog.Preserves]
  publish s version _ := by
    cases h : faults.publish <;>
      simp [components, h, effect, Image.select, Selected.publish, Image.selected] <;> first | rfl | exact Or.inr rfl
  check s id := by
    by_cases bound : id.toNat < s.catalog.length <;> simp [components, tableOps, bound]
  lookup s id key rows bound := by
    have read := table_read_refines s id key bound faults.create
    simp only [components, read]
    exact ⟨trivial, trivial⟩

end ExperimentalL0.Model
