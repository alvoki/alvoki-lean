import Alvoki.Experiments.L0.ManifestComposition

namespace ExperimentalL0.ManifestComposition

open DurableBlob L0Manifest
open WalRecoverySlice.Segmented

/-- The manifest part of the recovery state keeps the complete reached
image together with the L0 projections of the other two namespaces. -/
structure StateWithImage where
  selected : Selected
  image : Image
  valid : selected.version.Valid
  encoded : image.active = L0Manifest.encode selected.version

noncomputable def StateWithImage.install (s : StateWithImage) (image : Image) : StateWithImage := by
  classical
  exact
    if h : ∃ v, Version.Valid v ∧ image.active = L0Manifest.encode v then
      ⟨s.selected.publish (Classical.choose h), image, (Classical.choose_spec h).1,
        (Classical.choose_spec h).2⟩
    else s

noncomputable def StateWithImage.interpretation (dir : System.FilePath)
    (openReports : StateWithImage → LinuxEffects.Reports)
    (publishReports : StateWithImage → Version → LinuxEffects.Reports) :
    Interpretation
      (callbacks dir StateWithImage.image StateWithImage.install openReports publishReports)
      StateWithImage.selected where
  directory := dir
  image := StateWithImage.image
  install := StateWithImage.install
  openReports := openReports
  publishReports := publishReports
  schedule := rfl
  projection s := ⟨s.valid, s.encoded⟩
  imageInstalled s image admitted := by simp [StateWithImage.install, admitted]
  walFrame s image := by
    unfold StateWithImage.install
    split <;> rfl
  tableFrame s image := by
    unfold StateWithImage.install
    split <;> rfl

/-- Process exit keeps the reached image. At power loss the filesystem
selects one of its survivors. The caller retains the already durable table
catalog and settled WAL view across this boundary. -/
theorem restartAdmits {reached restarted : Image}
    (admitted : reached.Admits old pending)
    (restart : restarted = reached ∨
      ∃ survivor ∈ reached.survivors, restarted = .settled survivor) :
    restarted.Admits old pending := by
  rcases restart with rfl | ⟨survivor, survived, rfl⟩
  · exact admitted
  · have allowed := admitted.2 survivor survived
    simpa [Image.Admits, Image.settled] using allowed

/-- Both possible manifests reference the same retained WAL and catalog.
An uncertain publication, restart, and failed open preserve those choices.
The first successful open settles the selected image. -/
theorem recoverPublication (dir : System.FilePath)
    (publication failed opened : LinuxEffects.Reports)
    (view : Contract.View) (tables : Catalog) (history : Rows)
    (oldDurable : Durable ⟨view, old, tables⟩ history)
    (newDurable : Durable ⟨view, proposal, tables⟩ history)
    (stable : before.Stable (L0Manifest.encode old))
    (restart :
      let reached := match (LinuxEffects.backend dir publication).publish
          (L0Manifest.encode proposal) before with
        | .ok _ image | .error _ image => image
      restarted = reached ∨ ∃ survivor ∈ reached.survivors, restarted = .settled survivor)
    (failure : (LinuxEffects.backend dir failed).reopen restarted = .error () afterFailure)
    (success : (LinuxEffects.backend dir opened).reopen afterFailure = .ok bytes settled) :
    ∃ version, (backend dir opened).reopen afterFailure = .ok version settled ∧
      settled.Stable (L0Manifest.encode version) ∧
      Nonempty (Durable ⟨view, version, tables⟩ history) ∧
      RecoveryChoices.Retry (.online view) (.offline old (some proposal))
        (.online view) (.ready version) := by
  have reached := (LinuxEffects.publishUncertainAdmits dir publication stable
    (L0Manifest.encode proposal)).2
  have admitted := (LinuxEffects.reopenFailedAdmits dir failed
    (restartAdmits reached restart) failure).2
  obtain ⟨version, returned, pinned, allowed⟩ :=
    reopen dir opened (pending := some proposal) admitted oldDurable.unique
      (by simpa using newDurable.unique) success
  have durable : Nonempty (Durable ⟨view, version, tables⟩ history) := by
    rcases allowed with rfl | next
    · exact ⟨oldDurable⟩
    · cases Option.some.inj next
      exact ⟨newDurable⟩
  exact ⟨version, returned, pinned, durable, .manifest (.manifest .initial .openFailed trivial)
    (.opened allowed) trivial⟩

/-- After a successful recovery, any subsequent successful reopen across a
process stop or a power loss returns the same manifest. -/
theorem reopenAfterRestart (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (stable : settled.Stable (L0Manifest.encode version)) (valid : version.Valid)
    (restart : restarted = settled ∨
      ∃ survivor ∈ settled.survivors, restarted = .settled survivor)
    (returned : (LinuxEffects.backend dir reports).reopen restarted = .ok bytes after) :
    (backend dir reports).reopen restarted = .ok version after ∧
      after.Stable (L0Manifest.encode version) := by
  have admitted : settled.Admits (L0Manifest.encode version) none := by
    simp [Image.Admits, Permitted, stable.1, stable.2]
  obtain ⟨chosen, opened, pinned, allowed⟩ :=
    reopen dir reports (pending := none) (restartAdmits admitted restart) valid (by simp) returned
  have same : chosen = version := by simpa [Permitted] using allowed
  exact same ▸ ⟨opened, pinned⟩

end ExperimentalL0.ManifestComposition
