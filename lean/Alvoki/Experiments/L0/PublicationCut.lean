import Alvoki.Experiments.L0.ManifestRecovery
import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0.PublicationCut
open DurableBlob L0Manifest ManifestComposition

private def healthy : LinuxEffects.Reports := ⟨true, true, .ok, true, true, true, .ok, .ok⟩
private def renameError := { healthy with rename := Report.afterEffect }
private def readError := { healthy with readActive := false }

/-- A real cut in the interpreted Linux adapter. The rename happened and
reported an error before the parent barrier. Both images can survive. -/
theorem renameCut (dir : System.FilePath) (old proposal : Version) (valid : proposal.Valid) :
    (ManifestComposition.backend dir renameError).publish proposal (.settled (L0Manifest.encode old)) =
      .error () ⟨L0Manifest.encode proposal, [L0Manifest.encode proposal, L0Manifest.encode old], none, none⟩ := by
  simp [ManifestComposition.backend, L0Manifest.backend, valid, LinuxEffects.backend,
    Primitives.backend, Primitives.files, Files.backend, LinuxEffects.primitives,
    renameError, healthy, Bind.bind]
  rfl

/-- No reopen-success or failure receipt is assumed. Execute all three
attempts for every survivor of the failed publication. -/
theorem cutRecovery {before stored : Selected} {id : UInt64} (dir : System.FilePath) (prior : Durable before history)
    (view : stored.view = before.view) (version : stored.version = before.version)
    (created : before.tables.Created stored.tables id rows)
    (contents : ∀ key, lookupRows rows key = latest prior.pending key)
    (ordered : Rows.Ordered rows) (fits : before.view.tail < UInt64.size) :
    let proposal : Version := ⟨id :: before.version.tables, before.view.tail.toUInt64⟩
    let reached : Image := ⟨L0Manifest.encode proposal, [L0Manifest.encode proposal, L0Manifest.encode stored.version], none, none⟩
    (ManifestComposition.backend dir renameError).publish proposal (.settled (L0Manifest.encode stored.version)) =
      .error () reached ∧
    ∀ bytes ∈ reached.survivors, ∃ v, L0Manifest.encode v = bytes ∧
      Nonempty (Durable (stored.publish v) history) ∧
      (ManifestComposition.backend dir readError).reopen (.settled bytes) = .error () (.settled bytes) ∧
      (ManifestComposition.backend dir healthy).reopen (.settled bytes) = .ok v (.settled bytes) ∧
      (do
        let first ← (ManifestComposition.backend dir healthy).reopen
        let second ← (ManifestComposition.backend dir healthy).reopen
        pure (first, second)) (.settled bytes) = .ok (v, v) (.settled bytes) ∧
      (Image.settled bytes).survivors = [L0Manifest.encode v] := by
  dsimp only
  obtain ⟨old, new⟩ := flushPublicationChoices prior view version created contents ordered fits
  refine ⟨renameCut dir _ _ new.unique, ?_⟩
  intro bytes member
  have cases' : ∃ v, L0Manifest.encode v = bytes ∧ Nonempty (Durable (stored.publish v) history) := by
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_, rfl, ⟨new⟩⟩
    · obtain rfl := List.mem_singleton.mp tail
      exact ⟨_, rfl, ⟨old⟩⟩
  obtain ⟨v, rfl, ⟨durable⟩⟩ := cases'
  refine ⟨v, rfl, ⟨durable⟩, ?_, ?_, ?_, rfl⟩
  · simp [ManifestComposition.backend, L0Manifest.backend, LinuxEffects.backend,
      Primitives.backend, Primitives.files, Files.backend, LinuxEffects.primitives,
      readError, healthy, Bind.bind, EStateM.bind]
    rfl
  all_goals
    have opened := LinuxEffects.reopenHealthy dir healthy (Image.settled (L0Manifest.encode v)) rfl rfl rfl
    change (LinuxEffects.backend dir healthy).reopen (.settled (L0Manifest.encode v)) = .ok (L0Manifest.encode v) (.settled (L0Manifest.encode v)) at opened
    have valid : v.Valid := durable.unique
    simp [ManifestComposition.backend, L0Manifest.backend, Bind.bind, EStateM.bind,
      opened, L0Manifest.decode_encode valid, Pure.pure, EStateM.pure]

end ExperimentalL0.PublicationCut
