import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.Manifest.Proofs
import Alvoki.Experiments.L0.RecoveryChoices
import Alvoki.Experiments.L0.ComponentContract

namespace ExperimentalL0.ManifestComposition

open DurableBlob L0Manifest
open WalRecoverySlice.Segmented

def backend (dir : System.FilePath) (reports : LinuxEffects.Reports) :=
  L0Manifest.backend (fun _ => ()) (LinuxEffects.backend dir reports)

/-- The actual typed reopen schedule returns the version whose bytes the
directory barrier settled. Admission comes from the blob producer. -/
theorem reopen (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (admitted : before.Admits (L0Manifest.encode old) (pending.map L0Manifest.encode))
    (oldValid : old.Valid) (pendingValid : ∀ v ∈ pending, Version.Valid v)
    (returned : (LinuxEffects.backend dir reports).reopen before = .ok bytes after) :
    ∃ version, (backend dir reports).reopen before = .ok version after ∧
      after.Stable (L0Manifest.encode version) ∧ Permitted old pending version := by
  obtain ⟨step, stable⟩ := LinuxEffects.reopenSettles dir reports admitted returned
  cases step with
  | opened allowed =>
    have chosen : ∃ v, v.Valid ∧ bytes = L0Manifest.encode v ∧ Permitted old pending v := by
      rcases allowed with same | next
      · exact ⟨old, oldValid, same, Or.inl rfl⟩
      · cases pending with
        | none => simp at next
        | some v =>
          have eq : L0Manifest.encode v = bytes := Option.some.inj next
          exact ⟨v, pendingValid v (by simp), eq.symm, Or.inr rfl⟩
    obtain ⟨v, valid, rfl, permittedVersion⟩ := chosen
    refine ⟨v, ?_, stable, permittedVersion⟩
    simp [backend, L0Manifest.backend, Bind.bind, EStateM.bind, returned, L0Manifest.decode_encode valid, Pure.pure, EStateM.pure]

private theorem lastPublished (trace : Allows initial events state)
    (last : events.getLast? = some (.published bytes)) : state = .ready bytes := by
  cases trace with
  | initial => simp at last
  | next _ step =>
    simp at last
    subst_vars
    cases step
    rfl

/-- A successful publication installs exactly the submitted typed version.
The underlying publication theorem supplies the reached trace. -/
theorem publish (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (prior : Run initial events true before) (valid : proposal.Valid)
    (returned : (LinuxEffects.backend dir reports).publish (L0Manifest.encode proposal) before = .ok () after) :
    (backend dir reports).publish proposal before = .ok () after ∧
      L0Manifest.decode after.active = some proposal := by
  have run := LinuxEffects.publish dir reports (L0Manifest.encode proposal) prior
  rw [returned] at run
  have trace := run.refinesReady
  refine ⟨by simpa [backend, L0Manifest.backend, valid] using returned, ?_⟩
  have installed := lastPublished (bytes := L0Manifest.encode proposal) trace (by simp)
  rw [State.ready.inj installed, L0Manifest.decode_encode valid]

/-- The initialized empty manifest follows the same open and publish path
as any later version. -/
theorem initialOpenPublish (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (valid : proposal.Valid) :
    let initial := L0Manifest.encode Version.empty
    (LinuxEffects.backend dir reports).reopen (.settled initial) =
      .ok initial (.settled initial) →
    (LinuxEffects.backend dir reports).publish (L0Manifest.encode proposal) (.settled initial) =
      .ok () (.settled (L0Manifest.encode proposal)) →
    (backend dir reports).reopen (.settled initial) = .ok Version.empty (.settled initial) ∧
    (backend dir reports).publish proposal (.settled initial) =
      .ok () (.settled (L0Manifest.encode proposal)) ∧
    L0Manifest.decode (Image.settled (L0Manifest.encode proposal)).active = some proposal := by
  intro initial opened published
  have run := LinuxEffects.reopen dir reports (Run.initial (initial := initial))
  rw [opened] at run
  have emptyValid : Version.empty.Valid := by simp [Version.Valid, Version.empty]
  refine ⟨?_, publish dir reports run valid published⟩
  simp [backend, L0Manifest.backend, Bind.bind, EStateM.bind, opened, initial,
    L0Manifest.decode_encode emptyValid, Pure.pure, EStateM.pure]

private def healthy : LinuxEffects.Reports :=
  ⟨true, true, .ok, true, true, true, .ok, .ok⟩

/-- A healthy report sequence actually reaches the initialized open and
the first publication in the same interpreter. -/
theorem healthyInitialOpenPublish (dir : System.FilePath) (valid : proposal.Valid) :
    let initial := L0Manifest.encode Version.empty
    (backend dir healthy).reopen (.settled initial) = .ok Version.empty (.settled initial) ∧
    (backend dir healthy).publish proposal (.settled initial) =
      .ok () (.settled (L0Manifest.encode proposal)) ∧
    L0Manifest.decode (Image.settled (L0Manifest.encode proposal)).active = some proposal := by
  apply initialOpenPublish dir healthy valid <;>
    simp [LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
      LinuxEffects.primitives, healthy, Bind.bind, EStateM.bind] <;> rfl

/-- At an L0 recovery boundary, the selected version is projected from
the active image of that attempt. The WAL and table catalog are framed
separately by the filesystem namespace boundary. -/
theorem reopenSelected {selected : Selected} (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (returned : (LinuxEffects.backend dir reports).reopen before = .ok bytes after)
    (projection : before.active = L0Manifest.encode selected.version)
    (valid : selected.version.Valid) :
    (backend dir reports).reopen before = .ok selected.version after ∧
      after.Stable (L0Manifest.encode selected.version) := by
  have reached := LinuxEffects.reopenBinding dir reports before
  rw [returned] at reached
  obtain ⟨reply, stable⟩ := reached
  rw [projection] at reply
  subst bytes
  refine ⟨?_, stable⟩
  simp [backend, L0Manifest.backend, Bind.bind, EStateM.bind, returned,
    L0Manifest.decode_encode valid, Pure.pure, EStateM.pure]

/-- The producer supplies the new manifest projection. Only the two
unrelated namespace frames are needed to obtain the selected L0 state. -/
theorem publishSelected {selected reached : Selected} (dir : System.FilePath) (reports : LinuxEffects.Reports)
    (valid : proposal.Valid)
    (returned : (LinuxEffects.backend dir reports).publish (L0Manifest.encode proposal) before = .ok () after)
    (projection : L0Manifest.decode after.active = some reached.version)
    (walFrame : reached.view = selected.view) (tableFrame : reached.tables = selected.tables) :
    (backend dir reports).publish proposal before = .ok () after ∧
      reached = selected.publish proposal := by
  have settled := LinuxEffects.publishActive dir reports before (L0Manifest.encode proposal)
  rw [returned] at settled
  have decoded : L0Manifest.decode after.active = some proposal := by
    rw [settled.1, L0Manifest.decode_encode valid]
  have version := Option.some.inj (projection.symm.trans decoded)
  exact ⟨by simpa [backend, L0Manifest.backend, valid] using returned, by cases reached; cases selected; simp_all [Selected.publish]⟩

/-- Failed reopen keeps the pending choice available. A successful retry
pins it even if a later L0 callback fails and takes the session offline. -/
theorem retryAfterPublication (dir : System.FilePath) (publishReport failed opened : LinuxEffects.Reports)
    (view : Contract.View) (oldValid : old.Valid) (proposalValid : proposal.Valid)
    (stable : before.Stable (L0Manifest.encode old))
    (failure :
      let afterPublish := match (LinuxEffects.backend dir publishReport).publish (L0Manifest.encode proposal) before with
        | .ok _ image | .error _ image => image
      (LinuxEffects.backend dir failed).reopen afterPublish = .error () afterFailure)
    (success : (LinuxEffects.backend dir opened).reopen afterFailure = .ok bytes settled) :
    ∃ version, (backend dir opened).reopen afterFailure = .ok version settled ∧
      settled.Stable (L0Manifest.encode version) ∧
      RecoveryChoices.Retry (.online view) (.offline old (some proposal))
        (.online view) (.offline version none) := by
  have pending := (LinuxEffects.publishUncertainAdmits dir publishReport stable (L0Manifest.encode proposal)).2
  have admissible := (LinuxEffects.reopenFailedAdmits dir failed pending failure).2
  obtain ⟨version, returned, pinned, allowed⟩ :=
    reopen dir opened (pending := some proposal) admissible oldValid (by simpa using proposalValid) success
  exact ⟨version, returned, pinned,
    .manifest (.manifest (.manifest .initial .openFailed trivial) (.opened allowed) trivial) .stop trivial⟩

/-- Interpret the same typed manifest schedule in the manifest namespace
of the integrated callback state. Installation retains the reached image
on either outcome, including when a failed barrier took effect. -/
def callbacks (dir : System.FilePath) (read : σ → Image)
    (install : σ → Image → σ) (openReports : σ → LinuxEffects.Reports)
    (publishReports : σ → Version → LinuxEffects.Reports) :
    Backend (StorageM σ) Version where
  reopen s :=
    match (backend dir (openReports s)).reopen (read s) with
    | .ok version after => .ok version (install s after)
    | .error _ after => .error "manifest reopen failed" (install s after)
  publish version s :=
    match (backend dir (publishReports s version)).publish version (read s) with
    | .ok _ after => .ok () (install s after)
    | .error _ after => .error "manifest publication failed" (install s after)

/-- Only namespace state and primitive reports cross this boundary. The
typed return values and error cases are computed by the shared schedule. -/
structure Interpretation (ops : Backend (StorageM σ) Version) (selected : σ → Selected) where
  directory : System.FilePath
  image : σ → Image
  install : σ → Image → σ
  openReports : σ → LinuxEffects.Reports
  publishReports : σ → Version → LinuxEffects.Reports
  schedule : ops = callbacks directory image install openReports publishReports
  projection : ∀ s, (selected s).version.Valid ∧
    (image s).active = L0Manifest.encode (selected s).version
  imageInstalled : ∀ s reached, (∃ version, version.Valid ∧ reached.active = L0Manifest.encode version) →
    image (install s reached) = reached
  walFrame : ∀ s reached, (selected (install s reached)).view = (selected s).view
  tableFrame : ∀ s reached, (selected (install s reached)).tables = (selected s).tables

private theorem Interpretation.decodeImage {ops : Backend (StorageM σ) Version} (i : Interpretation ops selected) (s : σ) :
    L0Manifest.decode (i.image s).active = some (selected s).version := by
  obtain ⟨valid, encoding⟩ := i.projection s
  rw [encoding, L0Manifest.decode_encode valid]

private theorem selectedFields {a b : Selected}
    (view : a.view = b.view) (version : a.version = b.version) (tables : a.tables = b.tables) :
    a = b := by cases a; cases b; simp_all

theorem Interpretation.reopenEffect {ops : Backend (StorageM σ) Version} (i : Interpretation ops selected) (s : σ) :
    match ops.reopen s with
    | .ok version after => version = (selected s).version ∧ selected after = selected s
    | .error _ after => selected after = selected s := by
  rw [i.schedule]
  simp only [callbacks]
  have active := LinuxEffects.reopenBinding i.directory (i.openReports s) (i.image s)
  obtain ⟨valid, encoding⟩ := i.projection s
  cases returned : (LinuxEffects.backend i.directory (i.openReports s)).reopen (i.image s) with
  | ok bytes after =>
    obtain ⟨opened, stable⟩ := reopenSelected i.directory (i.openReports s) returned encoding valid
    rw [opened]
    have version := i.decodeImage (i.install s after)
    rw [i.imageInstalled s after ⟨_, valid, stable.1⟩, stable.1, L0Manifest.decode_encode valid] at version
    exact ⟨rfl, selectedFields (i.walFrame s after) (Option.some.inj version.symm)
      (i.tableFrame s after)⟩
  | error error after =>
    rw [returned] at active
    have failed : (backend i.directory (i.openReports s)).reopen (i.image s) = .error () after := by
      cases error
      simp [backend, L0Manifest.backend, Bind.bind, EStateM.bind, returned]
    rw [failed]
    have version := i.decodeImage (i.install s after)
    have canonical := active.trans encoding
    rw [i.imageInstalled s after ⟨_, valid, canonical⟩, canonical, L0Manifest.decode_encode valid] at version
    exact selectedFields (i.walFrame s after) (Option.some.inj version.symm) (i.tableFrame s after)

theorem Interpretation.publishEffect {ops : Backend (StorageM σ) Version} (i : Interpretation ops selected) (s : σ)
    (proposal : Version) (valid : proposal.Valid) :
    match ops.publish proposal s with
    | .ok _ after => selected after = (selected s).publish proposal
    | .error _ after => selected after = selected s ∨ selected after = (selected s).publish proposal := by
  rw [i.schedule]
  simp only [callbacks]
  cases returned : (LinuxEffects.backend i.directory (i.publishReports s proposal)).publish
      (L0Manifest.encode proposal) (i.image s) with
  | ok result after =>
    cases result
    have projection := i.decodeImage (i.install s after)
    have settled := LinuxEffects.publishActive i.directory (i.publishReports s proposal)
      (i.image s) (L0Manifest.encode proposal)
    rw [returned] at settled
    rw [i.imageInstalled s after ⟨_, valid, settled.1⟩] at projection
    obtain ⟨published, effect⟩ := publishSelected i.directory (i.publishReports s proposal) valid
      returned projection (i.walFrame s after) (i.tableFrame s after)
    rw [published]
    exact effect
  | error error after =>
    cases error
    have failed : (backend i.directory (i.publishReports s proposal)).publish proposal (i.image s) =
        .error () after := by
      simpa [backend, L0Manifest.backend, valid] using returned
    rw [failed]
    have active := LinuxEffects.publishActive i.directory (i.publishReports s proposal)
      (i.image s) (L0Manifest.encode proposal)
    rw [returned] at active
    have projection := i.decodeImage (i.install s after)
    rcases active with old | new
    · obtain ⟨oldValid, oldEncoded⟩ := i.projection s
      have canonical := old.trans oldEncoded
      rw [i.imageInstalled s after ⟨_, oldValid, canonical⟩, canonical,
        L0Manifest.decode_encode oldValid] at projection
      exact Or.inl (selectedFields (i.walFrame s after) (Option.some.inj projection.symm)
        (i.tableFrame s after))
    · have canonical := (Option.some.inj new).symm
      rw [i.imageInstalled s after ⟨_, valid, canonical⟩, canonical,
        L0Manifest.decode_encode valid] at projection
      exact Or.inr (selectedFields (i.walFrame s after) (Option.some.inj projection.symm)
        (i.tableFrame s after))

end ExperimentalL0.ManifestComposition
