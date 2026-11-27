import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeObsoleteRunUnlinkCut

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

/-- Each failed collection retry starts from the actual preceding error's
ready position and full run namespace. The hold list stays fixed and the
recorded diagnostic list is the order of the returned failures. -/
inductive NativeObsoleteRunUnlinkRetries {history log} (first : NativeReadPosition history log)
    (initial : RunUnlinkImage) (held : List UInt64) :
    NativeReadPosition history log → RunUnlinkImage → List IO.Error → Prop where
  | first {next : NativeReadPosition history log} (cut : NativeObsoleteRunUnlinkCut first.state)
      (error : NativeObsoleteRunUnlinkError cut) (returned : NativeObsoleteRunUnlinkErrorStep first cut error next)
      (sameImage : cut.plan.initial = initial) (sameHolds : cut.plan.reports.held = held) :
      NativeObsoleteRunUnlinkRetries first initial held next cut.reached [error.cause]
  | step {current next : NativeReadPosition history log} {before : RunUnlinkImage} {errors : List IO.Error}
      (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors)
      (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut)
      (returned : NativeObsoleteRunUnlinkErrorStep current cut error next)
      (sameImage : cut.plan.initial = before) (sameHolds : cut.plan.reports.held = held) :
      NativeObsoleteRunUnlinkRetries first initial held next cut.reached (errors ++ [error.cause])

/-- Start the lineage by deriving the first native error return at the
provided ready session. No subsequent retry result is needed. -/
theorem NativeReadPosition.startsObsoleteRunUnlinkRetries (current : NativeReadPosition history log)
    (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut) :
    ∃ next, NativeObsoleteRunUnlinkRetries current cut.plan.initial cut.plan.reports.held next cut.reached [error.cause] := by
  obtain ⟨next, returned⟩ := current.reachesObsoleteRunUnlinkError cut error
  exact ⟨next, .first cut error returned rfl rfl⟩

namespace NativeObsoleteRunUnlinkRetries

variable {history : List WAL.Write} {log : List DatabaseSubmissions}
  {first current : NativeReadPosition history log} {initial before : RunUnlinkImage}
  {held : List UInt64} {errors : List IO.Error}

theorem observesFailure (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors)
    (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut)
    (sameImage : cut.plan.initial = before) (sameHolds : cut.plan.reports.held = held) :
    ∃ next, NativeObsoleteRunUnlinkRetries first initial held next cut.reached (errors ++ [error.cause]) := by
  obtain ⟨next, returned⟩ := current.reachesObsoleteRunUnlinkError cut error
  exact ⟨next, .step prior cut error returned sameImage sameHolds⟩

/-- The retry lineage advances only the run namespace, with the same
returned session, table and checkpoint throughout. -/
theorem frames (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors) :
    current.state.session = first.state.session ∧ current.state.writer.installed = first.state.writer.installed ∧
    current.state.files = first.state.files ∧ current.state.cache = first.state.cache ∧
    current.state.census = first.state.census ∧ current.state.owner = first.state.owner ∧
    current.state.directorySlot = first.state.directorySlot ∧ current.state.writer.checkpoint = first.state.writer.checkpoint ∧
    current.state.writer.target = first.state.writer.target ∧ current.reads = first.reads := by
  induction prior with
  | first cut _ returned _ _ =>
    exact ⟨returned.session, returned.installed, returned.files, returned.cache, returned.census.trans cut.census.2,
      by rw [returned.state]; rfl, by rw [returned.state]; rfl,
      by rw [returned.state]; rfl, by rw [returned.state]; rfl, returned.reads⟩
  | step _ cut _ returned _ _ ih =>
    obtain ⟨session, installed, files, cache, census, owner, directory, checkpoint, target, reads⟩ := ih
    exact ⟨returned.session.trans session, returned.installed.trans installed, returned.files.trans files,
      returned.cache.trans cache, returned.census.trans (cut.census.2.trans census),
      by rw [returned.state]; exact owner, by rw [returned.state]; exact directory,
      by rw [returned.state]; exact checkpoint, by rw [returned.state]; exact target, returned.reads.trans reads⟩

theorem crashChoices (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors) :
    (∀ candidate ∈ initial.crashImages, candidate ∈ before.crashImages) ∧
    ∀ candidate ∈ before.crashImages,
      SelectedIntegrityCheckpoint candidate first.state.writer.target.pair.manifest first.state.writer.checkpoint := by
  induction prior with
  | first cut _ returned sameImage _ =>
    exact ⟨fun candidate member => cut.namespaceAtCut.2.2.2 candidate (sameImage.symm ▸ member), returned.survivors⟩
  | step earlier cut _ returned sameImage _ ih =>
    refine ⟨fun candidate member => cut.namespaceAtCut.2.2.2 candidate (sameImage.symm ▸ ih.1 candidate member), ?_⟩
    have selected := returned.survivors
    obtain ⟨_, _, _, _, _, _, _, checkpoint, target, _⟩ := earlier.frames
    rw [target, checkpoint] at selected
    exact selected

theorem retainsNamedBytes (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors) :
    ∀ generation index bytes, first.state.writer.installed.generation ≤ generation ∨ generation ∈ held →
      initial.guaranteed generation index = some bytes → before.guaranteed generation index = some bytes := by
  induction prior with
  | first _ _ returned sameImage sameHolds =>
    simpa only [sameImage, sameHolds] using returned.retainedNames
  | step earlier _ _ returned sameImage sameHolds ih =>
    intro generation index bytes keep originally
    apply returned.retainedNames generation index bytes
    · simpa only [earlier.frames.2.1, sameHolds] using keep
    · rw [sameImage]
      exact ih generation index bytes keep originally

/-- A healthy checked pass from the last exact error image durably settles
all old unheld absences. The ready return and replay are still those of the
same original writer, even when this pass has an empty unlink list. -/
theorem completes (prior : NativeObsoleteRunUnlinkRetries first initial held current before errors)
    (retry : NativeObsoleteRunCollection current.state) (sameImage : retry.initial = before)
    (sameHolds : retry.reports.held = held) :
    ∃ next, NativeObsoleteRunCollectionStep current retry next ∧
      next.state.session = first.state.session ∧ next.state.writer.installed = first.state.writer.installed ∧
      next.state.files = first.state.files ∧ next.state.cache = first.state.cache ∧ next.state.census = first.state.census ∧
      next.state.owner = first.state.owner ∧ next.state.directorySlot = first.state.directorySlot ∧ next.reads = first.reads ∧
      SelectedIntegrityCheckpoint retry.atBarrier.syncDirectory.visible first.state.writer.target.pair.manifest
        first.state.writer.checkpoint ∧
      (∀ generation index, generation < first.state.writer.installed.generation → generation ∉ held →
        retry.atBarrier.syncDirectory.DurablyAbsent (generation, index)) ∧
      ∀ generation index bytes, first.state.writer.installed.generation ≤ generation ∨ generation ∈ held →
        initial.guaranteed generation index = some bytes →
        retry.atBarrier.syncDirectory.guaranteed generation index = some bytes := by
  obtain ⟨next, returned⟩ := current.collectsObsoleteRuns retry
  obtain ⟨session, installed, files, cache, census, owner, directory, checkpoint, target, reads⟩ := prior.frames
  refine ⟨next, returned, returned.session.trans session, returned.installed.trans installed, returned.files.trans files,
    returned.cache.trans cache, returned.census.trans census, returned.owner.trans owner, returned.directory.trans directory,
    returned.reads.trans reads, ?_, ?_, ?_⟩
  · simpa only [target, checkpoint] using returned.selected
  · simpa only [installed, sameHolds] using returned.obsolete
  · intro generation index bytes keep originally
    apply returned.retainedNames generation index bytes
    · simpa only [installed, sameHolds] using keep
    · rw [sameImage]
      exact prior.retainsNamedBytes generation index bytes keep originally

end NativeObsoleteRunUnlinkRetries
end Alvoki.Storage.DiskSession
