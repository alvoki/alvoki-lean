import Alvoki.Storage.Disk.Proofs.Collection.NativeObsoleteRunCollection

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

namespace NativeObsoleteRunBarrierError

variable {state : NativeReadyState}

abbrev after (seen : NativeObsoleteRunBarrierError state) := seen.toNativeObsoleteRunPass.after

abbrev run (seen : NativeObsoleteRunBarrierError state) := seen.toNativeObsoleteRunPass.run

abbrev next (seen : NativeObsoleteRunBarrierError state) := seen.toNativeObsoleteRunPass.next

/-- An error before the sync effect retains every old crash choice from
the actual unlink prefix. An initially possible old binding can still
survive even though the visible name has already been removed. -/
theorem beforeEffect (seen : NativeObsoleteRunBarrierError state)
    (before : seen.outcome = .errorBeforeEffect seen.cause) :
    seen.after = seen.atBarrier ∧
    ∀ candidate ∈ seen.initial.crashImages, candidate ∈ seen.after.crashImages := by
  have image : seen.after = seen.atBarrier := by
    change seen.toNativeObsoleteRunPass.after = _
    rw [seen.toNativeObsoleteRunPass.after_eq, before]
    rfl
  have unlinked := runCollectionSteps_outcome (seen.reports.selected.map RunCollection.Step.unlink)
    seen.initial seen.reports.perform seen.reports.effects
  rw [seen.unlinked] at unlinked
  exact ⟨image, fun candidate member => by
    rw [image, unlinked]
    exact RunUnlinkImage.crashChoices_afterUnlinks _ _ member⟩

theorem retainsPossibleBinding (seen : NativeObsoleteRunBarrierError state)
    (before : seen.outcome = .errorBeforeEffect seen.cause) {candidate : RunFiles}
    (survived : candidate ∈ seen.initial.crashImages) {address : RunAddress} {bytes : ByteArray}
    (old : candidate address.1 address.2 = some bytes) :
    ¬ seen.after.DurablyAbsent address := by
  intro absent
  have missing := absent.2 candidate ((seen.beforeEffect before).2 candidate survived)
  rw [old] at missing
  contradiction

/-- The acknowledged sync effect settles the exact output of the
deletion pass even when the native callback returns an error. -/
theorem afterEffect (seen : NativeObsoleteRunBarrierError state) (valid : state.Valid)
    (effective : seen.outcome = .errorAfterEffect seen.cause) :
    seen.after = seen.initial.finishPass seen.reports.selected ∧
    seen.after.crashImages = [seen.after.visible] ∧
    ∀ generation index, generation < state.writer.installed.generation → generation ∉ seen.reports.held →
      seen.after.DurablyAbsent (generation, index) := by
  have image : seen.after = seen.atBarrier.syncDirectory := by
    change seen.toNativeObsoleteRunPass.after = _
    rw [seen.toNativeObsoleteRunPass.after_eq, effective]
    rfl
  refine ⟨image.trans (seen.toNativeObsoleteRunPass.returns valid).2.2, ?_, ?_⟩
  · rw [image]
    rfl
  · rw [image]
    exact seen.toNativeObsoleteRunPass.settlesOldRuns valid

/-- Both final-barrier errors occur after the intended visible removals. -/
theorem obsoleteVisible (seen : NativeObsoleteRunBarrierError state) (valid : state.Valid) :
    ∀ generation index, generation < state.writer.installed.generation → generation ∉ seen.reports.held →
      seen.after.visible generation index = none := by
  intro generation index older unheld
  have absent := (seen.toNativeObsoleteRunPass.settlesOldRuns valid generation index older unheld).1
  change seen.toNativeObsoleteRunPass.after.visible generation index = none
  rw [seen.toNativeObsoleteRunPass.after_eq]
  split <;> exact absent

end NativeObsoleteRunBarrierError

/-- The actual obsolete-run call returns ready on a directory-sync
error. The reached namespace, including its crash choices, stays with
the same writer and client replay. -/
structure NativeObsoleteRunBarrierErrorStep (current : NativeReadPosition history log)
    (seen : NativeObsoleteRunBarrierError current.state) (next : NativeReadPosition history log) : Prop where
  state : next.state = seen.next
  returned : seen.run =
    .error seen.diagnostic (next.state.session.phase, ⟨(next.state.cache, seen.after), next.state.files.owners⟩)
  reads : next.reads = current.reads
  session : next.state.session = current.state.session
  installed : next.state.writer.installed = current.state.writer.installed
  files : next.state.files = current.state.files
  held : next.state.files.owners.Owns next.state.session.directory next.state.session.descriptor
  census : next.state.census = seen.toNativeObsoleteRunPass.returnCensus
  cache : next.state.cache = current.state.cache
  durable : next.state.writer.published.durable = seen.after.guaranteed
  retainedNames : ∀ generation index bytes,
    current.state.writer.installed.generation ≤ generation ∨ generation ∈ seen.reports.held →
    seen.initial.guaranteed generation index = some bytes →
    seen.after.guaranteed generation index = some bytes
  survivors : ∀ candidate ∈ seen.after.crashImages,
    SelectedIntegrityCheckpoint candidate current.state.writer.target.pair.manifest current.state.writer.checkpoint
  replay : InstalledClientReplay log next.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.reachesObsoleteRunBarrierError (current : NativeReadPosition history log)
    (seen : NativeObsoleteRunBarrierError current.state) :
    ∃ next, NativeObsoleteRunBarrierErrorStep current seen next := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨ready, survivors⟩ := seen.toNativeObsoleteRunPass.preservesReady valid
  let state := seen.next
  let next : NativeReadPosition history log := ⟨.ok state.session (state.census, state.files), state, state, current.reads,
    .installed rfl ready sameHistory pending current.readPrefix.readsBounded⟩
  exact ⟨next, rfl, seen.returns valid, rfl, rfl, rfl, rfl, ready.retained.held, rfl, rfl, rfl,
    seen.toNativeObsoleteRunPass.retainsNamedBytes valid, survivors, next.readPrefix.guardedReplay⟩

/-- Retry directly from the returned namespace. The same hold list
remains in force. The healthy retry settles the absences even when its
checked inventory no longer lists any of the earlier removed names. -/
theorem NativeReadPosition.retriesObsoleteRunBarrierError (current : NativeReadPosition history log)
    (seen : NativeObsoleteRunBarrierError current.state)
    (observe : ∀ middle, NativeObsoleteRunBarrierErrorStep current seen middle →
      ∃ retry : NativeObsoleteRunCollection middle.state,
        retry.initial = seen.after ∧ retry.reports.held = seen.reports.held) :
    ∃ middle, NativeObsoleteRunBarrierErrorStep current seen middle ∧
      ∃ (retry : NativeObsoleteRunCollection middle.state) (next : NativeReadPosition history log),
        retry.initial = seen.after ∧ retry.reports.held = seen.reports.held ∧
        NativeObsoleteRunCollectionStep middle retry next ∧ next.reads = current.reads ∧
        ∀ generation index, generation < current.state.writer.installed.generation → generation ∉ seen.reports.held →
          retry.atBarrier.syncDirectory.DurablyAbsent (generation, index) := by
  obtain ⟨middle, failed⟩ := current.reachesObsoleteRunBarrierError seen
  obtain ⟨retry, image, held⟩ := observe middle failed
  obtain ⟨next, returned⟩ := middle.collectsObsoleteRuns retry
  refine ⟨middle, failed, retry, next, image, held, returned, returned.reads.trans failed.reads, ?_⟩
  simpa only [failed.installed, held] using returned.obsolete

end Alvoki.Storage.DiskSession
