import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkCut
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {state : NativeReadyState}

namespace NativeObsoleteRunUnlinkCut

/-- Project the one selected run map without changing the reached phase,
WAL or lock. The stopped collector itself never returns this state. -/
def survivor (cut : NativeObsoleteRunUnlinkCut state) (runs : RunFiles) : NativeReadyState :=
  { state with writer := state.writer.afterRunCollection runs, census := cut.reachedCensus }

theorem survivorValid (cut : NativeObsoleteRunUnlinkCut state) (valid : state.Valid)
    {runs : RunFiles} (survived : runs ∈ cut.reached.crashImages) : (cut.survivor runs).Valid := by
  have older (address : RunAddress) (chosen : address ∈ cut.plan.reports.selected) :
      address.1 < state.writer.installed.generation := ((cut.plan.reports.selected_eligible valid.retained).mp chosen).2.1
  have settled : (RunUnlinkImage.settled runs).guaranteed = runs :=
    congrArg Image.durable (RunUnlinkImage.project_settled runs state.writer.published.manifest)
  have retained := (valid.retained.afterRunCollection (cut.lineage.crash survived) older cut.plan.reports.known).1
  refine { valid with ownerLive := ?_, directoryLive := ?_, retained := ?_ }
  · simpa only [survivor, cut.census.2] using valid.ownerLive
  · simpa only [survivor, cut.census.2] using valid.directoryLive
  · rw [← settled]
    exact retained

end NativeObsoleteRunUnlinkCut

/-- The stopped unlink has one reported reboot namespace. Its run names
and payloads project the selected crash run map. Protected reads remain
bound to the reached filesystem objects under the reported crash. -/
structure NativeObsoleteRunUnlinkCrash (cut : NativeObsoleteRunUnlinkCut state) where
  runs : RunFiles
  survived : runs ∈ cut.reached.crashImages
  observed : NativeReadyQuietCrash (cut.survivor runs)
  runMap : ∀ (generation : UInt64) (index : Nat),
    (observed.names (state.session.directory.file (.run generation index))).map observed.contents =
      runs generation index
  reachedBindings : ∀ path, (cut.survivor runs).crashPath path →
    observed.live.names path =
      (cut.bindings (cut.reachedCensus, cut.reached) path).map cut.plan.lifetime.namespaceView.modelObject

namespace NativeObsoleteRunUnlinkCrash

variable {cut : NativeObsoleteRunUnlinkCut state}

theorem kept (crash : NativeObsoleteRunUnlinkCrash cut) (valid : state.Valid) :
    ∀ generation index bytes, state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
      cut.plan.initial.guaranteed generation index = some bytes → crash.runs generation index = some bytes := by
  intro generation index bytes retained present
  have guaranteed : (RunUnlinkImage.settled crash.runs).guaranteed = crash.runs :=
    congrArg Image.durable (RunUnlinkImage.project_settled crash.runs state.writer.published.manifest)
  rw [← guaranteed]
  apply (cut.lineage.crash crash.survived).keepsKnown (name := (generation, index)) present
  intro chosen
  have eligible := (cut.plan.reports.selected_eligible valid.retained).mp chosen
  exact retained.elim (fun le => UInt64.not_lt.mpr le eligible.2.1) eligible.2.2.1

theorem survivingRun (crash : NativeObsoleteRunUnlinkCrash cut) {generation : UInt64} {index : Nat} {bytes : ByteArray}
    (stored : crash.runs generation index = some bytes) :
    ∃ inode, crash.observed.names (state.session.directory.file (.run generation index)) = some inode ∧
      crash.observed.contents inode = bytes :=
  Option.map_eq_some_iff.mp ((crash.runMap generation index).trans stored)

theorem usesReachedBindings (crash : NativeObsoleteRunUnlinkCrash cut) {path : FilePath}
    (retained : (cut.survivor crash.runs).crashPath path) :
    crash.observed.names path =
      (cut.bindings (cut.reachedCensus, cut.reached) path).map cut.plan.lifetime.namespaceView.modelObject :=
  (crash.observed.settled _ crash.observed.chosen _ retained).trans (crash.reachedBindings _ retained)

end NativeObsoleteRunUnlinkCrash

/-- A stopped obsolete-run unlink, one physical run-map survivor and
the actual subsequent aligned return retain the same client ledger. -/
structure NativeObsoleteRunUnlinkCrashReopen (current next : NativeReadPosition history log)
    {cut : NativeObsoleteRunUnlinkCut current.state}
    (stop : NativeObsoleteRunUnlinkStop cut) (crash : NativeObsoleteRunUnlinkCrash cut) (input : FilePath) : Prop where
  stopped : ∀ barrier, stop.runFromReady barrier = .error cut.path
    (.ready current.state.writer.installed, ⟨(current.state.cache, cut.reachedCensus, cut.reached), current.state.files.owners⟩)
  selected : SelectedIntegrityCheckpoint crash.runs current.state.writer.target.pair.manifest current.state.writer.checkpoint
  keptRuns : ∀ generation index bytes,
    current.state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
    cut.plan.initial.guaranteed generation index = some bytes → crash.runs generation index = some bytes
  protectedBindings : ∀ path, (cut.survivor crash.runs).crashPath path →
    crash.observed.names path =
      (cut.bindings (cut.reachedCensus, cut.reached) path).map cut.plan.lifetime.namespaceView.modelObject
  survivingRuns : ∀ generation index bytes, crash.runs generation index = some bytes →
    ∃ inode, crash.observed.names (current.state.session.directory.file (.run generation index)) = some inode ∧
      crash.observed.contents inode = bytes
  loss : BoundedReopenTrace current.state.session.directory (· = current.state.writer.target)
    current.state.files crash.observed.retry
  reads : next.reads = current.reads
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  lock : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  directory : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  pair : next.state.files.image.directory.active = current.state.writer.target.pair
  target : next.state.writer.target = current.state.writer.target
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = crash.runs
  exactOpen : ∃ (layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history)
      (selected : SelectedIntegrityCheckpoint crash.runs
        crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (seen : NativeReadyRestartReads crash.observed input layout selected),
    next.opened = seen.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    (current.state.writer.target.pair.manifest = none →
      crash.observed.names (current.state.session.directory.file .manifest) = none) ∧
    (∀ bytes, current.state.writer.target.pair.manifest = some bytes →
      seen.ReadsSurvivor (current.state.session.directory.file .manifest) bytes) ∧
    (∀ bytes metadata, current.state.writer.target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
      crash.runs metadata.header.generation index = some payload →
        seen.ReadsSurvivor (current.state.session.directory.file (.run metadata.header.generation index)) payload) ∧
    seen.ReadsSurvivor (current.state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode current.state.writer.history).size.toUInt64) ∧
    seen.ReadsSurvivor (current.state.session.directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes ∧
    (∀ segment ∈ layout.sealed,
      seen.ReadsSurvivor (current.state.session.directory.file (.walSegment segment.first)) segment.bytes)
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- One specified reader is enough to attach the physical survivor
and previous ledger to its exact returned ready position. -/
theorem NativeObsoleteRunUnlinkCrashReopen.fromReader (current : NativeReadPosition history log)
    {cut : NativeObsoleteRunUnlinkCut current.state} (stop : NativeObsoleteRunUnlinkStop cut)
    (crash : NativeObsoleteRunUnlinkCrash cut) {input : FilePath}
    {layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history}
    {selected : SelectedIntegrityCheckpoint crash.runs
      crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint}
    (reader : NativeReadyRestartReads crash.observed input layout selected) {next : NativeReadyState}
    (reached : reader.ReachedSession next history log current.reads)
    (lost : BoundedReopenTrace current.state.session.directory (· = current.state.writer.target)
      current.state.files crash.observed.retry) :
    NativeObsoleteRunUnlinkCrashReopen current
      ⟨reader.run, next, next, current.reads, reached.1⟩ stop crash input := by
  obtain ⟨stopped, _, survivors, _, _, _⟩ := current.stopsDuringObsoleteRunUnlink cut stop
  obtain ⟨continuation, _, owner, directorySlot, cache, census, sessionFresh, phaseFresh, lock, directory,
    pair, target, checkpoint, durable, absent, manifest, runs, marker, keeper, seals, _⟩ := reached
  have keptLock : next.census.inode next.owner.description = current.state.census.inode current.state.owner.description :=
    lock.trans (congrArg (fun census : DescriptorInventory => census.inode current.state.owner.description) cut.census.2)
  have keptDirectory : next.census.inode next.directorySlot.description =
      current.state.census.inode current.state.directorySlot.description :=
    directory.trans (congrArg (fun census : DescriptorInventory => census.inode current.state.directorySlot.description) cut.census.2)
  exact ⟨stopped, survivors _ crash.survived, crash.kept current.readPrefix.refines.1,
    fun _ retained => crash.usesReachedBindings retained, fun _ _ _ stored => crash.survivingRun stored,
    lost, rfl, sessionFresh, phaseFresh, keptLock, keptDirectory, pair, target, checkpoint, durable,
    ⟨layout, selected, reader, rfl, continuation.frames.1, cache, census, owner, directorySlot, absent, manifest, runs,
      marker, keeper, seals⟩, continuation.guardedReplay⟩

theorem NativeReadPosition.recoversInterruptedRunUnlink (current : NativeReadPosition history log)
    {cut : NativeObsoleteRunUnlinkCut current.state} (stop : NativeObsoleteRunUnlinkStop cut)
    (crash : NativeObsoleteRunUnlinkCrash cut) {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history,
      layout.target = current.state.writer.target → Prepared crash.observed.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint crash.runs
        crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeReadyRestartReads crash.observed input layout selected)) :
    ∃ next, NativeObsoleteRunUnlinkCrashReopen current next stop crash input := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨lost, _, layout, selected, reader, next, reached⟩ :=
    crash.observed.restarts (cut.survivorValid valid crash.survived) sameHistory pending current.readPrefix.readsBounded observe
  exact ⟨_, NativeObsoleteRunUnlinkCrashReopen.fromReader current stop crash reader reached lost⟩

end Alvoki.Storage.DiskSession
