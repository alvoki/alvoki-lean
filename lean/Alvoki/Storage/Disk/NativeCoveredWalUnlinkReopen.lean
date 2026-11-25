import Alvoki.Storage.Disk.NativeCoveredWalUnlinkStop
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeCoveredWalUnlinkStop

variable {state : NativeReadyState}

/-- The reported surviving seals change only the retained WAL inventory.
This projection is proof evidence for recovery from the outer stop. -/
def survivor (stop : NativeCoveredWalUnlinkStop state) (sealed : List WalSegment) : NativeReadyState :=
  { state with
    writer := state.writer.afterWalCollection (.start { stop.after.visible with sealed })
    census := stop.census }

theorem survivorValid (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid)
    {sealed : List WalSegment} (survived : sealed ∈ stop.after.crashSealed) : (stop.survivor sealed).Valid := by
  refine { valid with ownerLive := ?_, directoryLive := ?_, retained := ?_ }
  · simpa only [survivor, stop.sameCensus.2] using valid.ownerLive
  · simpa only [survivor, stop.sameCensus.2] using valid.directoryLive
  · exact valid.retained.afterWalProjection ((stop.selections valid).2 sealed survived) stop.effect.metadata

/-- All allowed seal lists supply the same ordered files to marked open. -/
theorem survivingReads (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid)
    {sealed : List WalSegment} (survived : sealed ∈ stop.after.crashSealed) :
    (stop.survivor sealed).writer.wal.readDescriptors state.writer.target.range.watermark =
      state.writer.wal.readDescriptors state.writer.target.range.watermark := by
  have retry := (stop.selections valid).2 sealed survived
  have directory : (stop.survivor sealed).writer.wal.directory = state.writer.wal.directory := stop.effect.metadata
  have pair := (congrArg DirectoryPublication.Image.active directory).trans valid.retained.walPair
  have decoded : (stop.survivor sealed).writer.wal.directory.active.walRange = some state.writer.target.range :=
    pair.symm ▸ state.writer.target.decoded
  exact retry.keepsReadDescriptors (List.mem_cons_self ..) decoded

end NativeCoveredWalUnlinkStop

/-- One reboot reports an allowed seal list and a single namespace and
payload image. The retained file observations use the pre-effect view
of the issued unlink: an unbarriered detached seal can reappear with its
original binding. Other selected names still resolve at the stop. -/
structure NativeCoveredWalUnlinkCrash {state : NativeReadyState} (stop : NativeCoveredWalUnlinkStop state) where
  sealed : List WalSegment
  survived : sealed ∈ stop.after.crashSealed
  observed : NativeReadyQuietCrash (stop.survivor sealed)
  beforeBindings : ∀ name,
    (stop.survivor sealed).crashPath ⟨state.session.directory.path.toString ++ "/" ++ name⟩ →
    observed.live.names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
    (stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root name).map
      stop.inventory.lifetime.namespaceView.modelObject
  walBindings : ∀ offset, observed.names (state.session.directory.file (.walSegment offset)) =
    if offset = state.writer.wal.active.first ∨ offset ∈ sealed.map WalSegment.first then
      (stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root (renderWalSegmentName offset)).map
        stop.inventory.lifetime.namespaceView.modelObject
    else none

namespace NativeCoveredWalUnlinkCrash

variable {state : NativeReadyState} {stop : NativeCoveredWalUnlinkStop state}

theorem keepsReachedBinding (crash : NativeCoveredWalUnlinkCrash stop) {name : String}
    (selected : (stop.survivor crash.sealed).crashPath ⟨state.session.directory.path.toString ++ "/" ++ name⟩)
    (other : name ≠ renderWalSegmentName stop.first) :
    crash.observed.names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
      (stop.afterView.child stop.inventory.lifetime.root name).map stop.afterView.modelObject := by
  rw [crash.observed.settled _ crash.observed.chosen _ selected, crash.beforeBindings name selected, stop.effect.frame name other,
    stop.objects]

theorem survivingSeal (crash : NativeCoveredWalUnlinkCrash stop) (valid : state.Valid)
    (segment : WalSegment) (member : segment ∈ crash.sealed) :
    let earlier := ((stop.selections valid).2 crash.sealed crash.survived).sealedSublist.subset member
    let child := (stop.inventory.extent segment (List.mem_append_left _ earlier)).child.child
    crash.observed.names (state.session.directory.file (.walSegment segment.first)) =
      some (stop.inventory.lifetime.namespaceView.modelObject child) ∧
    crash.observed.contents (stop.inventory.lifetime.namespaceView.modelObject child) = segment.bytes := by
  intro earlier child
  have binding := crash.walBindings segment.first
  rw [ite_eq_left (.inr (List.mem_map_of_mem member)), stop.inventory.bound segment (List.mem_append_left _ earlier)] at binding
  obtain ⟨inode, named, contents⟩ := crash.observed.sealSurvives segment member
  exact ⟨binding, Option.some.inj (named.symm.trans binding) ▸ contents⟩

/-- The surviving keeper is the same physical object from the checked
inventory through the interrupted unlink and the reboot. -/
theorem survivingKeeper (crash : NativeCoveredWalUnlinkCrash stop) (valid : state.Valid) :
    ∃ child, stop.afterView.child stop.inventory.lifetime.root (renderWalSegmentName state.writer.wal.active.first) =
        some child ∧
      crash.observed.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
        some (stop.afterView.modelObject child) ∧
      crash.observed.contents (stop.afterView.modelObject child) = state.writer.wal.active.bytes := by
  let keeper := state.writer.wal.active
  have retained : keeper ∈ state.writer.wal.segments := List.mem_append_right _ List.mem_cons_self
  let child := (stop.inventory.extent keeper retained).child.child
  have original : stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root
      (renderWalSegmentName keeper.first) = some child := stop.inventory.bound keeper retained
  obtain ⟨segment, _, atFirst, eligible, _⟩ := stop.inspectedSeal valid
  have distinct : renderWalSegmentName keeper.first ≠ renderWalSegmentName stop.first := by
    intro same
    have measures := congrArg parseWalSegmentName same
    simp only [parseWalSegmentName_render, Option.some.injEq] at measures
    have earlier := Nat.lt_of_lt_of_le eligible.sealedBeforeActive.1 eligible.sealedBeforeActive.2
    exact (Nat.ne_of_lt earlier) (atFirst.trans measures.symm)
  have chosen := crash.walBindings keeper.first
  rw [ite_eq_left (.inl rfl), original, Option.map_some, ← stop.objects] at chosen
  obtain ⟨inode, named, contents⟩ := crash.observed.keeperSurvives
  change crash.observed.names (state.session.directory.file (.walSegment stop.after.visible.active.first)) = some inode at named
  change crash.observed.contents inode = stop.after.visible.active.bytes at contents
  rw [stop.effect.keeper] at named contents
  exact ⟨child, (stop.effect.frame _ distinct).trans original, chosen,
    Option.some.inj (named.symm.trans chosen) ▸ contents⟩

end NativeCoveredWalUnlinkCrash

/-- The first in-flight covered unlink and actual next healthy aligned
open use the same ledger, selected checkpoint and marked WAL suffix. -/
structure NativeCoveredWalUnlinkReopen (current : NativeReadPosition history log)
    {stop : NativeCoveredWalUnlinkStop current.state} (crash : NativeCoveredWalUnlinkCrash stop) (input : FilePath) : Prop where
  stopped : ∀ barrier, stop.run barrier = .error stop.path
    (.poisoned, ⟨(current.state.cache, stop.census, stop.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  checkpoint : SelectedIntegrityCheckpoint current.state.writer.published.durable
    crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint
  keeper : (stop.survivor crash.sealed).writer.wal.active = current.state.writer.wal.active
  keeperObject : ∃ child,
    stop.afterView.child stop.inventory.lifetime.root (renderWalSegmentName current.state.writer.wal.active.first) = some child ∧
    crash.observed.names (current.state.session.directory.file (.walSegment current.state.writer.wal.active.first)) =
      some (stop.afterView.modelObject child) ∧
    crash.observed.contents (stop.afterView.modelObject child) = current.state.writer.wal.active.bytes
  suffix : (stop.survivor crash.sealed).writer.wal.readDescriptors current.state.writer.target.range.watermark =
    current.state.writer.wal.readDescriptors current.state.writer.target.range.watermark
  reopened : crash.observed.Reopened input history log current.reads

theorem NativeReadPosition.recoversInterruptedCoveredWalUnlink (current : NativeReadPosition history log)
    (stop : NativeCoveredWalUnlinkStop current.state) (crash : NativeCoveredWalUnlinkCrash stop) {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history,
      layout.target = current.state.writer.target → Prepared crash.observed.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeReadyRestartReads crash.observed input layout selected)) :
    NativeCoveredWalUnlinkReopen current crash input := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  have retry := stop.survivorValid valid crash.survived
  exact ⟨stop.stops valid, valid.retained.held, retry.retained.resumed.selected, stop.effect.keeper, crash.survivingKeeper valid,
    stop.survivingReads valid crash.survived,
    crash.observed.restarts retry sameHistory pending current.readPrefix.readsBounded observe⟩

end Alvoki.Storage.DiskSession
