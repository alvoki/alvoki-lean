import Alvoki.Storage.Disk.NativeCoveredWalUnlinkStop
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact stopped collector supplies this reached namespace. Both
unlink and directory-barrier stops admit the same recovery proof. -/
structure NativeCoveredWalCrashCut (state : NativeReadyState) where
  calls : WalCollectionReads
  inventory : WalCollectionInventoryReport calls state.session.directory state.session.descriptor state.writer.wal
  census : DescriptorInventory
  sameCensus : census = state.census
  afterView : DirectoryReadNamespace
  after : WalSealedUnlinkImage
  objects : afterView.modelObject = inventory.lifetime.namespaceView.modelObject
  frameChild : ∀ {name : String}, (∀ offset ∈ state.writer.wal.collectionOffsets, name ≠ renderWalSegmentName offset) →
    afterView.child inventory.lifetime.root name = inventory.lifetime.namespaceView.child inventory.lifetime.root name
  intact : state.Valid → after.visible.directory = state.writer.wal.directory ∧ after.visible.active = state.writer.wal.active
  survivorAllowed : state.Valid → ∀ sealed ∈ after.crashSealed,
    WalSegmentCollectionRetry state.writer.wal { after.visible with sealed }

namespace NativeCoveredWalCrashCut

variable {state : NativeReadyState}

/-- The reported surviving seals change only the retained WAL inventory.
This projection is proof evidence for recovery from the outer cut. -/
def survivor (cut : NativeCoveredWalCrashCut state) (sealed : List WalSegment) : NativeReadyState :=
  { state with
    writer := state.writer.afterWalCollection (.start { cut.after.visible with sealed })
    census := cut.census }

theorem survivorValid (cut : NativeCoveredWalCrashCut state) (valid : state.Valid)
    {sealed : List WalSegment} (survived : sealed ∈ cut.after.crashSealed) : (cut.survivor sealed).Valid := by
  refine { valid with ownerLive := ?_, directoryLive := ?_, retained := ?_ }
  · simpa only [survivor, cut.sameCensus] using valid.ownerLive
  · simpa only [survivor, cut.sameCensus] using valid.directoryLive
  · exact valid.retained.afterWalProjection (cut.survivorAllowed valid sealed survived) (cut.intact valid).1

/-- All allowed seal lists supply the same ordered files to marked open. -/
theorem survivingReads (cut : NativeCoveredWalCrashCut state) (valid : state.Valid)
    {sealed : List WalSegment} (survived : sealed ∈ cut.after.crashSealed) :
    (cut.survivor sealed).writer.wal.readDescriptors state.writer.target.range.watermark =
      state.writer.wal.readDescriptors state.writer.target.range.watermark := by
  have retry := cut.survivorAllowed valid sealed survived
  have directory : (cut.survivor sealed).writer.wal.directory = state.writer.wal.directory := (cut.intact valid).1
  have pair := (congrArg DirectoryPublication.Image.active directory).trans valid.retained.walPair
  have decoded : (cut.survivor sealed).writer.wal.directory.active.walRange = some state.writer.target.range :=
    pair.symm ▸ state.writer.target.decoded
  exact retry.keepsReadDescriptors (List.mem_cons_self ..) decoded

end NativeCoveredWalCrashCut

/-- One reboot reports an allowed seal list and a single namespace and
payload image. The retained observations use the checked view before
the entire unlink schedule. Any unbarriered detached seal can reappear
with its original binding. Protected names still resolve at the cut. -/
structure NativeCoveredWalCrash {state : NativeReadyState} (cut : NativeCoveredWalCrashCut state) where
  sealed : List WalSegment
  survived : sealed ∈ cut.after.crashSealed
  observed : NativeReadyQuietCrash (cut.survivor sealed)
  beforeBindings : ∀ name,
    (cut.survivor sealed).crashPath ⟨state.session.directory.path.toString ++ "/" ++ name⟩ →
    observed.live.names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
    (cut.inventory.lifetime.namespaceView.child cut.inventory.lifetime.root name).map
      cut.inventory.lifetime.namespaceView.modelObject
  walBindings : ∀ offset, observed.names (state.session.directory.file (.walSegment offset)) =
    if offset = state.writer.wal.active.first ∨ offset ∈ sealed.map WalSegment.first then
      (cut.inventory.lifetime.namespaceView.child cut.inventory.lifetime.root (renderWalSegmentName offset)).map
        cut.inventory.lifetime.namespaceView.modelObject
    else none

namespace NativeCoveredWalCrash

variable {state : NativeReadyState} {cut : NativeCoveredWalCrashCut state}

theorem keepsReachedBinding (crash : NativeCoveredWalCrash cut) {name : String}
    (selected : (cut.survivor crash.sealed).crashPath ⟨state.session.directory.path.toString ++ "/" ++ name⟩)
    (other : ∀ offset ∈ state.writer.wal.collectionOffsets, name ≠ renderWalSegmentName offset) :
    crash.observed.names ⟨state.session.directory.path.toString ++ "/" ++ name⟩ =
      (cut.afterView.child cut.inventory.lifetime.root name).map cut.afterView.modelObject := by
  rw [crash.observed.settled _ crash.observed.chosen _ selected, crash.beforeBindings name selected, cut.frameChild other,
    cut.objects]

theorem survivingSeal (crash : NativeCoveredWalCrash cut) (valid : state.Valid)
    (segment : WalSegment) (member : segment ∈ crash.sealed) :
    let earlier := (cut.survivorAllowed valid crash.sealed crash.survived).sealedSublist.subset member
    let child := (cut.inventory.extent segment (List.mem_append_left _ earlier)).child.child
    crash.observed.names (state.session.directory.file (.walSegment segment.first)) =
      some (cut.inventory.lifetime.namespaceView.modelObject child) ∧
    crash.observed.contents (cut.inventory.lifetime.namespaceView.modelObject child) = segment.bytes := by
  intro earlier child
  have binding := crash.walBindings segment.first
  rw [ite_eq_left (.inr (List.mem_map_of_mem member)), cut.inventory.bound segment (List.mem_append_left _ earlier)] at binding
  obtain ⟨inode, named, contents⟩ := crash.observed.sealSurvives segment member
  exact ⟨binding, Option.some.inj (named.symm.trans binding) ▸ contents⟩

/-- The surviving keeper is the same physical object from the checked
inventory through the interrupted collector and the reboot. -/
theorem survivingKeeper (crash : NativeCoveredWalCrash cut) (valid : state.Valid) :
    ∃ child, cut.afterView.child cut.inventory.lifetime.root (renderWalSegmentName state.writer.wal.active.first) =
        some child ∧
      crash.observed.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
        some (cut.afterView.modelObject child) ∧
      crash.observed.contents (cut.afterView.modelObject child) = state.writer.wal.active.bytes := by
  let keeper := state.writer.wal.active
  have retained : keeper ∈ state.writer.wal.segments := List.mem_append_right _ List.mem_cons_self
  let child := (cut.inventory.extent keeper retained).child.child
  have original : cut.inventory.lifetime.namespaceView.child cut.inventory.lifetime.root
      (renderWalSegmentName keeper.first) = some child := cut.inventory.bound keeper retained
  have distinct (offset : Nat) (included : offset ∈ state.writer.wal.collectionOffsets) :
      renderWalSegmentName keeper.first ≠ renderWalSegmentName offset := by
    obtain ⟨segment, member, atFirst⟩ := (valid.retained.layout.collectionOffsets_approved included).1
    have eligible := (valid.retained.layout.collectionOffsets_approved included).2 segment member atFirst
    intro same
    have measures := congrArg parseWalSegmentName same
    simp only [parseWalSegmentName_render, Option.some.injEq] at measures
    have earlier := Nat.lt_of_lt_of_le eligible.sealedBeforeActive.1 eligible.sealedBeforeActive.2
    exact (Nat.ne_of_lt earlier) (atFirst.trans measures.symm)
  have chosen := crash.walBindings keeper.first
  rw [ite_eq_left (.inl rfl), original, Option.map_some, ← cut.objects] at chosen
  obtain ⟨inode, named, contents⟩ := crash.observed.keeperSurvives
  change crash.observed.names (state.session.directory.file (.walSegment cut.after.visible.active.first)) = some inode at named
  change crash.observed.contents inode = cut.after.visible.active.bytes at contents
  rw [(cut.intact valid).2] at named contents
  exact ⟨child, (cut.frameChild distinct).trans original, chosen,
    Option.some.inj (named.symm.trans chosen) ▸ contents⟩

end NativeCoveredWalCrash

namespace NativeCoveredWalCrash

variable {state : NativeReadyState} {cut : NativeCoveredWalCrashCut state}

def ReopenReports (crash : NativeCoveredWalCrash cut) (input : FilePath) : Prop :=
  ∀ layout : CanonicalKeeperLayout crash.observed.retry.image state.writer.history,
    layout.target = state.writer.target → Prepared crash.observed.retry.image layout.target layout.plan →
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.observed.retry.image.directory.active.manifest state.writer.checkpoint,
    Nonempty (NativeReadyRestartReads crash.observed input layout selected)

end NativeCoveredWalCrash

/-- The reported reboot keeps the marked suffix and checkpoint, then
uses the same captured aligned opener to return the actual table. -/
structure NativeCoveredWalReopened (current : NativeReadPosition history log)
    {cut : NativeCoveredWalCrashCut current.state} (crash : NativeCoveredWalCrash cut) (input : FilePath) : Prop where
  checkpoint : SelectedIntegrityCheckpoint current.state.writer.published.durable
    crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint
  keeper : (cut.survivor crash.sealed).writer.wal.active = current.state.writer.wal.active
  keeperObject : ∃ child,
    cut.afterView.child cut.inventory.lifetime.root (renderWalSegmentName current.state.writer.wal.active.first) = some child ∧
    crash.observed.names (current.state.session.directory.file (.walSegment current.state.writer.wal.active.first)) =
      some (cut.afterView.modelObject child) ∧
    crash.observed.contents (cut.afterView.modelObject child) = current.state.writer.wal.active.bytes
  suffix : (cut.survivor crash.sealed).writer.wal.readDescriptors current.state.writer.target.range.watermark =
    current.state.writer.wal.readDescriptors current.state.writer.target.range.watermark
  reopened : crash.observed.Reopened input history log current.reads

theorem NativeReadPosition.reopensCoveredWalCut (current : NativeReadPosition history log)
    {cut : NativeCoveredWalCrashCut current.state} (crash : NativeCoveredWalCrash cut) {input : FilePath}
    (observe : crash.ReopenReports input) : NativeCoveredWalReopened current crash input := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  have retry := cut.survivorValid valid crash.survived
  exact ⟨retry.retained.resumed.selected, (cut.intact valid).2, crash.survivingKeeper valid,
    cut.survivingReads valid crash.survived,
    crash.observed.restarts retry sameHistory pending current.readPrefix.readsBounded observe⟩

namespace NativeCoveredWalUnlinkStop

variable {state : NativeReadyState}

def crashCut (stop : NativeCoveredWalUnlinkStop state) : NativeCoveredWalCrashCut state :=
  ⟨stop.calls, stop.inventory, stop.census, stop.sameCensus.2, stop.afterView, stop.after,
    stop.objects, stop.frameChild, fun _ => stop.intact, fun valid => (stop.selections valid).2⟩

end NativeCoveredWalUnlinkStop

abbrev NativeCoveredWalUnlinkCrash {state : NativeReadyState} (stop : NativeCoveredWalUnlinkStop state) :=
  NativeCoveredWalCrash stop.crashCut

/-- The in-flight covered unlink and actual next healthy aligned
open use the same ledger, selected checkpoint and marked WAL suffix. -/
structure NativeCoveredWalUnlinkReopen (current : NativeReadPosition history log)
    {stop : NativeCoveredWalUnlinkStop current.state} (crash : NativeCoveredWalUnlinkCrash stop) (input : FilePath) : Prop
    extends NativeCoveredWalReopened current crash input where
  stopped : ∀ barrier, stop.run barrier = .error stop.path
    (.poisoned, ⟨(current.state.cache, stop.census, stop.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor

theorem NativeReadPosition.recoversInterruptedCoveredWalUnlink (current : NativeReadPosition history log)
    (stop : NativeCoveredWalUnlinkStop current.state) (crash : NativeCoveredWalUnlinkCrash stop) {input : FilePath}
    (observe : crash.ReopenReports input) : NativeCoveredWalUnlinkReopen current crash input := by
  let valid := current.readPrefix.refines.1
  exact ⟨current.reopensCoveredWalCut crash observe, stop.stops valid, valid.retained.held⟩

end Alvoki.Storage.DiskSession
