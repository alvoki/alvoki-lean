import Alvoki.Storage.Disk.WalSegmentAppendRepair
import Alvoki.Storage.Disk.WalSegmentCheckpointReopen

namespace Alvoki.Storage

open DiskSession WalSegmentRepair WAL.Boundary

/-- The live image retains its metadata and keeper alternatives. A power
loss can choose only a pair and a keeper admitted by the same append cut. -/
inductive AppendReopenObservation (cut : ReopenImage) : ReopenImage → Prop where
  | live : AppendReopenObservation cut cut
  | crash (pair : DirectoryPublication.Bindings) (keeper : Option ByteArray)
      (pairSurvives : pair ∈ cut.directory.crashImages) (keeperSurvives : keeper ∈ cut.wal.crashImages) :
      AppendReopenObservation cut (.crash pair keeper)

private theorem AppendReopenObservation.choices {cut observed : ReopenImage} (seen : AppendReopenObservation cut observed)
    (nonempty : cut.wal.crashImages ≠ []) :
    observed.directory.active ∈ cut.directory.active :: cut.directory.crashImages ∧
      observed.wal.crashImages ≠ [] ∧
      (∀ candidate ∈ observed.wal.active :: observed.wal.crashImages,
        candidate ∈ cut.wal.active :: cut.wal.crashImages) := by
  cases seen with
  | live => exact ⟨List.mem_cons_self .., nonempty, fun _ member => member⟩
  | crash pair keeper pairSurvives keeperSurvives =>
    refine ⟨List.mem_cons_of_mem _ pairSurvives, by simp [ReopenImage.crash, Publication.Image.settled], ?_⟩
    intro candidate member
    have same : candidate = keeper := by
      simpa [ReopenImage.crash, Publication.Image.settled] using member
    exact List.mem_cons_of_mem _ (same.symm ▸ keeperSurvives)

def WalSegmentImage.appendReopenFiles (before : WalSegmentImage) (observed : ReopenImage)
    (scratch : Option (ByteArray × Bool)) : FileImage :=
  { before.checkpointReopenFiles observed.directory scratch with
    keeper := { observed.wal with staged := scratch } }

private def WalSegment.atHistoryEnd (segment : WalSegment) (history : List WAL.Write) : WalSegment :=
  ⟨segment.first, history.length, WAL.encode (history.drop segment.first)⟩

/-- The logical layout for one selected marker. The physical repair image
still uses the observed directory choices and untrimmed keeper candidates. -/
def WalSegmentImage.appendSelectedView (before : WalSegmentImage) (pair : DirectoryPublication.Bindings)
    (history : List WAL.Write) : WalSegmentImage :=
  ⟨.settled pair, before.sealed, before.active.atHistoryEnd history⟩

private theorem chainAppend {before : List WAL.Write} {first : Nat}
    {sealed : List WalSegment} {active : WalSegment}
    (chain : WalSegment.Chain before first (sealed ++ [active]))
    (sealedEnd : ∀ segment ∈ sealed, segment.last ≤ before.length)
    (suffix : List WAL.Write) :
    WalSegment.Chain (before ++ suffix) first (sealed ++ [active.atHistoryEnd (before ++ suffix)]) := by
  induction sealed generalizing first with
  | nil =>
    have starts := chain.startsWithin active (by simp)
    cases chain
    refine .cons (segment := active.atHistoryEnd (before ++ suffix)) ?_ (fun _ => rfl) ?_ .endOfHistory
    · change active.first ≤ (before ++ suffix).length
      rw [List.length_append]
      omega
    · change WAL.encode ((before ++ suffix).drop active.first) =
        WAL.encode (((before ++ suffix).drop active.first).take ((before ++ suffix).length - active.first))
      rw [List.take_of_length_le (by simp)]
  | cons segment rest ih =>
    cases chain with
    | cons bounds nonempty bytes tail =>
      have within := sealedEnd segment (List.mem_cons_self ..)
      have span : segment.last - segment.first ≤ (before.drop segment.first).length := by
        simp only [List.length_drop]
        omega
      refine .cons bounds (fun same => False.elim (by simpa using nonempty same)) ?_
        (ih tail (fun file stored => sealedEnd file (List.mem_cons_of_mem _ stored)))
      rw [List.drop_append_of_le_length (Nat.le_trans bounds within), List.take_append_of_le_length span]
      exact bytes

private theorem WalSegmentImage.ReadLayout.atSelectedHistory {before : WalSegmentImage} {history : List WAL.Write}
    (layout : before.ReadLayout history) (pair : DirectoryPublication.Bindings) (selected : List WAL.Write)
    (starts : before.active.first ≤ selected.length) : (before.appendSelectedView pair selected).ReadLayout selected := by
  obtain ⟨sealed, _, precedes⟩ := List.pairwise_append.mp layout.ordered
  refine ⟨?_, ?_, rfl, rfl⟩
  · apply List.pairwise_append.mpr
    refine ⟨sealed, by simp, ?_⟩
    intro file earlier last seen
    obtain rfl := List.mem_singleton.mp seen
    exact precedes file earlier before.active (List.mem_singleton_self _)
  · intro segment present
    rcases List.mem_append.mp present with earlier | keeper
    · exact layout.forward segment (List.mem_append_left _ earlier)
    · obtain rfl := List.mem_singleton.mp keeper
      exact starts

/-- A write cut selects the acknowledged history or exactly one additional
frame. Every sealed segment still describes its original slice, while the
keeper's selected prefix and any physical tail come from the actual cut.
All segment names were retained by the settled writer. -/
theorem WalSegmentImage.ReadLayout.afterAppendCut
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (chain : WalSegment.Chain history 0 before.segments)
    {watermark : Nat} (covered : watermark ≤ history.length)
    (event : WAL.Write) (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (markerScratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark manifest = some watermark)
    (observed : ReopenImage) (scratch : Option (ByteArray × Bool)) :
    let cut := (writeFilesAfter (runWriteEffects history event effects markerScratch)).reopenSegment
      before.active.first history manifest
    AppendReopenObservation cut observed →
    let files := before.appendReopenFiles observed scratch
    ∃ selectedHistory,
      let wal := before.appendSelectedView observed.directory.active selectedHistory
      (selectedHistory = history ∨ selectedHistory = history ++ [event]) ∧
      files.directory.active.manifest = manifest ∧
      files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selectedHistory).size.toUInt64) ∧
      wal.ReadLayout selectedHistory ∧ WalSegment.Chain selectedHistory 0 wal.segments ∧
      ∃ selected : CanonicalKeeperLayout files selectedHistory,
        selected.range = ⟨watermark, selectedHistory.length⟩ ∧ selected.keeper = wal.active ∧
        selected.sealed ++ [selected.keeper] = wal.readDescriptors watermark ∧
        selectWalSegmentReads (wal.segments.map (·.first)) watermark =
          some (selected.first, (wal.readDescriptors watermark).map (·.first)) ∧
        (∀ segment ∈ selected.sealed, files.kept segment.first = some segment.bytes) ∧
        files.keeper.crashImages ≠ [] ∧
        (∀ bytes ∈ files.keeper.crashImages, ∃ tail, bytes = some (selected.keeper.bytes ++ tail)) ∧
        files.later.Beyond selected.range.through := by
  intro cut observedCut files
  have starts := chain.startsWithin before.active (List.mem_append_right _ (List.mem_singleton_self _))
  have nonempty : cut.wal.crashImages ≠ [] :=
    (writeFilesAfter (runWriteEffects history event effects markerScratch)).reopenImage_crashWal_nonempty
      (history.drop before.active.first) manifest
  obtain ⟨chosen, possible, survivors⟩ := observedCut.choices nonempty
  obtain ⟨unchecked, _, visible⟩ := (writeFilesAfter (runWriteEffects history event effects markerScratch)).candidate_from_tail
    (history.drop before.active.first) manifest (survivors _ (List.mem_cons_self ..))
  obtain ⟨selectedHistory, target, allowed, targetPair, sameManifest, rawMarker, first, selectedRange, trimmed, prepared⟩ :=
    prepareAfterAppendCut starts covered event fits effects manifest markerScratch checkpoint files visible possible
      (by exact ⟨rfl, rfl⟩) chosen survivors
  let wal := before.appendSelectedView observed.directory.active selectedHistory
  have sealedEnd : ∀ segment ∈ before.sealed, segment.last ≤ history.length := by
    intro segment member
    exact Nat.le_trans ((List.pairwise_append.mp layout.ordered).2.2 segment member before.active
      (List.mem_singleton_self _)).2 starts
  have canonical : WalSegment.Chain selectedHistory 0 wal.segments := by
    rcases allowed with old | appended
    · simpa only [wal, WalSegmentImage.appendSelectedView, WalSegmentImage.segments, old, List.append_nil]
        using chainAppend chain sealedEnd []
    · simpa only [wal, WalSegmentImage.appendSelectedView, WalSegmentImage.segments, appended]
        using chainAppend chain sealedEnd [event]
  have selectedStarts : before.active.first ≤ selectedHistory.length := by
    simpa only [first, selectedRange] using target.firstCovered
  have view := layout.atSelectedHistory observed.directory.active selectedHistory selectedStarts
  have decoded : wal.directory.active.walRange = some ⟨watermark, selectedHistory.length⟩ := by
    rw [← selectedRange]
    exact targetPair ▸ target.decoded
  have valid : wal.Valid selectedHistory := WalSegmentImage.Valid.of_chain canonical fun pair choice => by
    have same : pair = wal.directory.active := by
      simpa [WalSegmentImage.Selects, wal, WalSegmentImage.appendSelectedView, DirectoryPublication.Image.settled]
        using choice
    subst pair
    exact ⟨_, decoded, Nat.zero_le _, Nat.le_refl _⟩
  obtain ⟨canonicalKeeper, range, keeper, _, descriptors, offsets, sealedReads, _, _, _⟩ :=
    view.checkpointReopenLayout valid .visible decoded rfl scratch
  have activeBytes : target.trimmed = canonicalKeeper.keeper.bytes := by
    simp only [trimmed, keeper, WalSegmentImage.appendSelectedView, WalSegment.atHistoryEnd]
  obtain ⟨tail, actual⟩ := prepared.keeperPrefix.activeValid
  rw [activeBytes] at actual
  let selected : CanonicalKeeperLayout files selectedHistory :=
    ⟨canonicalKeeper.range, by rw [range]; exact decoded, canonicalKeeper.through,
      canonicalKeeper.first, canonicalKeeper.sealed, canonicalKeeper.keeper, canonicalKeeper.chain,
      canonicalKeeper.covers, tail, actual⟩
  refine ⟨selectedHistory, allowed, targetPair ▸ sameManifest, targetPair ▸ rawMarker, view, canonical,
    selected, range, keeper, descriptors, offsets, sealedReads, prepared.keeperPrefix.hasCrashImage, ?_, ?_⟩
  · intro bytes survives
    obtain ⟨suffix, exactBytes⟩ := prepared.keeperPrefix.crashValid bytes survives
    exact ⟨suffix, by rw [exactBytes, activeBytes]⟩
  · change files.later.Beyond canonicalKeeper.range.through
    rw [range, ← selectedRange]
    exact prepared.newer

end Alvoki.Storage
