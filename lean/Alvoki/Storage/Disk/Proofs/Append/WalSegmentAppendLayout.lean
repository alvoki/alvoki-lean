import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendRepair
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCheckpointReopen
import Alvoki.Storage.Disk.Proofs.Append.ReopenedSegmentAppend

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

/-- Extending the active segment preserves the complete segment catalog. -/
theorem WalSegmentImage.appendSelectedView_starts (wal : WalSegmentImage) (pair : DirectoryPublication.Bindings)
    (history : List WAL.Write) :
    (wal.appendSelectedView pair history).segments.map WalSegment.first = wal.segments.map WalSegment.first := by
  rw [WalSegmentImage.segments, List.map_append, WalSegmentImage.segments, List.map_append]
  rfl

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

private theorem WalSegmentImage.ReadLayout.sealedEndsBeforeHistory
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (starts : before.active.first ≤ history.length) : ∀ segment ∈ before.sealed, segment.last ≤ history.length := by
  intro segment member
  exact Nat.le_trans ((List.pairwise_append.mp layout.ordered).2.2 segment member before.active
    (List.mem_singleton_self _)).2 starts

private theorem WalSegmentImage.ReadLayout.extendActiveSuffix
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (pair : DirectoryPublication.Bindings) (suffix : List WAL.Write) :
    let selected := history ++ suffix
    let wal := before.appendSelectedView pair selected
    wal.ReadLayout selected ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encode suffix⟩ := by
  intro selected wal
  have starts : before.active.first ≤ history.length := by
    rw [← layout.activeEnd]
    exact layout.forward before.active (List.mem_append_right _ (by simp))
  have wider : before.active.first ≤ selected.length := Nat.le_trans starts (by simp [selected])
  refine ⟨layout.atSelectedHistory pair selected wider, ?_⟩
  change (⟨before.active.first, selected.length,
    WAL.encode ((history ++ suffix).drop before.active.first)⟩ : WalSegment) =
    ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encode suffix⟩
  rw [List.drop_append_of_le_length starts, WAL.encode_append, layout.activeBytes]

private theorem WalSegmentImage.ReadLayout.extendActive
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (pair : DirectoryPublication.Bindings) (event : WAL.Write) :
    let selected := history ++ [event]
    let wal := before.appendSelectedView pair selected
    wal.ReadLayout selected ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encodeFrame event⟩ := by
  simpa [WAL.encode] using layout.extendActiveSuffix pair [event]

/-- An acknowledged append extends the active segment by one canonical
frame. All sealed descriptors and the active file's start stay exact. -/
theorem WalSegmentImage.ReadLayout.afterAcknowledgedAppend
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (chain : WalSegment.Chain history 0 before.segments) (pair : DirectoryPublication.Bindings) (event : WAL.Write) :
    let selected := history ++ [event]
    let wal := before.appendSelectedView pair selected
    wal.ReadLayout selected ∧ WalSegment.Chain selected 0 wal.segments ∧ wal.sealed = before.sealed ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encodeFrame event⟩ := by
  intro selected wal
  have starts := chain.startsWithin before.active (List.mem_append_right _ (List.mem_singleton_self _))
  have active := layout.extendActive pair event
  exact ⟨active.1, chainAppend chain (layout.sealedEndsBeforeHistory starts) [event], rfl, active.2⟩

private theorem WalSegmentImage.ReadLayout.readDescriptors_filter
    {image : WalSegmentImage} {history : List WAL.Write} (layout : image.ReadLayout history) (watermark : Nat) :
    image.readDescriptors watermark =
      image.sealed.filter (fun segment => decide (watermark < segment.last)) ++ [image.active] := by
  by_cases needed : watermark < image.active.last
  · simp [WalSegmentImage.readDescriptors, WalSegmentImage.afterWatermark, List.filter_append, needed]
  · have within := layout.forward image.active (List.mem_append_right _ (by simp))
    have allCovered := layout.sealedEndsBeforeHistory (layout.activeEnd ▸ within)
    have noSeals : image.sealed.filter (fun segment => decide (watermark < segment.last)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro segment member
      have covered : segment.last ≤ watermark :=
        Nat.le_trans (allCovered segment member) (layout.activeEnd ▸ Nat.le_of_not_gt needed)
      simp [Nat.not_lt_of_ge covered]
    simp [WalSegmentImage.readDescriptors, needed, noSeals]

/-- A selected suffix extends the original active descriptor while keeping
the gap-free read chain from the selected checkpoint. An empty suffix
preserves the original read layout, including an empty active descriptor. -/
theorem WalSegmentImage.ReadLayout.afterRetainedSuffix
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (valid : before.Valid history) {watermark : Nat}
    (oldRange : before.directory.active.walRange = some ⟨watermark, history.length⟩)
    (pair : DirectoryPublication.Bindings) (suffix : List WAL.Write)
    (newRange : pair.walRange = some ⟨watermark, (history ++ suffix).length⟩) :
    let selected := history ++ suffix
    let wal := before.appendSelectedView pair selected
    wal.ReadLayout selected ∧ wal.Valid selected ∧ wal.sealed = before.sealed ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encode suffix⟩ := by
  intro selected wal
  have active := layout.extendActiveSuffix pair suffix
  refine ⟨active.1, ?_, rfl, active.2⟩
  intro candidate survives
  have same : candidate = pair := by
    simpa [WalSegmentImage.Selects, wal, WalSegmentImage.appendSelectedView, DirectoryPublication.Image.settled]
      using survives
  subst candidate
  by_cases empty : suffix = []
  · have prior : selected = history := by simp [selected, empty]
    have sameKeeper : wal.active = before.active := by
      change before.active.atHistoryEnd selected = before.active
      unfold WalSegment.atHistoryEnd
      rw [prior, ← layout.activeEnd, ← layout.activeBytes]
    obtain ⟨range, first, original, covers, _, chain⟩ :=
      valid before.directory.active (List.mem_cons_self ..)
    have sameRange := Option.some.inj (original.symm.trans oldRange)
    subst range
    refine ⟨_, first, newRange, covers, by simp [selected, empty], ?_⟩
    rw [prior]
    change WalSegment.Chain history first
      ((before.sealed ++ [wal.active]).filter (fun segment => decide (watermark < segment.last)))
    rw [sameKeeper]
    exact chain
  · obtain ⟨first, covers, _, _, chain, _⟩ := layout.selects valid (List.mem_cons_self ..) oldRange
    let sealed := before.sealed.filter (fun segment => decide (watermark < segment.last))
    have retained : WalSegment.Chain history first (sealed ++ [before.active]) :=
      layout.readDescriptors_filter watermark ▸ chain
    have starts := retained.startsWithin before.active (List.mem_append_right _ (List.mem_singleton_self _))
    have extended := chainAppend retained
      (fun segment member => layout.sealedEndsBeforeHistory starts segment (List.mem_filter.mp member).1) suffix
    have covered : watermark ≤ history.length := (DirectoryPublication.Bindings.walRange_accounting oldRange).2.1
    have positive : 0 < suffix.length := Nat.pos_of_ne_zero (fun zero => empty (List.length_eq_zero_iff.mp zero))
    have needsActive : watermark < selected.length := by
      simp only [selected, List.length_append]
      omega
    have descriptors : wal.afterWatermark watermark = sealed ++ [before.active.atHistoryEnd selected] := by
      change (before.sealed ++ [before.active.atHistoryEnd selected]).filter
        (fun segment => decide (watermark < segment.last)) = _
      simp [List.filter_append, WalSegment.atHistoryEnd, needsActive, sealed]
    exact ⟨_, first, newRange, covers, Nat.le_refl _, descriptors.symm ▸ extended⟩

/-- An append continues the selected gap-free chain after covered seals
have been removed. The active descriptor is included even when the
checkpoint covers its entire previous payload. -/
theorem WalSegmentImage.ReadLayout.afterRetainedAppend
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (valid : before.Valid history) {watermark : Nat}
    (oldRange : before.directory.active.walRange = some ⟨watermark, history.length⟩)
    (pair : DirectoryPublication.Bindings) (event : WAL.Write)
    (newRange : pair.walRange = some ⟨watermark, (history ++ [event]).length⟩) :
    let selected := history ++ [event]
    let wal := before.appendSelectedView pair selected
    wal.ReadLayout selected ∧ wal.Valid selected ∧ wal.sealed = before.sealed ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encodeFrame event⟩ := by
  simpa [WAL.encode] using layout.afterRetainedSuffix valid oldRange pair [event] newRange

/-- Use the exact directory left by a successful publication, including its
staging bindings. Its new absolute marker covers the extended history and
the old checkpoint. The sealed lookup map still names the same bytes. -/
theorem WalSegmentImage.ReadLayout.afterSuccessfulAppend
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (chain : WalSegment.Chain history 0 before.segments) {image : FileImage}
    (kept : image.kept = (before.checkpointReopenFiles before.directory none).kept)
    {watermark : Nat} (oldRange : image.directory.active.walRange = some ⟨watermark, history.length⟩)
    {event : WAL.Write} (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    {effects : WriteEffects} {written : WriteFiles}
    (ran : runWriteEffects history event effects (image.directory.staged .walBoundary) = .ok () written) :
    let selected := history ++ [event]
    let after := resumedAppendFiles image history before.active.first written
    let wal := { before.appendSelectedView after.directory.active selected with directory := after.directory }
    wal.ReadLayout selected ∧ WalSegment.Chain selected 0 wal.segments ∧ wal.Valid selected ∧
      wal.sealed = before.sealed ∧
      wal.active = ⟨before.active.first, selected.length, before.active.bytes ++ WAL.encodeFrame event⟩ ∧
      after.kept = (wal.checkpointReopenFiles wal.directory none).kept ∧
      wal.directory.active.manifest = image.directory.active.manifest ∧
      wal.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selected).size.toUInt64) ∧
      wal.directory.active.walRange = some ⟨watermark, selected.length⟩ ∧
      wal.directory.crashImages = [wal.directory.active] ∧
      after.keeper.active = some wal.active.bytes ∧ after.keeper.crashImages = [some wal.active.bytes] := by
  intro selected after wal
  obtain ⟨nextLayout, nextChain, sealed, nextActive⟩ := layout.afterAcknowledgedAppend chain after.directory.active event
  have starts := chain.startsWithin before.active (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨exactPair, markerDurable, keeperExact, keeperDurable⟩ :=
    WalSegmentCommit.settledSegment_ofSuccess starts ran image.directory.active.manifest
  have sameManifest : wal.directory.active.manifest = image.directory.active.manifest := by
    have exactManifest := congrArg DirectoryPublication.Bindings.manifest exactPair
    exact exactManifest
  have marker : wal.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selected).size.toUInt64) := by
    have exactMarker := congrArg DirectoryPublication.Bindings.walBoundary exactPair
    exact exactMarker
  have old := DirectoryPublication.Bindings.walRange_accounting oldRange
  have checkpoint : selectedCheckpointWatermark wal.directory.active.manifest = some watermark := by
    rw [sameManifest]
    exact old.1
  have covered : watermark ≤ selected.length := Nat.le_trans old.2.1 (by simp [selected])
  have count : (WAL.encode selected).size.toUInt64.toNat = selected.length * WAL.frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' fits, WAL.encode_size, Nat.mul_comm]
  have range : wal.directory.active.walRange = some ⟨watermark, selected.length⟩ :=
    DirectoryPublication.Bindings.walRange_of_counts checkpoint marker (WAL.Boundary.decode_encode _) count covered
  have durable : wal.directory.crashImages = [wal.directory.active] := markerDurable
  have valid : wal.Valid selected := WalSegmentImage.Valid.of_chain nextChain (by
    intro pair chosen
    have same : pair = wal.directory.active := by
      simpa [WalSegmentImage.Selects, durable] using chosen
    rw [same]
    exact ⟨_, range, Nat.zero_le _, Nat.le_refl _⟩)
  have exactKeeper : after.keeper.active = some wal.active.bytes := keeperExact
  have retained : after.kept = (wal.checkpointReopenFiles wal.directory none).kept :=
    (resumedAppendFiles_retains image history before.active.first written).1.trans kept
  refine ⟨⟨nextLayout.ordered, nextLayout.forward, nextLayout.activeEnd, nextLayout.activeBytes⟩,
    nextChain, valid, sealed, nextActive, retained, sameManifest, marker, range, durable, exactKeeper, ?_⟩
  rw [← exactKeeper]
  exact keeperDurable

private theorem WalSegmentImage.ReadLayout.selectedAppendValid
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (valid : before.Valid history) {watermark : Nat}
    (oldRange : before.directory.active.walRange = some ⟨watermark, history.length⟩)
    (event : WAL.Write) {selected : List WAL.Write} (allowed : selected = history ∨ selected = history ++ [event])
    (pair : DirectoryPublication.Bindings) (decoded : pair.walRange = some ⟨watermark, selected.length⟩) :
    (before.appendSelectedView pair selected).Valid selected := by
  rcases allowed with rfl | rfl
  · simpa using (layout.afterRetainedSuffix valid oldRange pair [] (by simpa using decoded)).2.1
  · exact (layout.afterRetainedAppend valid oldRange pair event decoded).2.1

private theorem WalSegmentImage.ReadLayout.afterAppendCutBy
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    {watermark : Nat} (covered : watermark ≤ history.length)
    (event : WAL.Write) (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    (validSelection : ∀ selectedHistory, (selectedHistory = history ∨ selectedHistory = history ++ [event]) →
      ∀ pair : DirectoryPublication.Bindings, pair.walRange = some ⟨watermark, selectedHistory.length⟩ →
        (before.appendSelectedView pair selectedHistory).Valid selectedHistory)
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
      wal.ReadLayout selectedHistory ∧ wal.Valid selectedHistory ∧
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
  have starts : before.active.first ≤ history.length := by
    rw [← layout.activeEnd]
    exact layout.forward before.active (List.mem_append_right _ (by simp))
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
  have selectedStarts : before.active.first ≤ selectedHistory.length := by
    simpa only [first, selectedRange] using target.firstCovered
  have view := layout.atSelectedHistory observed.directory.active selectedHistory selectedStarts
  have decoded : wal.directory.active.walRange = some ⟨watermark, selectedHistory.length⟩ := by
    rw [← selectedRange]
    exact targetPair ▸ target.decoded
  have valid : wal.Valid selectedHistory := validSelection selectedHistory allowed _ decoded
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
  refine ⟨selectedHistory, allowed, targetPair ▸ sameManifest, targetPair ▸ rawMarker, view, valid,
    selected, range, keeper, descriptors, offsets, sealedReads, prepared.keeperPrefix.hasCrashImage, ?_, ?_⟩
  · intro bytes survives
    obtain ⟨suffix, exactBytes⟩ := prepared.keeperPrefix.crashValid bytes survives
    exact ⟨suffix, by rw [exactBytes, activeBytes]⟩
  · change files.later.Beyond canonicalKeeper.range.through
    rw [range, ← selectedRange]
    exact prepared.newer

/-- The observed write cut selects the same validated WAL suffix after
covered segment files have been collected. It keeps the exact original
read layout for the old marker or extends its active segment by one frame
for the newer marker. -/
theorem WalSegmentImage.ReadLayout.afterRetainedAppendCut
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (valid : before.Valid history) {watermark : Nat}
    (oldRange : before.directory.active.walRange = some ⟨watermark, history.length⟩)
    (event : WAL.Write) (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    (effects : WriteEffects) (markerScratch : Option (ByteArray × Bool))
    (observed : ReopenImage) (scratch : Option (ByteArray × Bool)) :
    let cut := (writeFilesAfter (runWriteEffects history event effects markerScratch)).reopenSegment
      before.active.first history before.directory.active.manifest
    AppendReopenObservation cut observed →
    let files := before.appendReopenFiles observed scratch
    ∃ selectedHistory,
      let wal := before.appendSelectedView observed.directory.active selectedHistory
      (selectedHistory = history ∨ selectedHistory = history ++ [event]) ∧
      files.directory.active.manifest = before.directory.active.manifest ∧
      files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selectedHistory).size.toUInt64) ∧
      wal.ReadLayout selectedHistory ∧ wal.Valid selectedHistory ∧
      ∃ selected : CanonicalKeeperLayout files selectedHistory,
        selected.range = ⟨watermark, selectedHistory.length⟩ ∧ selected.keeper = wal.active ∧
        selected.sealed ++ [selected.keeper] = wal.readDescriptors watermark ∧
        selectWalSegmentReads (wal.segments.map (·.first)) watermark =
          some (selected.first, (wal.readDescriptors watermark).map (·.first)) ∧
        (∀ segment ∈ selected.sealed, files.kept segment.first = some segment.bytes) ∧
        files.keeper.crashImages ≠ [] ∧
        (∀ bytes ∈ files.keeper.crashImages, ∃ tail, bytes = some (selected.keeper.bytes ++ tail)) ∧
        files.later.Beyond selected.range.through := by
  have accounting := DirectoryPublication.Bindings.walRange_accounting oldRange
  exact layout.afterAppendCutBy accounting.2.1 event fits
    (fun _ allowed pair decoded => layout.selectedAppendValid valid oldRange event allowed pair decoded)
    effects before.directory.active.manifest markerScratch accounting.1 observed scratch

private theorem WalSegmentImage.ReadLayout.selectedAppendChain
    {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (chain : WalSegment.Chain history 0 before.segments) (event : WAL.Write) {selected : List WAL.Write}
    (allowed : selected = history ∨ selected = history ++ [event]) (pair : DirectoryPublication.Bindings) :
    WalSegment.Chain selected 0 (before.appendSelectedView pair selected).segments := by
  have starts := chain.startsWithin before.active (List.mem_append_right _ (List.mem_singleton_self _))
  have sealedEnd := layout.sealedEndsBeforeHistory starts
  rcases allowed with rfl | rfl
  · simpa only [WalSegmentImage.appendSelectedView, WalSegmentImage.segments, List.append_nil]
      using chainAppend chain sealedEnd []
  · exact chainAppend chain sealedEnd [event]

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
  intro cut seen files
  have valid (selected : List WAL.Write) (allowed : selected = history ∨ selected = history ++ [event])
      (pair : DirectoryPublication.Bindings) (decoded : pair.walRange = some ⟨watermark, selected.length⟩) :
      (before.appendSelectedView pair selected).Valid selected := by
    apply WalSegmentImage.Valid.of_chain (layout.selectedAppendChain chain event allowed pair)
    intro candidate chosen
    have same : candidate = pair := by
      simpa [WalSegmentImage.Selects, WalSegmentImage.appendSelectedView, DirectoryPublication.Image.settled]
        using chosen
    subst candidate
    exact ⟨_, decoded, Nat.zero_le _, Nat.le_refl _⟩
  obtain ⟨history, allowed, manifest, marker, view, _, keeper⟩ :=
    layout.afterAppendCutBy covered event fits valid effects manifest markerScratch checkpoint observed scratch seen
  exact ⟨history, allowed, manifest, marker, view, layout.selectedAppendChain chain event allowed _, keeper⟩

end Alvoki.Storage
