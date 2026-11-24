import Alvoki.Storage.Disk.WalSegmentFirstReplay
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects
import Alvoki.Storage.Disk.WalSegmentRotation

namespace Alvoki.Storage.WalSegmentRotation

open System
open WalSegmentRepair
open WAL (frameSize)

private theorem CanRotate.readLayout {image : WalSegmentImage} {history : List WAL.Write}
    (rotation : CanRotate image history) (layout : image.ReadLayout history) :
    image.rotated.ReadLayout history := by
  have segments : image.rotated.segments = image.segments ++ [image.rotated.active] := rfl
  have endBound : ∀ segment ∈ image.segments, segment.first < image.active.last ∧
      segment.last ≤ image.active.last := by
    intro segment present
    rcases List.mem_append.mp present with sealed | active
    · have before := (List.pairwise_append.mp layout.ordered).2.2 segment sealed image.active (by simp)
      exact ⟨Nat.lt_trans before.1 rotation.nonempty, Nat.le_trans before.2 (Nat.le_of_lt rotation.nonempty)⟩
    · obtain rfl := List.mem_singleton.mp active
      exact ⟨rotation.nonempty, Nat.le_refl _⟩
  refine ⟨?_, ?_, rotation.atEnd, ?_⟩
  · rw [segments]
    refine List.pairwise_append.mpr ⟨layout.ordered, by simp, ?_⟩
    intro left old right new
    obtain rfl := List.mem_singleton.mp new
    exact endBound left old
  · intro segment present
    rw [segments] at present
    rcases List.mem_append.mp present with old | new
    · exact layout.forward segment old
    · obtain rfl := List.mem_singleton.mp new
      exact Nat.le_refl _
  · change ByteArray.empty = WAL.encode (history.drop image.active.last)
    rw [rotation.atEnd, List.drop_length]
    rfl

theorem State.visibleReadLayout (state : State) {image : WalSegmentImage} {history : List WAL.Write}
    (rotation : CanRotate image history) (layout : image.ReadLayout history) :
    (state.visible image).ReadLayout history := by
  let current : WalSegmentImage := { image with directory := state.metadata }
  have observed : current.ReadLayout history :=
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩
  have canRotate : CanRotate current history := ⟨rotation.nonempty, rotation.atEnd, rotation.sealedBefore⟩
  by_cases absent : state.successor = .absent
  · simpa only [visible, absent, ite_true] using observed
  · simpa only [visible, absent, ite_false] using canRotate.readLayout observed

theorem State.settleForReopen_keeper (state : State) (image : WalSegmentImage) :
    (state.settleForReopen.visible image).active = (state.visible image).active := by
  by_cases absent : state.successor = .absent <;> simp [settleForReopen, visible, absent] <;> rfl

theorem State.settleForReopen_survives (state : State) {present : Bool}
    (survives : state.settleForReopen.successor.MaySurvive present) :
    present = state.observeSuccessor.isSome := by
  by_cases absent : state.successor = .absent <;>
    simpa [State.settleForReopen, State.observeSuccessor, absent, Binding.MaySurvive] using survives

/-- This fixed-keeper image is only used after the binding settles. Every
preceding descriptor still names its exact immutable bytes. -/
def State.settledReopenImage (state : State) (image : WalSegmentImage) : FileImage :=
  let layout := state.settleForReopen.visible image
  ⟨layout.directory, fun first => (layout.sealed.find? (fun segment => segment.first == first)).map (·.bytes),
    .settled (some layout.active.bytes), .settled []⟩

/-- The plan still describes the visible preflight keeper once the
directory effect has applied. This also holds after a reported error
following the effect, when open has not returned a writer. -/
theorem State.preparedAfterReopenBarrier (state : State) {image : WalSegmentImage} {history : List WAL.Write}
    (layout : (state.visible image).ReadLayout history) {range : MarkedWalRange}
    (selected : state.metadata.active.walRange = some range) (atEnd : range.through = history.length) :
    let active := (state.visible image).active
    let plan : Plan := ⟨range.through, active.first, [], active.bytes⟩
    ∃ target, Prepared (state.settledReopenImage image) target plan ∧
      plan.alignedWithoutPrune = true := by
  intro active plan
  have through : active.last = range.through := layout.activeEnd.trans atEnd.symm
  have first : active.first ≤ range.through :=
    through ▸ layout.forward active (List.mem_append_right _ (List.mem_singleton_self _))
  have size : active.bytes.size = (range.through - active.first) * frameSize := by
    rw [layout.activeBytes, WAL.encode_size, List.length_drop, atEnd, Nat.mul_comm]
  have binding : (state.settledReopenImage image).directory = state.metadata.syncDirectory := by
    rw [settledReopenImage, State.visible_metadata]
    rfl
  have bytes : (state.settledReopenImage image).keeper = .settled (some active.bytes) := by
    simp only [settledReopenImage, State.settleForReopen_keeper]
    rfl
  let target : Target := ⟨state.metadata.active, range, selected, active.first, first, active.bytes, size⟩
  have later : (state.settledReopenImage image).later.Beyond range.through := by
    simp [settledReopenImage, LaterNames.settled, LaterNames.Beyond]
  have prepared : Prepared (state.settledReopenImage image) target plan :=
    ⟨by rw [binding]; rfl, bytes ▸ Publication.Image.settled_valid target.acceptsTrimmed, later,
      rfl, rfl, rfl, by rw [bytes]; rfl⟩
  refine ⟨target, prepared, ?_⟩
  simp [Plan.alignedWithoutPrune, prepared.valid, plan, Plan.keeperSize, size]

/-- The aligned finish executes the actual shared open route on both
reported outcomes of the first directory barrier. An error after its
effect still settles the name and skips the keeper sync. -/
theorem State.finishAfterRotation {state : State} {image : WalSegmentImage} {history : List WAL.Write}
    (layout : (state.visible image).ReadLayout history) {range : MarkedWalRange}
    (selected : state.metadata.active.walRange = some range) (atEnd : range.through = history.length)
    (directory : DiskDirectory)
    (remove : FilePath → EStateM IO.Error State (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error State Unit)
    (sync : Array FilePath → EStateM IO.Error State Unit)
    (rename : FilePath → FilePath → EStateM IO.Error State Unit) :
    let active := (state.visible image).active
    let plan : Plan := ⟨range.through, active.first, [], active.bytes⟩
    (match sync #[directory.path] state with
      | .ok _ after => after = state.settleForReopen
      | .error _ after => after = state ∨ after = state.settleForReopen) →
    (match sync #[directory.file (.walSegment active.first)] state.settleForReopen with
      | .ok _ after | .error _ after => after = state.settleForReopen) →
    ∃ target, Prepared (state.settledReopenImage image) target plan ∧
      (∀ error after, sync #[directory.path] state = .error error after →
        finishMarkedOpen directory plan remove write sync rename state = .error error after) ∧
      (match finishMarkedOpen directory plan remove write sync rename state with
      | .ok _ after => after = state.settleForReopen ∧ (state.settledReopenImage image).Ready target
      | .error _ after => after = state ∨ after = state.settleForReopen) := by
  intro active plan directoryReport keeperReport
  obtain ⟨target, prepared, aligned⟩ := state.preparedAfterReopenBarrier layout selected atEnd
  change plan.alignedWithoutPrune = true at aligned
  change Prepared (state.settledReopenImage image) target plan at prepared
  refine ⟨target, prepared, ?_, ?_⟩
  · intro error after failed
    simp only [finishMarkedOpen, aligned, ite_true, Bind.bind, EStateM.bind, failed]
  simp only [finishMarkedOpen, aligned, ite_true, Bind.bind, EStateM.bind]
  cases directorySync : sync #[directory.path] state with
  | error error after =>
    simpa only [directorySync] using directoryReport
  | ok result after =>
    cases result
    rw [directorySync] at directoryReport
    subst after
    change match sync #[directory.file (.walSegment active.first)] state.settleForReopen with
      | .ok _ after => after = state.settleForReopen ∧ (state.settledReopenImage image).Ready target
      | .error _ after => after = state ∨ after = state.settleForReopen
    cases keeperSync : sync #[directory.file (.walSegment active.first)] state.settleForReopen with
    | error error after => exact Or.inr (by simpa only [keeperSync] using keeperReport)
    | ok result after =>
      have settled : (state.settledReopenImage image).directory.crashImages =
          [(state.settledReopenImage image).directory.active] := by
        rw [settledReopenImage, State.visible_metadata]
        rfl
      have keeper := prepared.aligned (by
        have exactSize : plan.keeperBytes.size = plan.keeperSize := by
          have facts := aligned
          simp only [Plan.alignedWithoutPrune, Bool.and_eq_true, beq_iff_eq] at facts
          exact facts.2
        omega)
      exact ⟨by simpa only [keeperSync] using keeperReport,
        prepared.pair, settled.trans (congrArg (fun pair => [pair]) prepared.pair), keeper,
        by rw [← keeper]; rfl, ⟨rfl, rfl⟩⟩

private theorem splitAtMarker {offsets : List Nat} {through : Nat}
    (needed : ∀ offset ∈ offsets, offset ≤ through) :
    offsets.takeWhile (fun first => decide (first ≤ through)) = offsets ∧
      offsets.dropWhile (fun first => decide (first ≤ through)) = [] := by
  induction offsets with
  | nil => exact ⟨rfl, rfl⟩
  | cons first later ih =>
    obtain ⟨take, drop⟩ := ih fun offset member => needed offset (List.mem_cons_of_mem _ member)
    simp [List.takeWhile, List.dropWhile, needed first (List.mem_cons_self ..), take, drop]

/-- The visible layout after a rotation cut determines the same marked
replay as the admitted complete history. The actual reader chooses the
covering start and the last present file at the marker. -/
theorem Trace.replaysVisible {image : WalSegmentImage} {state : State} {history : List WAL.Write}
    (trace : Trace image state) (rotation : CanRotate image history) (layout : image.ReadLayout history)
    (valid : image.Valid history) {range : MarkedWalRange}
    (selected : state.metadata.active.walRange = some range) (atEnd : range.through = history.length)
    {count : UInt64} (absolute : count.toNat = history.length * frameSize)
    {base table : PackedTable} (clock : base.committed.toNat = range.watermark)
    (ordered : WAL.OrdinalsFrom 1 history) (replay : recoverSelected base (WAL.encode history) = .ok table) :
    let current := state.visible image
    let files := (current.readDescriptors range.watermark).map (fun segment => (segment.first, segment.bytes))
    ∃ first,
      selectWalSegmentReadsThrough (current.segments.map (·.first)) range.watermark range.through =
        some (files.map Prod.fst, []) ∧
      files.getLast? = some (current.active.first, current.active.bytes) ∧
      recoverMarkedWalSegments base count files = .ok (WAL.encode (history.drop first), table) := by
  intro current files
  have currentLayout : current.ReadLayout history := state.visibleReadLayout rotation layout
  have currentValid : current.Valid history := (trace.preservesRecovery rotation valid).1
  have chosen : current.Selects state.metadata.active := by
    change state.metadata.active ∈ (state.visible image).directory.active :: (state.visible image).directory.crashImages
    rw [state.visible_metadata]
    exact List.mem_cons_self ..
  obtain ⟨first, starts, _, read, chain, _⟩ := currentLayout.selects currentValid chosen selected
  obtain ⟨sealed, split⟩ := current.readDescriptors_endsActive range.watermark
  have fileStarts : files.map Prod.fst = (current.readDescriptors range.watermark).map (·.first) := by
    simp [files, List.map_map, Function.comp_def]
  have exactRead : selectWalSegmentReads (current.segments.map (·.first)) range.watermark =
      some (first, files.map Prod.fst) := by rw [fileStarts]; exact read
  have allNeeded : ∀ start ∈ files.map Prod.fst, start ≤ range.through := by
    intro start occurs
    rw [fileStarts] at occurs
    obtain ⟨segment, requested, rfl⟩ := List.mem_map.mp occurs
    have member : segment ∈ current.segments := by
      by_cases needed : range.watermark < current.active.last
      · rw [WalSegmentImage.readDescriptors, ite_eq_left needed] at requested
        exact (List.mem_filter.mp requested).1
      · rw [WalSegmentImage.readDescriptors, ite_eq_right needed] at requested
        exact List.mem_append_right _ requested
    have forward := currentLayout.forward segment member
    have lastThrough : current.active.last = range.through := currentLayout.activeEnd.trans atEnd.symm
    rw [← lastThrough]
    rcases List.mem_append.mp member with older | last
    · have before := (List.pairwise_append.mp currentLayout.ordered).2.2 segment older current.active (by simp)
      exact Nat.le_trans forward (Nat.le_trans before.2
        (currentLayout.forward current.active (List.mem_append_right _ (List.mem_singleton_self _))))
    · obtain rfl := List.mem_singleton.mp last
      exact forward
  obtain ⟨take, drop⟩ := splitAtMarker allNeeded
  have routed := selectWalSegmentReadsThrough_exact exactRead (through := range.through)
  have selectedOffsets : selectWalSegmentReadsThrough (current.segments.map (·.first))
      range.watermark range.through = some (files.map Prod.fst, []) := by
    simp only [List.takeWhile_map, List.dropWhile_map, Function.comp_def] at take drop
    rw [routed, take, drop]
  have filesExact : files = sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(current.active.first, current.active.bytes)] := by
    simp [files, split]
  have exactChain : WalSegment.Chain history first (sealed ++ [current.active]) := split ▸ chain
  have decoded := exactChain.replaysMarked ByteArray.empty absolute (clock.symm ▸ starts) ordered replay
  refine ⟨first, selectedOffsets, by rw [filesExact, List.getLast?_concat], ?_⟩
  simpa only [filesExact, ByteArray.append_empty] using decoded

/-- Both admitted power-loss choices before name settlement replay the
same table from the same checkpoint and marker. Their physical retained
bytes can differ when the checkpoint is exactly at the new start. -/
theorem Trace.replaysAfterReopenCrash {image : WalSegmentImage} {state : State} {history : List WAL.Write}
    (trace : Trace image state) (rotation : CanRotate image history) (layout : image.ReadLayout history)
    (valid : image.Valid history) {pair : DirectoryPublication.Bindings} (survives : pair ∈ state.metadata.crashImages)
    {range : MarkedWalRange} (selected : pair.walRange = some range) (atEnd : range.through = history.length)
    {base : PackedTable} (clock : base.committed.toNat = range.watermark) (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ marker count table,
      pair.walBoundary = some marker ∧ WAL.Boundary.decode marker = .ok count ∧
      table.committed.toNat = history.length ∧
      recoverSelected base (WAL.encode history) = .ok table ∧
      ∀ present, state.successor.MaySurvive present →
        let crashed : State := ⟨.settled pair, if present then .durable else .absent⟩
        let current := crashed.visible image
        let files := (current.readDescriptors range.watermark).map (fun segment => (segment.first, segment.bytes))
        ∃ first,
          selectWalSegmentReadsThrough (current.segments.map (·.first)) range.watermark range.through =
            some (files.map Prod.fst, []) ∧
          files.getLast? = some (current.active.first, current.active.bytes) ∧
          recoverMarkedWalSegments base count files = .ok (WAL.encode (history.drop first), table) := by
  obtain ⟨_, covered, marker, count, visible, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting selected
  have splits := List.take_append_drop range.watermark history
  have coveredLength : (history.take range.watermark).length = base.committed.toNat := by
    simp [clock, Nat.min_eq_left (atEnd ▸ covered)]
  obtain ⟨table, replay, committed⟩ := recoverSelected_encoded_complete base
    (history.take range.watermark) (history.drop range.watermark) (splits.symm ▸ ordered) coveredLength
  rw [splits] at replay
  rw [← List.length_append, splits] at committed
  refine ⟨marker, count, table, visible, decoded, committed, replay, ?_⟩
  intro present allowed crashed
  have crash : Trace image crashed := .crash trace pair survives allowed
  exact crash.replaysVisible rotation layout valid selected atEnd (atEnd ▸ absolute) clock ordered replay

end Alvoki.Storage.WalSegmentRotation
