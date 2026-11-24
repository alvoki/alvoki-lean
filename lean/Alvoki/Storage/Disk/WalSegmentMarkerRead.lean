import Alvoki.Storage.Disk.WalSegmentRepair

namespace Alvoki.Storage
open WAL (frameSize)

theorem selectWalSegmentReadsThrough_exact {offsets : List Nat} {watermark through first : Nat}
    {files : List (Nat × ByteArray)}
    (selected : selectWalSegmentReads offsets watermark = some (first, files.map (·.1))) :
    selectWalSegmentReadsThrough offsets watermark through = some
      ((files.takeWhile fun file => decide (file.1 ≤ through)).map (·.1),
       (files.dropWhile fun file => decide (file.1 ≤ through)).map (·.1)) := by
  simp [selectWalSegmentReadsThrough, selected, List.takeWhile_map, List.dropWhile_map, Function.comp_def,
    bind, Option.bind, pure]

/-- The marker-limited native route interpreted by the same primitive
listing, metadata and binary read reports as the complete reader. -/
theorem OpenPathReadReports.readWalSegmentsThroughWith_reports (reports : OpenPathReadReports)
    (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (listing : Except IO.Error (Array IO.FS.DirEntry)) :
    readWalSegmentsThroughWith directory watermark length (fun _ => listing)
        (fun path => pure (reports.lstat path)) reports.readBin =
      (do
        let through := length.toNat / frameSize
        if length.toNat % frameSize = 0 ∧ watermark ≤ through then
          let entries ← listing
          let offsets ← reports.walSegmentOffsets directory (entries.toList.map (·.fileName))
          let some (required, newer) := selectWalSegmentReadsThrough offsets watermark through
            | throw (IO.userError "no WAL segment covers the checkpoint watermark")
          let payloads ← reports.readWalSegmentPayloads directory required
          pure ⟨required.zip payloads, newer⟩
        else throw (IO.userError "invalid absolute WAL segment marker")) := by
  have probe : probeWalSegmentWith directory (fun path => pure (reports.lstat path)) =
      reports.probeWalSegment directory := by
    funext first
    simp only [probeWalSegmentWith, OpenPathReadReports.probeWalSegment, pure, Except.pure, bind, Except.bind]
    cases classifyWalSegmentLookup (directory.file (.walSegment first)) first
      (reports.lstat (directory.file (.walSegment first))) <;> rfl
  simp only [readWalSegmentsThroughWith, probe, walSegmentOffsets, readWalSegmentPayloads]
  rfl

private theorem WalSegmentSpans.takeThrough {through : Nat} {files : List (Nat × ByteArray)}
    (spans : WalSegmentSpans through files) (starts : (files.head?.any fun file => decide (file.1 ≤ through)) = true) :
    WalSegmentSpans through (files.takeWhile fun file => decide (file.1 ≤ through)) := by
  induction spans with
  | @active first bytes covered =>
    have needed : first ≤ through := by simpa using starts
    simpa [List.takeWhile, needed] using (WalSegmentSpans.active (first := first) covered)
  | @sealed first next nextBytes remaining bytes forward size rest later =>
    have needed : first ≤ through := by simpa using starts
    by_cases nextNeeded : next ≤ through
    · have good := later (by simpa using nextNeeded)
      have tail : WalSegmentSpans through
          ((next, nextBytes) :: remaining.takeWhile fun file => decide (file.1 ≤ through)) := by
        simpa [List.takeWhile, nextNeeded] using good
      simpa [List.takeWhile, needed, nextNeeded] using WalSegmentSpans.sealed forward size tail
    · have enough : (through - first) * frameSize ≤ bytes.size := by
        rw [size]
        exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.le_of_lt (Nat.lt_of_not_ge nextNeeded)) _)
      simpa [List.takeWhile, needed, nextNeeded] using (WalSegmentSpans.active (first := first) enough)

theorem checkSelectedWalSegmentSpans_takeThrough {through : Nat} {files : List (Nat × ByteArray)}
    (checked : checkWalSegmentSpans through files = true) :
    checkSelectedWalSegmentSpans through (files.takeWhile fun file => decide (file.1 ≤ through)) = true := by
  obtain ⟨⟨first, rest, rfl, starts⟩, spans⟩ := (checkWalSegmentSpans_iff ..).mp checked
  have selectedSpans := spans.takeThrough (by simpa using starts)
  rw [checkSelectedWalSegmentSpans, Bool.and_eq_true]
  refine ⟨List.all_takeWhile, (checkWalSegmentSpans_iff ..).mpr ⟨?_, selectedSpans⟩⟩
  exact ⟨first, rest.takeWhile (fun file => decide (file.1 ≤ through)), by simp [List.takeWhile, starts], starts⟩

private theorem WalSegmentSpans.covers {through : Nat} {files : List (Nat × ByteArray)}
    (spans : WalSegmentSpans through files) :
    (through - (files.head?.map Prod.fst).getD through) * frameSize ≤ (walSegmentPayloadBytes files).size := by
  induction spans with
  | active covered => simpa [walSegmentPayloadBytes] using covered
  | @sealed first next nextBytes remaining bytes forward size rest later =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at later ⊢
    change (through - first) * frameSize ≤
      (bytes ++ walSegmentPayloadBytes ((next, nextBytes) :: remaining)).size
    rw [ByteArray.size_append, size]
    simp only [WAL.frameSize] at later ⊢
    omega

private theorem select_covered_extract (length : UInt64) (bytes : ByteArray) (enough : length.toNat ≤ bytes.size) :
    WAL.Boundary.select length bytes = if length.toNat % frameSize != 0 then .error "WAL boundary is not frame aligned"
      else .ok (bytes.extract 0 length.toNat) := by
  unfold WAL.Boundary.select
  simp only [Nat.not_lt.mpr enough, ↓reduceIte]
  split
  · rfl
  · split
    · rename_i same
      rw [← same, ByteArray.extract_zero_size]
    · rfl

private theorem recoverRetainedMarked_append_covered (base : PackedTable) (first : Nat) (length : UInt64)
    (bytes later : ByteArray) (enough : length.toNat - first * frameSize ≤ bytes.size) :
    WAL.Boundary.recoverRetainedMarked base first length (bytes ++ later) =
      WAL.Boundary.recoverRetainedMarked base first length bytes := by
  have selection : WAL.Boundary.selectRetained first length (bytes ++ later) =
      WAL.Boundary.selectRetained first length bytes := by
    by_cases earlier : length.toNat < first * frameSize
    · simp [WAL.Boundary.selectRetained, earlier]
    · simp only [WAL.Boundary.selectRetained, earlier, ↓reduceIte]
      let count := (length.toNat - first * frameSize).toUInt64
      have exactCount : count.toNat = length.toNat - first * frameSize :=
        UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le ..) length.toNat_lt_size)
      have within : count.toNat ≤ bytes.size := exactCount.symm ▸ enough
      have full : count.toNat ≤ (bytes ++ later).size := by
        rw [ByteArray.size_append]
        exact Nat.le_trans within (Nat.le_add_right ..)
      rw [select_covered_extract _ _ full, select_covered_extract _ _ within]
      rw [ByteArray.extract_append, Nat.zero_sub, Nat.sub_eq_zero_of_le within]
      simp
  simp [WAL.Boundary.recoverRetainedMarked, selection]

private theorem recoverRetainedMarked_extract_covered (base : PackedTable) (first : Nat) (length : UInt64)
    (bytes : ByteArray) (enough : length.toNat - first * frameSize ≤ bytes.size) :
    WAL.Boundary.recoverRetainedMarked base first length (bytes.extract 0 (length.toNat - first * frameSize)) =
      WAL.Boundary.recoverRetainedMarked base first length bytes := by
  let count := length.toNat - first * frameSize
  have within : count ≤ bytes.size := enough
  have split : bytes.extract 0 count ++ bytes.extract count bytes.size = bytes := by
    simp [ByteArray.extract_append_extract, Nat.max_eq_right within]
  have size : (bytes.extract 0 count).size = count := by simp [Nat.min_eq_left within]
  have same := recoverRetainedMarked_append_covered base first length (bytes.extract 0 count)
    (bytes.extract count bytes.size) (Nat.le_of_eq size.symm)
  rw [split] at same
  exact same.symm

/-- The validated required vector supplies the exact marked replay for
any later bytes. In particular it needs no read or contiguity premise for
the files strictly after the keeper. -/
theorem recoverMarkedWalSegments_eq_retained (base : PackedTable) (length : UInt64) (first : Nat)
    (bytes : ByteArray) (rest : List (Nat × ByteArray)) (later : ByteArray)
    (aligned : length.toNat % frameSize = 0)
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true) :
    recoverMarkedWalSegments base length ((first, bytes) :: rest) =
      WAL.Boundary.recoverRetainedMarked base first length (walSegmentPayloadBytes ((first, bytes) :: rest) ++ later) := by
  have sizes : checkWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true := by
    have accepted := checked
    rw [checkSelectedWalSegmentSpans, Bool.and_eq_true] at accepted
    exact accepted.2
  have spans := ((checkWalSegmentSpans_iff ..).mp sizes).2
  have enough := spans.covers
  simp only [List.head?_cons, Option.map_some, Option.getD_some] at enough
  have exactMarker : (length.toNat / frameSize) * frameSize = length.toNat := by
    simp only [WAL.frameSize] at aligned ⊢
    omega
  have enoughBytes : length.toNat - first * frameSize ≤ (walSegmentPayloadBytes ((first, bytes) :: rest)).size := by
    rw [← exactMarker, ← Nat.sub_mul]
    exact enough
  rw [recoverMarkedWalSegments_eq_extract base length first bytes rest checked]
  rw [recoverRetainedMarked_extract_covered _ _ _ _ enoughBytes]
  exact (recoverRetainedMarked_append_covered base first length _ later enoughBytes).symm

private theorem walSegmentPayloadBytes_append (files later : List (Nat × ByteArray)) :
    walSegmentPayloadBytes (files ++ later) =
      walSegmentPayloadBytes files ++ walSegmentPayloadBytes later := by
  induction files with
  | nil => simp [walSegmentPayloadBytes]
  | cons file files ih =>
    change file.2 ++ walSegmentPayloadBytes (files ++ later) =
      (file.2 ++ walSegmentPayloadBytes files) ++ walSegmentPayloadBytes later
    rw [ih, ByteArray.append_assoc]

/-- From an admitted complete vector, the limited reads give the same
exact replay and retained prefix as reading every selected inventory entry. -/
theorem recoverMarkedWalSegments_takeThrough_eq (base : PackedTable) (length : UInt64)
    (full : List (Nat × ByteArray)) (aligned : length.toNat % frameSize = 0)
    (checked : checkWalSegmentSpans (length.toNat / frameSize) full = true) :
    recoverMarkedWalSegments base length
        (full.takeWhile fun file => decide (file.1 ≤ length.toNat / frameSize)) =
      WAL.Boundary.recoverRetainedMarked base ((full.head?.map Prod.fst).getD 0) length
        (walSegmentPayloadBytes full) := by
  let needed (file : Nat × ByteArray) : Bool := decide (file.1 ≤ length.toNat / frameSize)
  obtain ⟨⟨⟨first, bytes⟩, rest, rfl, begins⟩, _⟩ := (checkWalSegmentSpans_iff ..).mp checked
  have kept : ((first, bytes) :: rest).takeWhile needed = (first, bytes) :: rest.takeWhile needed := by
    simp [List.takeWhile, needed, begins]
  have accepted := checkSelectedWalSegmentSpans_takeThrough checked
  change checkSelectedWalSegmentSpans _ (((first, bytes) :: rest).takeWhile needed) = true at accepted
  rw [kept] at accepted
  have joined := congrArg walSegmentPayloadBytes
    (List.takeWhile_append_dropWhile (p := needed) (l := (first, bytes) :: rest))
  rw [walSegmentPayloadBytes_append, kept] at joined
  change recoverMarkedWalSegments base length (((first, bytes) :: rest).takeWhile needed) =
    WAL.Boundary.recoverRetainedMarked base first length (walSegmentPayloadBytes ((first, bytes) :: rest))
  rw [kept, recoverMarkedWalSegments_eq_retained _ _ _ _ _
    (walSegmentPayloadBytes (((first, bytes) :: rest).dropWhile needed)) aligned accepted, joined]

/-- The exact selected retained-layout replay result still holds for a
physically validated marker-limited read. Omitted bytes are only a proof
witness, so recovery does not need to observe them. -/
theorem WalSegmentRecovery.recoversMarkerLimitedReadBytes
    {image : WalSegmentImage} {pair : DirectoryPublication.Bindings} {range : MarkedWalRange}
    {history : List WAL.Write} {base table : PackedTable} {earlier first : Nat}
    (recovery : WalSegmentRecovery image pair range history base earlier table)
    (selected : pair.walRange = some range) (starts : first ≤ range.watermark) (bounded : range.through ≤ history.length)
    (baseClock : base.committed.toNat = range.watermark) (ordered : WAL.OrdinalsFrom 1 history)
    {bytes omitted tail : ByteArray} {rest : List (Nat × ByteArray)}
    (checked : checkSelectedWalSegmentSpans range.through ((first, bytes) :: rest) = true)
    (readExact : walSegmentPayloadBytes ((first, bytes) :: rest) ++ omitted = WAL.encode (history.drop first) ++ tail) :
    ∃ marker length, pair.walBoundary = some marker ∧ WAL.Boundary.decode marker = .ok length ∧
      recoverMarkedWalSegments base length ((first, bytes) :: rest) =
        .ok (WAL.encode ((history.take range.through).drop first), table) := by
  obtain ⟨marker, length, visible, decoded, recovers⟩ :=
    recovery.recoversReadBytes selected starts bounded baseClock ordered readExact
  obtain ⟨observed, observedLength, _, exactVisible, exactDecoded, markerCount, _⟩ := recovery.marked
  have sameMarker : observed = marker := Option.some.inj (exactVisible.symm.trans visible)
  subst observed
  have sameLength : observedLength = length := Except.ok.inj (exactDecoded.symm.trans decoded)
  subst observedLength
  have aligned : length.toNat % frameSize = 0 := by rw [markerCount, Nat.mul_mod_left]
  have count : length.toNat / frameSize = range.through := by
    rw [markerCount, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  refine ⟨marker, length, visible, decoded, ?_⟩
  rw [recoverMarkedWalSegments_eq_retained _ _ _ _ _ omitted aligned (count.symm ▸ checked)]
  exact recovers

end Alvoki.Storage
