import Alvoki.Storage.Disk.WAL.WalSegmentReplay

namespace Alvoki.Storage

open WAL (frameSize)

/-- Moving replay between consecutive chunks drops checkpoint-covered events
in exactly the same order as replay of their concatenated event list. -/
theorem replay_drop_append (base : PackedTable) (first : Nat) (left right : List WAL.Write) :
    replay base ((left ++ right).drop (base.committed.toNat - first)) = (do
      let table ← replay base (left.drop (base.committed.toNat - first))
      replay table (right.drop (table.committed.toNat - (first + left.length)))) := by
  rw [List.drop_append]
  cases played : replay base (left.drop (base.committed.toNat - first)) with
  | error message =>
    simp only [replay, List.foldlM_append] at played ⊢
    rw [played]
    rfl
  | ok table =>
    rw [replay_append played]
    have advanced := replay_committed_count (left.drop (base.committed.toNat - first)) played
    rw [List.length_drop] at advanced
    have dropCount :
        table.committed.toNat - (first + left.length) = base.committed.toNat - first - left.length := by
      omega
    simp [Bind.bind, Except.bind, dropCount]

/-- The outer result stores the first decoder error, which takes precedence
over the replay error stored in the inner result. Each successful step replays
only the events newer than the table's current watermark. -/
def replayWalChunk (state : Except String PackedTable) (first : Nat) (bytes : ByteArray) :
    Except String (Except String PackedTable) := do
  let events ← WAL.decodeOrdinalsFrom (first + 1) bytes
  pure (state.bind fun table => replay table (events.drop (table.committed.toNat - first)))

def replayWalChunks (first : Nat) (state : Except String PackedTable) :
    List ByteArray → Except String (Except String PackedTable)
  | [] => .ok state
  | bytes :: rest => do
    let next ← replayWalChunk state first bytes
    replayWalChunks (first + bytes.size / frameSize) next rest

/-- The serial fold preserves chronological decode errors and the complete
checkpoint-relative replay result. The initial inner result may already
hold a replay error from an earlier chunk. -/
theorem replayWalChunks_eq_concat (first : Nat) (state : Except String PackedTable) (chunks : List ByteArray)
    (aligned : ∀ bytes ∈ chunks, bytes.size % frameSize = 0) :
    replayWalChunks first state chunks = (do
      let events ← WAL.decodeOrdinalsFrom (first + 1) (chunks.foldr (· ++ ·) ByteArray.empty)
      pure (state.bind fun table => replay table (events.drop (table.committed.toNat - first)))) := by
  induction chunks generalizing first state with
  | nil =>
    have decoded : WAL.decodeOrdinalsFrom (first + 1) ByteArray.empty = .ok [] := rfl
    cases state <;> simp [replayWalChunks, decoded, replay, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cons bytes rest ih =>
    rw [replayWalChunks, replayWalChunk, List.foldr_cons,
      WAL.decodeOrdinalsFrom_append _ _ _ (aligned bytes (by simp))]
    have nextOrdinal : first + 1 + bytes.size / frameSize = first + bytes.size / frameSize + 1 := by omega
    rw [nextOrdinal]
    cases left : WAL.decodeOrdinalsFrom (first + 1) bytes with
    | error => rfl
    | ok prior =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih _ _ (fun chunk member => aligned chunk (List.mem_cons_of_mem _ member))]
      have size := WAL.decodeOrdinalsFrom_length left
      rw [← size]
      cases WAL.decodeOrdinalsFrom (first + prior.length + 1) (rest.foldr (· ++ ·) ByteArray.empty) with
      | error => rfl
      | ok later =>
        cases state with
        | error => rfl
        | ok base => exact congrArg Except.ok (replay_drop_append base first prior later).symm

/-- Keep the final committed-count guard from the retained byte decoder. -/
def finishWalChunkReplay (through : Nat) (decoded : Except String (Except String PackedTable)) :
    Except String PackedTable := do
  let replayed ← decoded
  let table ← replayed
  if table.committed.toNat == through then .ok table
  else .error "selected WAL frame count disagrees with the recovered sequence"

theorem finishWalChunkReplay_eq_retained (base : PackedTable) (first through : Nat) (chunks : List ByteArray)
    (aligned : ∀ bytes ∈ chunks, bytes.size % frameSize = 0)
    (count : through = first + (chunks.foldr (· ++ ·) ByteArray.empty).size / frameSize) :
    finishWalChunkReplay through (replayWalChunks first (.ok base) chunks) =
      recoverRetainedFrom base first (chunks.foldr (· ++ ·) ByteArray.empty) := by
  rw [finishWalChunkReplay, replayWalChunks_eq_concat _ _ _ aligned, recoverRetainedFrom, count]
  cases WAL.decodeOrdinalsFrom (first + 1) (chunks.foldr (· ++ ·) ByteArray.empty) <;> rfl

private theorem WalSegmentSpans.replayWalChunks_eq_foldlM {through : Nat} {files : List (Nat × ByteArray)}
    (spans : WalSegmentSpans through files) (state : Except String PackedTable) :
    replayWalChunks (files.head?.map Prod.fst |>.getD through) state (files.map Prod.snd) =
      files.foldlM (fun current file => replayWalChunk current file.1 file.2) state := by
  induction spans generalizing state with
  | active => rfl
  | @sealed first next nextBytes remaining bytes forward size _ ih =>
    have nextOffset : first + bytes.size / frameSize = next := by
      rw [size, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
      omega
    simp only [List.head?_cons, Option.map_some, Option.getD_some, List.map_cons,
      replayWalChunks, List.foldlM_cons, nextOffset] at ih ⊢
    cases replayWalChunk state first bytes with
    | error => rfl
    | ok nextState => exact ih nextState

private theorem walSegmentPayloadBytes_eq_fold (files : List (Nat × ByteArray)) :
    walSegmentPayloadBytes files = (files.map Prod.snd).foldr (· ++ ·) ByteArray.empty := by
  exact List.foldr_map.symm

private theorem WalSegmentSpans.exactPayloads {through : Nat} {files : List (Nat × ByteArray)}
    (spans : WalSegmentSpans through files)
    (within : ∀ file ∈ files, file.1 ≤ through)
    (keeper : ∀ file, files.getLast? = some file → file.2.size = (through - file.1) * frameSize) :
    (∀ bytes ∈ files.map Prod.snd, bytes.size % frameSize = 0) ∧
      (walSegmentPayloadBytes files).size = (through - (files.head?.map Prod.fst).getD through) * frameSize := by
  induction spans with
  | @active start bytes _ =>
    have size := keeper (start, bytes) rfl
    constructor
    · simp [size, Nat.mul_mod_left]
    · simp [walSegmentPayloadBytes, size]
  | @sealed first next nextBytes remaining bytes forward size _ ih =>
    have remainingWithin (file : Nat × ByteArray) (member : file ∈ (next, nextBytes) :: remaining) :=
      within file (List.mem_cons_of_mem _ member)
    have ⟨aligned, restSize⟩ := ih remainingWithin (by simpa using keeper)
    constructor
    · simpa [List.map_cons, List.forall_mem_cons, size, Nat.mul_mod_left] using aligned
    · change (bytes ++ walSegmentPayloadBytes ((next, nextBytes) :: remaining)).size = (through - first) * frameSize
      change (walSegmentPayloadBytes ((next, nextBytes) :: remaining)).size = (through - next) * frameSize at restSize
      have offsets : next - first + (through - next) = through - first := by
        have nextWithin := remainingWithin (next, nextBytes) (by simp)
        omega
      rw [ByteArray.size_append, size, restSize, ← Nat.add_mul, offsets]

/-- When the keeper is the exact bounded prefix, the segment sizes already
validated by marked recovery imply the frame alignment and final watermark
of the serial replay. Its table or diagnostic matches the vector decoder. -/
theorem finishWalChunkReplay_eq_marked (base : PackedTable) (length : UInt64)
    (first : Nat) (bytes : ByteArray) (rest : List (Nat × ByteArray))
    (aligned : length.toNat % frameSize = 0)
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true)
    (keeper : ∀ file, ((first, bytes) :: rest).getLast? = some file →
      file.2.size = (length.toNat / frameSize - file.1) * frameSize) :
    finishWalChunkReplay (length.toNat / frameSize)
      (((first, bytes) :: rest).foldlM (fun current file => replayWalChunk current file.1 file.2) (.ok base)) =
      (recoverMarkedWalSegments base length ((first, bytes) :: rest)).map Prod.snd := by
  let files := (first, bytes) :: rest
  let through := length.toNat / frameSize
  let payload := walSegmentPayloadBytes files
  have accepted := checked
  rw [checkSelectedWalSegmentSpans, Bool.and_eq_true, List.all_eq_true] at accepted
  have within (file : Nat × ByteArray) (member : file ∈ files) : file.1 ≤ through :=
    of_decide_eq_true (accepted.1 file member)
  have firstWithin : first ≤ through := within (first, bytes) (by simp [files])
  have spans := ((checkWalSegmentSpans_iff through files).mp accepted.2).2
  obtain ⟨allAligned, size⟩ := spans.exactPayloads within keeper
  change payload.size = (through - first) * frameSize at size
  have markerBytes : through * frameSize = length.toNat := by
    simpa [through, aligned, Nat.mul_comm] using Nat.mod_add_div length.toNat frameSize
  have count : length.toNat - first * frameSize = payload.size := by
    rw [size, ← markerBytes, ← Nat.sub_mul]
  have bound : first * frameSize ≤ length.toNat := by
    rw [← markerBytes]
    exact Nat.mul_le_mul_right _ firstWithin
  have countFits : (length.toNat - first * frameSize).toUInt64.toNat = payload.size := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le ..) length.toNat_lt_size), count]
  have selection : WAL.Boundary.selectRetained first length payload = .ok payload := by
    rw [WAL.Boundary.selectRetained, ite_eq_right (Nat.not_lt.mpr bound), WAL.Boundary.select]
    simp [countFits, size, Nat.mul_mod_left]
  have last : through = first + payload.size / frameSize := by
    rw [size, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
    omega
  have concat := walSegmentPayloadBytes_eq_fold files
  change finishWalChunkReplay through
      (files.foldlM (fun current file => replayWalChunk current file.1 file.2) (.ok base)) =
    (recoverMarkedWalSegments base length files).map Prod.snd
  rw [← spans.replayWalChunks_eq_foldlM]
  change finishWalChunkReplay through (replayWalChunks first (.ok base) (files.map Prod.snd)) = _
  rw [finishWalChunkReplay_eq_retained _ _ _ _ allAligned (by rwa [← concat]), ← concat]
  rw [recoverMarkedWalSegments_eq_extract base length first bytes rest checked]
  change recoverRetainedFrom base first payload =
    (WAL.Boundary.recoverRetainedMarked base first length (payload.extract 0 (length.toNat - first * frameSize))).map
      Prod.snd
  rw [count, ByteArray.extract_zero_size, WAL.Boundary.recoverRetainedMarked, selection]
  cases replayed : recoverRetainedFrom base first payload <;>
    simp [replayed, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]

end Alvoki.Storage
