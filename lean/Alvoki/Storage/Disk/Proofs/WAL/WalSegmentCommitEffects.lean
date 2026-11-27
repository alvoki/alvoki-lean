import Alvoki.Storage.Disk.Proofs.WAL.RetainedWalBoundary
import Alvoki.Storage.Disk.WAL.WalSegmentCommit
import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.Storage.WalSegmentCommit

open System WAL.Boundary

/-- Classify a write by its file effects while retaining its original
error in the caller's execution. -/
def forgetError {ε σ α : Type} (run : EStateM ε σ α) : EStateM Unit σ α :=
  fun state => match run state with
    | .ok value after => .ok value after
    | .error _ after => .error () after

private theorem forgetError_bind {ε σ α β : Type} (run : EStateM ε σ α)
    (next : α → EStateM ε σ β) :
    forgetError (run >>= next) = (forgetError run >>= fun value => forgetError (next value)) := by
  funext state
  simp only [forgetError, Bind.bind, EStateM.bind]
  cases run state <;> rfl

theorem forgetError_commitBytesAt {ε : Type} (dir : DiskDirectory) (first : Nat) (bytes : ByteArray)
    (newBytes : Nat) (append write : FilePath → ByteArray → EStateM ε WriteFiles Unit)
    (sync : Array FilePath → EStateM ε WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM ε WriteFiles Unit) :
    forgetError (commitBytesAt dir first bytes newBytes append write sync rename) =
      commitBytesAt dir first bytes newBytes (fun path bytes => forgetError (append path bytes))
        (fun path bytes => forgetError (write path bytes)) (fun paths => forgetError (sync paths))
        (fun source target => forgetError (rename source target)) := by
  rw [commitBytesAt_fileEffects, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, forgetError_bind]
  rfl

theorem forgetError_commitAt {ε : Type} (dir : DiskDirectory) (first : Nat) (event : WAL.Write)
    (newBytes : Nat) (append write : FilePath → ByteArray → EStateM ε WriteFiles Unit)
    (sync : Array FilePath → EStateM ε WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM ε WriteFiles Unit) :
    forgetError (commitAt dir first event newBytes append write sync rename) =
      commitAt dir first event newBytes (fun path bytes => forgetError (append path bytes))
        (fun path bytes => forgetError (write path bytes)) (fun paths => forgetError (sync paths))
        (fun source target => forgetError (rename source target)) :=
  forgetError_commitBytesAt dir first (WAL.encodeFrame event) newBytes append write sync rename

/-- Equality of the reached callbacks suffices for equality of the marker schedules. -/
theorem markerSteps_agree
    (observed modeled : Publication.Step → EStateM Unit WriteFiles Unit)
    (steps : List Publication.Step) (initial : WriteFiles)
    (agrees : ∀ prior step remaining state, steps = prior ++ step :: remaining →
      (prior.forM modeled) initial = .ok () state → observed step state = modeled step state) :
    (steps.forM observed) initial = (steps.forM modeled) initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step rest ih =>
    change EStateM.bind (observed step) (fun _ => rest.forM observed) initial =
      EStateM.bind (modeled step) (fun _ => rest.forM modeled) initial
    unfold EStateM.bind
    rw [agrees [] step rest initial rfl rfl]
    cases next : modeled step initial with
    | error _ _ => rfl
    | ok value after =>
      cases value
      apply ih
      intro prior action remaining state schedule executed
      apply agrees (step :: prior) action remaining state (congrArg (List.cons step) schedule)
      change EStateM.bind (modeled step) (fun _ => prior.forM modeled) initial = .ok () state
      simpa only [EStateM.bind, next] using executed

/-- The executable callbacks and the existing durability model have the
same result under reports at the actual reached states. The initial append
extends an existing stable segment. The marker steps include the independent
effects of either file sync when the grouped callback fails. -/
theorem commitAt_reports (dir : DiskDirectory) (first : Nat) (before : List WAL.Write)
    (event : WAL.Write) (newBytes : Nat) (count : newBytes = (WAL.encode (before ++ [event])).size)
    (effects : WriteEffects) (scratch : Option (ByteArray × Bool))
    (append write : FilePath → ByteArray → EStateM Unit WriteFiles Unit)
    (sync : Array FilePath → EStateM Unit WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM Unit WriteFiles Unit)
    (appendReport : append (dir.file (.walSegment first)) (WAL.encodeFrame event) (WriteFiles.initial before scratch) =
      effects.appendFrame event (WriteFiles.initial before scratch))
    (markerReports : ∀ appended, effects.appendFrame event (WriteFiles.initial before scratch) = .ok () appended →
      ∀ prior action remaining state, Publication.steps = prior ++ action :: remaining →
      (prior.forM (effects.markerStep (WAL.Boundary.encode newBytes.toUInt64))) appended = .ok () state →
      performMarkerAt dir first newBytes write sync rename action state =
        effects.markerStep (WAL.Boundary.encode newBytes.toUInt64) action state) :
    commitAt dir first event newBytes append write sync rename (WriteFiles.initial before scratch) =
      runWriteEffects before event effects scratch := by
  rw [runWriteEffects_eq_commit, ← count]
  change EStateM.bind (append (dir.file (.walSegment first)) (WAL.encodeFrame event))
      (fun _ => Publication.run (performMarkerAt dir first newBytes write sync rename))
      (WriteFiles.initial before scratch) =
    EStateM.bind (effects.appendFrame event) (fun _ => Publication.run (effects.markerStep (WAL.Boundary.encode newBytes.toUInt64)))
      (WriteFiles.initial before scratch)
  unfold EStateM.bind
  rw [appendReport]
  cases appended : effects.appendFrame event (WriteFiles.initial before scratch) with
  | error _ _ => rfl
  | ok value after =>
    cases value
    exact markerSteps_agree _ _ Publication.steps after (markerReports after appended)

/-- Only the active segment's physical prefix is present at this path. The
same metadata still records the absolute WAL count. The sealed segments and
their bindings are fixed during this write schedule. -/
def _root_.Alvoki.WAL.Boundary.WriteFiles.reopenSegment (files : WriteFiles)
    (first : Nat) (before : List WAL.Write) (manifest : Option ByteArray) : ReopenImage :=
  files.reopenImage (before.drop first) manifest

private theorem encoded_split (history : List WAL.Write) (first : Nat) :
    WAL.encode history = WAL.encode (history.take first) ++ WAL.encode (history.drop first) := by
  rw [← WAL.encode_append, List.take_append_drop]

/-- At every reported append or publication cut, each admitted marker and
active-segment survivor select the exact local bytes of the acknowledged
history, or that history with the one submitted frame. The marker's count
and event ordinals are absolute even if earlier segments have been retired. -/
theorem selectSegment_atReportedCut {before : List WAL.Write} {first : Nat}
    (starts : first ≤ before.length) (event : WAL.Write)
    (fits : (WAL.encode (before ++ [event])).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (pair : DirectoryPublication.Bindings) (bytes : ByteArray) :
    let segment := (writeFilesAfter (runWriteEffects before event effects scratch)).reopenSegment first before manifest
    pair ∈ segment.directory.active :: segment.directory.crashImages →
    some bytes ∈ segment.wal.active :: segment.wal.crashImages →
    ∃ history, (history = before ∨ history = before ++ [event]) ∧ pair.manifest = manifest ∧
      pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      selectRetained first (WAL.encode history).size.toUInt64 bytes = .ok (WAL.encode (history.drop first)) := by
  intro segment pairChosen bytesChosen
  let files := writeFilesAfter (runWriteEffects before event effects scratch)
  let full := files.reopenImage before manifest
  obtain ⟨tail, tailChosen, localBytes⟩ := files.candidate_from_tail (before.drop first) manifest bytesChosen
  have fullChosen : some (WAL.encode before ++ tail) ∈ full.wal.active :: full.wal.crashImages := by
    rcases List.mem_cons.mp tailChosen with rfl | survives
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem survives)
  obtain ⟨contents, marker, fullBytes, cut, visible, crash⟩ :=
    (runWriteEffects_hasWriteCuts before event effects manifest scratch)
      (some (WAL.encode before ++ tail)) fullChosen
  have admissible : pair.walBoundary = marker.active ∨ pair.walBoundary ∈ marker.crashImages := by
    rcases List.mem_cons.mp pairChosen with rfl | survived
    · exact .inl visible.symm
    · exact .inr (crash _ survived)
  have oldFits : (WAL.encode before).size < UInt64.size := by
    apply Nat.lt_of_le_of_lt _ fits
    rw [WAL.encode_append, ByteArray.size_append]
    exact Nat.le_add_right _ _
  obtain ⟨rawMarker, history, boundMarker, exactMarker, allowed, selected⟩ :=
    write_cut_selects_old_or_new cut oldFits fits admissible
  have historyFits : (WAL.encode history).size < UInt64.size := by
    rcases allowed with rfl | rfl
    · exact oldFits
    · exact fits
  have left : history.take first = before.take first := by
    rcases allowed with rfl | rfl
    · rfl
    · exact List.take_append_of_le_length starts
  let removed := WAL.encode (before.take first)
  have offset : removed.size = first * WAL.frameSize := by
    simp [removed, Nat.min_eq_left starts, Nat.mul_comm]
  have covers : removed.size ≤ (WAL.encode history).size.toUInt64.toNat := by
    rw [UInt64.toNat_ofNat_of_lt' historyFits, encoded_split history first, left, ByteArray.size_append]
    exact Nat.le_add_right _ _
  have fullBytes : contents = removed ++ bytes := by
    rw [← Option.some.inj fullBytes, encoded_split before first, ByteArray.append_assoc, Option.some.inj localBytes]
  simp only [exactMarker, decode_encode, Bind.bind, Except.bind] at selected
  rw [fullBytes, selectRetained_eq_select _ _ offset covers] at selected
  have exactHistory : WAL.encode history = removed ++ WAL.encode (history.drop first) := by
    rw [encoded_split history first, left]
  have selected := selected.trans (congrArg Except.ok exactHistory)
  have sameManifest := files.reopenImage_manifest_eq (before.drop first) manifest pairChosen
  refine ⟨history, allowed, sameManifest, boundMarker.trans (congrArg some exactMarker), ?_⟩
  cases retained : selectRetained first (WAL.encode history).size.toUInt64 bytes with
  | error reason =>
    rw [retained] at selected
    contradiction
  | ok selectedBytes =>
    rw [retained] at selected
    have same := (ByteArray.append_right_inj removed).mp (Except.ok.inj selected)
    exact congrArg Except.ok same

/-- A reported success durably selects the one appended frame and keeps the
exact bytes of the extended active segment. -/
theorem settledSegment_ofSuccess {before : List WAL.Write} {event : WAL.Write} {effects : WriteEffects}
    {scratch : Option (ByteArray × Bool)} {files : WriteFiles} {first : Nat} (starts : first ≤ before.length)
    (ran : runWriteEffects before event effects scratch = .ok () files) (manifest : Option ByteArray) :
    let after := files.reopenSegment first before manifest
    after.directory.active = ⟨manifest, some (WAL.Boundary.encode (WAL.encode (before ++ [event])).size.toUInt64)⟩ ∧
      after.directory.crashImages = [after.directory.active] ∧
      after.wal.active = some (WAL.encode ((before ++ [event]).drop first)) ∧
      after.wal.crashImages = [after.wal.active] := by
  obtain ⟨active, durable, marker⟩ := runWriteEffects_success ran
  have extended : WAL.encode (before.drop first) ++ WAL.encodeFrame event =
      WAL.encode ((before ++ [event]).drop first) := by
    rw [List.drop_append_of_le_length starts, WAL.encode_append]
    simp [WAL.encode]
  change (⟨manifest, files.marker.active⟩ : DirectoryPublication.Bindings) =
      ⟨manifest, some (WAL.Boundary.encode (WAL.encode (before ++ [event])).size.toUInt64)⟩ ∧
    files.marker.crashImages.map (DirectoryPublication.Bindings.mk manifest) = [⟨manifest, files.marker.active⟩] ∧
    some (WAL.encode (before.drop first) ++ files.visibleTail) = some (WAL.encode ((before ++ [event]).drop first)) ∧
    files.crashTails.map (fun tail => some (WAL.encode (before.drop first) ++ tail)) =
      [some (WAL.encode (before.drop first) ++ files.visibleTail)]
  simp [active, durable, marker, Publication.Image.settled, extended]

end Alvoki.Storage.WalSegmentCommit
