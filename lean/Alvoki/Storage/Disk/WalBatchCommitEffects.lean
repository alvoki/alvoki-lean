import Alvoki.Storage.Disk.WalBatch
import Alvoki.Storage.Disk.WalSegmentAppendRepair
import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.AppendCutSession

namespace Alvoki.Storage.WalSegmentCommit

open System WAL.Boundary

/-- A batch extends an already durable prefix in one append. Reports can
admit arbitrary bytes after that prefix until the whole suffix is synced. -/
def appendBatch (effects : WriteEffects) (batch : List WAL.Write) : EStateM Unit WriteFiles Unit :=
  fun files =>
    let candidates := ByteArray.empty :: effects.appendCrashTails
    match effects.append with
    | .ok () => .ok ()
      { files with visibleTail := WAL.encode batch, crashTails := candidates, crashPossible := by simp [candidates] }
    | .error visible => .error ()
      { files with visibleTail := visible, crashTails := candidates, crashPossible := by simp [candidates] }

private def batchMarker (history : List WAL.Write) : ByteArray :=
  WAL.Boundary.encode (WAL.encode history).size.toUInt64

/-- One append report followed by the same four marker steps as a single
write. The only candidate replacement marker covers the entire batch. -/
def runBatchEffects (before batch : List WAL.Write) (effects : WriteEffects)
    (scratch : Option (ByteArray × Bool) := none) : EStateM.Result Unit WriteFiles Unit :=
  WAL.Boundary.commit (appendBatch effects batch)
    (Publication.run (effects.markerStep (batchMarker (before ++ batch))))
    (WriteFiles.initial before scratch)

/-- Exact reports at reached callbacks connect an append-plus-publication
schedule to the model. The append starts on an existing active segment.
The marker callbacks account for both file sync effects and for a
directory sync that may take effect despite a reported error. -/
theorem batch_reports (dir : DiskDirectory) (first : Nat) (before batch : List WAL.Write)
    (newBytes : Nat) (count : newBytes = (WAL.encode (before ++ batch)).size)
    (effects : WriteEffects) (scratch : Option (ByteArray × Bool))
    (append write : FilePath → ByteArray → EStateM Unit WriteFiles Unit)
    (sync : Array FilePath → EStateM Unit WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM Unit WriteFiles Unit)
    (appendReport : append (dir.file (.walSegment first)) (WAL.encodeBatch batch) (WriteFiles.initial before scratch) =
      appendBatch effects batch (WriteFiles.initial before scratch))
    (markerReports : ∀ appended, appendBatch effects batch (WriteFiles.initial before scratch) = .ok () appended →
      ∀ prior action remaining state, Publication.steps = prior ++ action :: remaining →
      (prior.forM (effects.markerStep (WAL.Boundary.encode newBytes.toUInt64))) appended = .ok () state →
      performMarkerAt dir first newBytes write sync rename action state =
        effects.markerStep (WAL.Boundary.encode newBytes.toUInt64) action state) :
    commitBytesAt dir first (WAL.encodeBatch batch) newBytes append write sync rename
      (WriteFiles.initial before scratch) = runBatchEffects before batch effects scratch := by
  rw [WAL.encodeBatch_eq] at appendReport ⊢
  rw [count] at markerReports ⊢
  change EStateM.bind (append (dir.file (.walSegment first)) (WAL.encode batch))
      (fun _ => Publication.run (performMarkerAt dir first (WAL.encode (before ++ batch)).size write sync rename))
      (WriteFiles.initial before scratch) =
    EStateM.bind (appendBatch effects batch)
      (fun _ => Publication.run (effects.markerStep (batchMarker (before ++ batch))))
      (WriteFiles.initial before scratch)
  unfold EStateM.bind
  rw [appendReport]
  cases appended : appendBatch effects batch (WriteFiles.initial before scratch) with
  | error _ _ => rfl
  | ok value after =>
    cases value
    exact markerSteps_agree _ _ Publication.steps after (markerReports after appended)

private def BeforeRename (before : List WAL.Write) (files : WriteFiles) : Prop :=
  files.marker.active = some (batchMarker before) ∧
  ∀ marker ∈ files.marker.crashImages, marker = some (batchMarker before)

private def BatchSynced (before batch : List WAL.Write) (files : WriteFiles) : Prop :=
  files.visibleTail = WAL.encode batch ∧ files.crashTails = [WAL.encode batch] ∧
  Publication.Retry (fun _ bytes => bytes = batchMarker (before ++ batch))
    (.settled (some (batchMarker before))) files.marker

private theorem runBatchEffects_cut (before batch : List WAL.Write)
    (effects : WriteEffects) (scratch : Option (ByteArray × Bool)) :
    let files := writeFilesAfter (runBatchEffects before batch effects scratch)
    BeforeRename before files ∨ BatchSynced before batch files := by
  intro files
  have beforeRename : ∀ files, files.marker.active = some (batchMarker before) →
      files.marker.crashImages = [some (batchMarker before)] → BeforeRename before files := by
    intro files visible survives
    exact ⟨visible, fun _ chosen => List.mem_singleton.mp (survives ▸ chosen)⟩
  rcases effects with ⟨append, tails, stage, sync, rename, directory⟩
  rcases append with visible | ⟨⟩
  · exact .inl (beforeRename _ rfl rfl)
  rcases stage with leftover | ⟨⟩
  · exact .inl (beforeRename _ rfl rfl)
  rcases sync with ⟨walEffect, markerSynced⟩ | ⟨⟩
  · cases walEffect <;> cases markerSynced <;> exact .inl (beforeRename _ rfl rfl)
  cases rename with
  | errorBeforeEffect => exact .inr ⟨rfl, rfl, .attempt (.refl _) rfl 2 rfl⟩
  | errorAfterEffect => exact .inr ⟨rfl, rfl, .attempt (.refl _) rfl 3 rfl⟩
  | success =>
    cases directory with
    | errorBeforeEffect => exact .inr ⟨rfl, rfl, .attempt (.refl _) rfl 3 rfl⟩
    | success | errorAfterEffect => exact .inr ⟨rfl, rfl, .attempt (.refl _) rfl 4 rfl⟩

private theorem batchOldFits {before batch : List WAL.Write}
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size) :
    (WAL.encode before).size < UInt64.size := by
  apply Nat.lt_of_le_of_lt _ fits
  rw [WAL.encode_append, ByteArray.size_append]
  exact Nat.le_add_right _ _

private theorem batchLengthMonotone {before batch history : List WAL.Write}
    (allowed : history = before ∨ history = before ++ batch) : before.length ≤ history.length := by
  rcases allowed with rfl | rfl
  · exact Nat.le_refl _
  · simp

private theorem batchHistoryFits {before batch history : List WAL.Write}
    (allowed : history = before ∨ history = before ++ batch)
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size) : (WAL.encode history).size < UInt64.size := by
  rcases allowed with rfl | rfl
  · exact batchOldFits fits
  · exact fits

private theorem batchHistory_eq_of_length {before batch left right : List WAL.Write}
    (leftAllowed : left = before ∨ left = before ++ batch)
    (rightAllowed : right = before ∨ right = before ++ batch)
    (sameLength : left.length = right.length) : left = right := by
  rcases leftAllowed with rfl | rfl <;> rcases rightAllowed with rfl | rfl
  · rfl
  · have empty : batch = [] := List.length_eq_zero_iff.mp (by simp only [List.length_append] at sameLength; omega)
    simp [empty]
  · have empty : batch = [] := List.length_eq_zero_iff.mp (by simp only [List.length_append] at sameLength; omega)
    simp [empty]
  · rfl

private theorem selectRetained_encoded (history : List WAL.Write) (first : Nat) (tail : ByteArray)
    (starts : first ≤ history.length) (fits : (WAL.encode history).size < UInt64.size) :
    selectRetained first (WAL.encode history).size.toUInt64 (WAL.encode (history.drop first) ++ tail) =
      .ok (WAL.encode (history.drop first)) := by
  have covers : first * WAL.frameSize ≤ (WAL.encode history).size := by
    rw [WAL.encode_size, Nat.mul_comm WAL.frameSize]
    exact Nat.mul_le_mul_right _ starts
  have dropped : (WAL.encode history).size - first * WAL.frameSize =
      (WAL.encode (history.drop first)).size := by
    rw [WAL.encode_size, WAL.encode_size, List.length_drop, Nat.mul_comm first, Nat.mul_sub_left_distrib]
  have localFits : (WAL.encode (history.drop first)).size < UInt64.size :=
    Nat.lt_of_le_of_lt (dropped ▸ Nat.sub_le ..) fits
  unfold selectRetained
  rw [UInt64.toNat_ofNat_of_lt' fits, ite_eq_right (Nat.not_lt.mpr covers), dropped]
  exact select_encoded (history.drop first) tail localFits

/-- At any reported cut, every selectable marker and every admitted active
segment image yield precisely the old acknowledged history or that history
plus the entire batch. Selection is absolute even when older WAL segments
are no longer present. An arbitrary torn suffix cannot select a proper
part of the batch. -/
theorem selectSegment_atReportedBatchCut {before batch : List WAL.Write} {first : Nat}
    (starts : first ≤ before.length) (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (pair : DirectoryPublication.Bindings) (bytes : ByteArray) :
    let segment := (writeFilesAfter (runBatchEffects before batch effects scratch)).reopenSegment first before manifest
    pair ∈ segment.directory.active :: segment.directory.crashImages →
    some bytes ∈ segment.wal.active :: segment.wal.crashImages →
    ∃ history, (history = before ∨ history = before ++ batch) ∧ pair.manifest = manifest ∧
      pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      selectRetained first (WAL.encode history).size.toUInt64 bytes = .ok (WAL.encode (history.drop first)) := by
  intro segment pairChosen bytesChosen
  let files := writeFilesAfter (runBatchEffects before batch effects scratch)
  have binding : pair.walBoundary = files.marker.active ∨ pair.walBoundary ∈ files.marker.crashImages := by
    rcases List.mem_cons.mp pairChosen with rfl | survives
    · exact .inl rfl
    · obtain ⟨marker, member, rfl⟩ := List.mem_map.mp survives
      exact .inr member
  have sameManifest := files.reopenImage_manifest_eq (before.drop first) manifest pairChosen
  obtain ⟨tail, tailChosen, exactBytes⟩ := files.candidate_from_tail (before.drop first) manifest bytesChosen
  have bytesEq := Option.some.inj exactBytes
  have oldFits := batchOldFits fits
  have oldCase :
      selectRetained first (WAL.encode before).size.toUInt64 bytes = .ok (WAL.encode (before.drop first)) := by
    rw [bytesEq]
    exact selectRetained_encoded before first tail starts oldFits
  rcases runBatchEffects_cut before batch effects scratch with ⟨visible, survives⟩ | ⟨visible, survives, published⟩
  · have old := binding.elim (·.trans visible) (survives _)
    exact ⟨before, .inl rfl, sameManifest, old, oldCase⟩
  · let allowed := fun marker => marker = some (batchMarker before) ∨ marker = some (batchMarker (before ++ batch))
    have valid : files.marker.Valid allowed := Publication.retry_preserves
      (fun _ next _ replacement => Or.inr (congrArg some replacement))
      (Publication.Image.settled_valid (Or.inl rfl)) published
    rcases binding.elim (fun same => same.symm ▸ valid.activeValid) (valid.crashValid _) with old | whole
    · exact ⟨before, .inl rfl, sameManifest, old, oldCase⟩
    · have complete : tail = WAL.encode batch :=
        (List.mem_cons.mp tailChosen).elim (·.trans visible) (fun member => List.mem_singleton.mp (survives ▸ member))
      have extended : bytes = WAL.encode ((before ++ batch).drop first) := by
        rw [bytesEq, complete, List.drop_append_of_le_length starts, WAL.encode_append]
      have startsNew : first ≤ (before ++ batch).length := by
        rw [List.length_append]
        exact Nat.le_trans starts (Nat.le_add_right ..)
      refine ⟨before ++ batch, .inr rfl, sameManifest, whole, ?_⟩
      rw [extended]
      simpa only [ByteArray.append_empty] using
        selectRetained_encoded (before ++ batch) first ByteArray.empty startsNew fits

/-- A reported success leaves one durable marker and exactly the complete
batch appended to the segment. -/
theorem settledSegment_ofBatchSuccess {before batch : List WAL.Write} {effects : WriteEffects}
    {scratch : Option (ByteArray × Bool)} {files : WriteFiles} {first : Nat} (starts : first ≤ before.length)
    (ran : runBatchEffects before batch effects scratch = .ok () files) (manifest : Option ByteArray) :
    let after := files.reopenSegment first before manifest
    after.directory.active = ⟨manifest, some (WAL.Boundary.encode (WAL.encode (before ++ batch)).size.toUInt64)⟩ ∧
      after.directory.crashImages = [after.directory.active] ∧
      after.wal.active = some (WAL.encode ((before ++ batch).drop first)) ∧
      after.wal.crashImages = [after.wal.active] := by
  rcases effects with ⟨append, tails, stage, sync, rename, directory⟩
  rcases append with visible | ⟨⟩
  · contradiction
  rcases stage with leftover | ⟨⟩
  · contradiction
  rcases sync with ⟨walEffect, markerSynced⟩ | ⟨⟩
  · cases walEffect <;> cases markerSynced <;> contradiction
  cases rename with
  | errorBeforeEffect | errorAfterEffect => contradiction
  | success =>
    cases directory with
    | errorBeforeEffect | errorAfterEffect => contradiction
    | success =>
      cases ran
      refine ⟨rfl, rfl, ?_, rfl⟩
      change some (WAL.encode (before.drop first) ++ WAL.encode batch) = _
      rw [List.drop_append_of_le_length starts, WAL.encode_append]

end Alvoki.Storage.WalSegmentCommit

namespace Alvoki.Storage.WalSegmentRepair

open WalSegmentCommit WAL.Boundary

/-- The batch's observed marker admits one of two complete histories.
A target carries the exact physical suffix of the selected history. -/
def BatchRetryTarget (before batch : List WAL.Write) (first : Nat) (target : Target) : Prop :=
  target.first = first ∧ ∃ history, (history = before ∨ history = before ++ batch) ∧
    target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
    target.range.through = history.length ∧ target.trimmed = WAL.encode (history.drop first)

theorem BatchRetryTarget.unique {before batch : List WAL.Write} {first : Nat} {left right : Target}
    (a : BatchRetryTarget before batch first left) (b : BatchRetryTarget before batch first right)
    (pair : left.pair = right.pair) : left = right := by
  obtain ⟨leftStart, l, leftAllowed, _, throughLeft, bytesLeft⟩ := a
  obtain ⟨rightStart, r, rightAllowed, _, throughRight, bytesRight⟩ := b
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  have length := throughLeft.symm.trans (congrArg MarkedWalRange.through range) |>.trans throughRight
  have history := batchHistory_eq_of_length leftAllowed rightAllowed length
  have sameStart := leftStart.trans rightStart.symm
  rw [history] at bytesLeft
  have sameBytes := bytesLeft.trans bytesRight.symm
  cases left
  cases right
  cases pair
  cases range
  cases sameStart
  cases sameBytes
  rfl

/-- One observed batch marker determines the unique repair cutoff for every
compatible keeper candidate. Sealed reads and lock ownership are checked
separately by the bounded reopen caller. -/
theorem prepareAfterBatchCut {before batch : List WAL.Write} {first watermark : Nat}
    (starts : first ≤ before.length) (covered : watermark ≤ before.length)
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark manifest = some watermark)
    (image : FileImage) {keeperBytes : ByteArray}
    (readKeeper : image.keeper.active = some keeperBytes)
    (keeperCrash : image.keeper.crashImages ≠ [])
    (noLater : image.later.DurablyEmpty) :
    let cut := (writeFilesAfter (runBatchEffects before batch effects scratch)).reopenSegment first before manifest
    image.directory.active ∈ cut.directory.active :: cut.directory.crashImages →
    (∀ binding ∈ image.keeper.active :: image.keeper.crashImages,
      binding ∈ cut.wal.active :: cut.wal.crashImages) →
    ∃ target, BatchRetryTarget before batch first target ∧ target.pair.manifest = manifest ∧
      Prepared image target ⟨target.range.through, first, [], keeperBytes⟩ := by
  intro cut chosen observed
  have active := observed image.keeper.active (List.mem_cons_self ..)
  rw [readKeeper] at active
  obtain ⟨history, allowed, sameManifest, rawMarker, _⟩ :=
    selectSegment_atReportedBatchCut starts fits effects manifest scratch
      image.directory.active keeperBytes chosen active
  have lengthMonotone := batchLengthMonotone allowed
  have count : (WAL.encode history).size.toUInt64.toNat = history.length * WAL.frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' (batchHistoryFits allowed fits), WAL.encode_size, Nat.mul_comm]
  have covers : watermark ≤ history.length := Nat.le_trans covered lengthMonotone
  have decoded : image.directory.active.walRange = some ⟨watermark, history.length⟩ :=
    DirectoryPublication.Bindings.walRange_of_counts (sameManifest ▸ checkpoint) rawMarker (decode_encode _) count covers
  let target : Target :=
    ⟨image.directory.active, ⟨watermark, history.length⟩, decoded, first, Nat.le_trans starts lengthMonotone,
      WAL.encode (history.drop first), by rw [WAL.encode_size, List.length_drop, Nat.mul_comm]⟩
  have accepted (binding : Option ByteArray) (member : binding ∈ image.keeper.active :: image.keeper.crashImages) :
      target.Accepts binding := by
    have survived := observed binding member
    obtain ⟨tail, _, rfl⟩ := (writeFilesAfter (runBatchEffects before batch effects scratch)).candidate_from_tail
      (before.drop first) manifest survived
    obtain ⟨other, allowedOther, otherManifest, markerOther, selected⟩ :=
      selectSegment_atReportedBatchCut starts fits effects manifest scratch image.directory.active _ chosen survived
    have otherSize : (WAL.encode other).size.toUInt64.toNat = other.length * WAL.frameSize := by
      rw [UInt64.toNat_ofNat_of_lt' (batchHistoryFits allowedOther fits), WAL.encode_size, Nat.mul_comm]
    have otherDecoded : image.directory.active.walRange = some ⟨watermark, other.length⟩ :=
      DirectoryPublication.Bindings.walRange_of_counts (otherManifest ▸ checkpoint) markerOther (decode_encode _)
        otherSize (Nat.le_trans covered (batchLengthMonotone allowedOther))
    have sameLength : other.length = history.length :=
      congrArg MarkedWalRange.through (Option.some.inj (otherDecoded.symm.trans decoded))
    rw [batchHistory_eq_of_length allowedOther allowed sameLength] at selected
    exact Target.accepts_of_selected selected
  have later : image.later.Beyond target.range.through := by
    intro names appears
    rw [noLater.1, noLater.2] at appears
    obtain rfl : names = [] := by simpa using appears
    simp
  exact ⟨target, ⟨rfl, history, allowed, rawMarker, rfl, rfl⟩, sameManifest,
    ⟨rfl, ⟨keeperCrash, accepted _ (List.mem_cons_self ..),
      fun binding h => accepted binding (List.mem_cons_of_mem _ h)⟩,
      later, rfl, rfl, noLater.1.symm, readKeeper⟩⟩

/-- Compare the reached files with the batch interpreter's visible and
crash choices. The reached staging files are carried by the retry trace. -/
structure BatchCutProjection (initial : FileImage) (cut : ReopenImage) : Prop where
  active : initial.directory.active = cut.directory.active
  metadata : initial.directory.crashImages = cut.directory.crashImages
  keeper : initial.keeper.active = cut.wal.active
  keeperChoices : initial.keeper.crashImages = cut.wal.crashImages
  noLater : initial.later.DurablyEmpty

/-- Any finite series of reported bounded reopen failures, final reference
drops and power losses retains an old-or-whole batch selection. Before the
directory barrier a power loss may still select either original marker.
After the barrier the existing repair lineage keeps the authorized target. -/
private theorem boundedBatchRetry_layoutInputs {before batch : List WAL.Write} {first watermark : Nat}
    (starts : first ≤ before.length) (covered : watermark ≤ before.length)
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark manifest = some watermark)
    {directory : DiskDirectory} {initial after : DiskSession.LockedFileState FileImage}
    (attempts : DiskSession.BoundedReopenTrace directory (BatchRetryTarget before batch first) initial after) :
    let cut := (writeFilesAfter (runBatchEffects before batch effects scratch)).reopenSegment first before manifest
    BatchCutProjection initial.image cut →
    after.image.kept = initial.image.kept ∧
      ∃ target, BatchRetryTarget before batch first target ∧ target.pair.manifest = manifest ∧
        after.image.directory.active = target.pair ∧ after.image.keeper.Valid target.Accepts ∧
        after.image.later.Beyond target.range.through ∧ after.image.later.visible = [] := by
  intro cut observed
  obtain ⟨activeEq, metadataEq, keeperEq, crashEq, noLater⟩ := observed
  have keeperCrash : initial.image.keeper.crashImages ≠ [] := by
    rw [crashEq]
    exact (writeFilesAfter (runBatchEffects before batch effects scratch)).reopenImage_crashWal_nonempty
      (before.drop first) manifest
  have prepareObserved {current : FileImage} (observation : BeforeReopenBarrier initial.image current) :
      ∃ target plan, BatchRetryTarget before batch first target ∧ target.pair.manifest = manifest ∧
        Prepared current target plan := by
    have prepare {image : FileImage}
        (chosen : image.directory.active ∈ cut.directory.active :: cut.directory.crashImages)
        (payloads : ∀ binding ∈ image.keeper.active :: image.keeper.crashImages,
          binding ∈ cut.wal.active :: cut.wal.crashImages)
        (crashPossible : image.keeper.crashImages ≠ []) (emptyLater : image.later.DurablyEmpty) :
        ∃ target plan, BatchRetryTarget before batch first target ∧ target.pair.manifest = manifest ∧
          Prepared image target plan := by
      obtain ⟨_, _, readKeeper⟩ := (writeFilesAfter (runBatchEffects before batch effects scratch)).candidate_from_tail
        (before.drop first) manifest (payloads _ (List.mem_cons_self ..))
      obtain ⟨target, admitted, sameManifest, prepared⟩ :=
        prepareAfterBatchCut starts covered fits effects manifest scratch checkpoint
          image readKeeper crashPossible emptyLater chosen payloads
      exact ⟨target, _, admitted, sameManifest, prepared⟩
    cases observation with
    | live =>
      apply prepare _ _ keeperCrash noLater
      · rw [activeEq]
        exact List.mem_cons_self ..
      · intro binding member
        simpa only [keeperEq, crashEq] using member
    | crash pair keeper later observed read names =>
      have empty : later = [] := List.mem_singleton.mp (noLater.2 ▸ names)
      have keeperMember : keeper ∈ cut.wal.crashImages := crashEq ▸ read
      have pairMember : pair ∈ cut.directory.crashImages := metadataEq ▸ observed
      subst later
      apply prepare (List.mem_cons_of_mem _ pairMember) _ (by simp [FileImage.crash, Publication.Image.settled])
        (by exact ⟨rfl, rfl⟩)
      intro binding member
      have same : binding = keeper := by simpa [FileImage.crash, Publication.Image.settled] using member
      exact List.mem_cons_of_mem _ (same.symm ▸ keeperMember)
  have observedEmpty {current : FileImage} (observation : BeforeReopenBarrier initial.image current) :
      current.later.visible = [] := by
    cases observation with
    | live => exact noLater.1
    | crash pair keeper later metadata payload names => exact List.mem_singleton.mp (noLater.2 ▸ names)
  have lineage := attempts.lineage (fun a b pair => BatchRetryTarget.unique a b pair)
  refine ⟨lineage.keepsSealed, ?_⟩
  cases lineage with
  | before observed =>
    obtain ⟨target, _, admitted, sameManifest, prepared⟩ := prepareObserved observed
    exact ⟨target, admitted, sameManifest, prepared.pair, prepared.keeperPrefix, prepared.newer, observedEmpty observed⟩
  | repairing observed admitted prepared trace =>
    obtain ⟨candidate, _, candidateAdmitted, sameManifest, firstRead⟩ := prepareObserved observed
    have same := BatchRetryTarget.unique candidateAdmitted admitted (firstRead.pair.symm.trans prepared.pair)
    subst candidate
    have valid := trace.valid prepared.pair prepared.keeperPrefix prepared.newer
    exact ⟨_, admitted, sameManifest, valid.selected, valid.keeper, valid.later, trace.emptyLater (observedEmpty observed)⟩

/-- Any finite series of reported bounded reopen failures, final reference
drops and power losses retains an old-or-whole batch selection. Before the
directory barrier a power loss may still select either original marker.
After the barrier the existing repair lineage keeps the authorized target. -/
theorem boundedBatchRetry_selection {before batch : List WAL.Write} {first watermark : Nat}
    (starts : first ≤ before.length) (covered : watermark ≤ before.length)
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    (effects : WriteEffects) (manifest : Option ByteArray) (scratch : Option (ByteArray × Bool))
    (checkpoint : selectedCheckpointWatermark manifest = some watermark)
    {directory : DiskDirectory} {initial after : DiskSession.LockedFileState FileImage}
    (noLater : initial.image.later.DurablyEmpty)
    (attempts : DiskSession.BoundedReopenTrace directory (BatchRetryTarget before batch first) initial after) :
    let cut := (writeFilesAfter (runBatchEffects before batch effects scratch)).reopenSegment first before manifest
    initial.image.directory = cut.directory →
    initial.image.keeper.active = cut.wal.active →
    initial.image.keeper.crashImages = cut.wal.crashImages →
    after.image.kept = initial.image.kept ∧
      ∃ target, BatchRetryTarget before batch first target ∧ target.pair.manifest = manifest ∧
        after.image.directory.active = target.pair ∧ after.image.keeper.Valid target.Accepts := by
  intro cut directoryEq keeperEq crashEq
  obtain ⟨sealed, target, admitted, sameManifest, pair, keeper, _, _⟩ :=
    boundedBatchRetry_layoutInputs starts covered fits effects manifest scratch checkpoint attempts
      ⟨congrArg DirectoryPublication.Image.active directoryEq, congrArg DirectoryPublication.Image.crashImages directoryEq,
        keeperEq, crashEq, noLater⟩
  exact ⟨sealed, target, admitted, sameManifest, pair, keeper⟩

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- A bounded retry lineage from an interrupted batch selects one actual
marked layout before any new opener reads the files. -/
theorem BoundedReopenTrace.selectsAfterBatchCut {directory : DiskDirectory}
    {oldWal : WalSegmentImage} {before batch : List WAL.Write} {watermark : Nat}
    (layout : oldWal.ReadLayout before) (valid : oldWal.Valid before)
    (oldRange : oldWal.directory.active.walRange = some ⟨watermark, before.length⟩)
    (ordered : WAL.OrdinalsFrom 1 before) {live next : PackedTable} {rows : List (UInt64 × Option UInt64)}
    (committed : before.length = live.committed.toNat) (prepared : prepareBatch live rows = some (batch, next))
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    {published : CheckpointPublication.Image}
    (checkpoint : published.AcceptsVersioned before.length.toUInt64 (CheckpointRepresentsPrefix before)
      oldWal.directory.active.manifest)
    (effects : WriteEffects) {initial retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before batch oldWal.active.first) initial retry)
    (observed : BatchCutProjection initial.image
      ((writeFilesAfter (runBatchEffects before batch effects (oldWal.directory.staged .walBoundary))).reopenSegment
        oldWal.active.first before oldWal.directory.active.manifest)) :
    retry.image.kept = initial.image.kept ∧
    retry.image.directory.active.manifest = oldWal.directory.active.manifest ∧
    ∃ history, (history = before ∨ history = before ++ batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      let wal := oldWal.appendSelectedView retry.image.directory.active history
      wal.ReadLayout history ∧ wal.Valid history ∧
      ∃ selected : CanonicalKeeperLayout retry.image history,
        selected.range.watermark = watermark ∧ selected.target.first = oldWal.active.first ∧
        selected.keeper = wal.active ∧
        selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark ∧
        selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
          some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
        Prepared retry.image selected.target selected.plan ∧ retry.image.later.visible = [] ∧
        published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
          retry.image.directory.active.manifest ∧
        WAL.OrdinalsFrom 1 history ∧
        ∃ generation : UInt64,
          ((retry.image.directory.active.manifest.mapM fun bytes =>
              (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) :
              Except String UInt64) = .ok generation := by
  obtain ⟨watermarkRead, covered, _⟩ := DirectoryPublication.Bindings.walRange_accounting oldRange
  have starts : oldWal.active.first ≤ before.length := by
    rw [← layout.activeEnd]
    exact layout.forward oldWal.active (List.mem_append_right _ (by simp))
  obtain ⟨sealed, target, ⟨start, history, allowed, marker, through, trimmed⟩, sameManifest, pair, keeper,
      later, noLater⟩ :=
    boundedBatchRetry_layoutInputs starts covered fits effects oldWal.directory.active.manifest
      (oldWal.directory.staged .walBoundary) watermarkRead attempts observed
  have count : (WAL.encode history).size.toUInt64.toNat = history.length * WAL.frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' (batchHistoryFits allowed fits), WAL.encode_size, Nat.mul_comm]
  have newCovered := Nat.le_trans covered (batchLengthMonotone allowed)
  have decoded : retry.image.directory.active.walRange = some ⟨watermark, history.length⟩ := by
    rw [pair]
    exact DirectoryPublication.Bindings.walRange_of_counts (sameManifest ▸ watermarkRead)
      marker (decode_encode _) count newCovered
  let wal := oldWal.appendSelectedView retry.image.directory.active history
  have layoutValid : wal.ReadLayout history ∧ wal.Valid history := by
    rcases allowed with rfl | rfl
    · have same := layout.afterRetainedSuffix valid oldRange retry.image.directory.active []
        (by simpa only [List.append_nil] using decoded)
      exact ⟨by simpa only [List.append_nil] using same.1, by simpa only [List.append_nil] using same.2.1⟩
    · have same := layout.afterRetainedSuffix valid oldRange retry.image.directory.active batch decoded
      exact ⟨same.1, same.2.1⟩
  obtain ⟨ideal, range, sameKeeper, _, descriptors, offsets, _, _, _, _⟩ :=
    layoutValid.1.checkpointReopenLayout layoutValid.2 .visible decoded rfl none
  have trimmedKeeper : target.trimmed = ideal.keeper.bytes := by
    rw [trimmed, sameKeeper] <;> rfl
  obtain ⟨tail, visible⟩ := keeper.activeValid
  let selected : CanonicalKeeperLayout retry.image history :=
    ⟨ideal.range, range.symm ▸ decoded, ideal.through, ideal.first, ideal.sealed, ideal.keeper,
      ideal.chain, ideal.covers, tail, trimmedKeeper ▸ visible⟩
  have selectedFirst : selected.target.first = oldWal.active.first := by
    change ideal.keeper.first = oldWal.active.first
    rw [sameKeeper] <;> rfl
  have selectedTrimmed : selected.target.trimmed = WAL.encode (history.drop oldWal.active.first) := by
    rw [← selectedFirst]
    exact selected.chain.keeperBytes
  have selectedMarker : selected.target.pair.walBoundary =
      some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) := by
    change retry.image.directory.active.walBoundary = _
    rw [pair]
    exact marker
  have actual : selected.target = target :=
    BatchRetryTarget.unique
      ⟨selectedFirst, history, allowed, selectedMarker, selected.through, selectedTrimmed⟩
      ⟨start, history, allowed, marker, through, trimmed⟩ pair
  have plan : Prepared retry.image selected.target selected.plan := by
    apply selected.prepared keeper.hasCrashImage
    · intro payload survives
      obtain ⟨extra, exactPayload⟩ := keeper.crashValid payload survives
      exact ⟨extra, trimmedKeeper ▸ exactPayload⟩
    · rw [← actual] at later
      exact later
  have accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest := by
    rw [pair, sameManifest]
    rcases allowed with rfl | rfl
    · exact checkpoint
    · exact published.acceptsVersioned_extend_history checkpoint fits
  have consecutive : WAL.OrdinalsFrom 1 history :=
    allowed.elim (fun old => old.symm ▸ ordered) fun whole =>
      whole.symm ▸ (prepareBatch_extends_history ordered committed prepared).2.1
  have generationRead : ∃ generation : UInt64,
      ((retry.image.directory.active.manifest.mapM fun bytes =>
        (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) :
          Except String UInt64) = .ok generation := by
    cases visible : retry.image.directory.active.manifest with
    | none => exact ⟨0, rfl⟩
    | some bytes =>
      have selectedWatermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
      rw [visible] at selectedWatermark
      obtain ⟨parsed, parsedOk, _⟩ := selectedCheckpointWatermark_present_iff.mp selectedWatermark
      exact ⟨parsed.header.generation, by rw [Option.mapM, parsedOk]; rfl⟩
  obtain ⟨generation, generationRead⟩ := generationRead
  have exactDescriptors : selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark := by
    change ideal.sealed ++ [ideal.keeper] = wal.readDescriptors ideal.range.watermark
    rw [range]
    exact descriptors
  have exactOffsets : selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
    change selectWalSegmentReads (wal.segments.map WalSegment.first) ideal.range.watermark =
      some (ideal.first, (wal.readDescriptors ideal.range.watermark).map WalSegment.first)
    rw [range]
    exact offsets
  exact ⟨sealed, pair ▸ sameManifest, history, allowed, selectedMarker, layoutValid.1, layoutValid.2,
    selected, congrArg MarkedWalRange.watermark range, selectedFirst, sameKeeper, exactDescriptors,
    exactOffsets, plan, noLater, accepted, consecutive, generation, generationRead⟩

/-- After a physical batch cut and any admitted finite retry trace, the
selected directory pair determines exact WAL descriptors and keeper bytes.
Healthy reports at the reached locked paths install the corresponding old
or complete history through the existing bounded reopen worker. -/
theorem BoundedReopenTrace.installsAfterBatchCut {directory : DiskDirectory}
    {oldWal : WalSegmentImage} {before batch : List WAL.Write} {watermark : Nat}
    (layout : oldWal.ReadLayout before) (valid : oldWal.Valid before)
    (oldRange : oldWal.directory.active.walRange = some ⟨watermark, before.length⟩)
    (ordered : WAL.OrdinalsFrom 1 before) {live next : PackedTable} {rows : List (UInt64 × Option UInt64)}
    (committed : before.length = live.committed.toNat) (prepared : prepareBatch live rows = some (batch, next))
    (fits : (WAL.encode (before ++ batch)).size < UInt64.size)
    {published : CheckpointPublication.Image}
    (checkpoint : published.AcceptsVersioned before.length.toUInt64 (CheckpointRepresentsPrefix before)
      oldWal.directory.active.manifest)
    (effects : WriteEffects) {initial retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before batch oldWal.active.first) initial retry)
    (observed : BatchCutProjection initial.image
      ((writeFilesAfter (runBatchEffects before batch effects (oldWal.directory.staged .walBoundary))).reopenSegment
        oldWal.active.first before oldWal.directory.active.manifest))
    {descriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    retry.image.kept = initial.image.kept ∧
    retry.image.directory.active.manifest = oldWal.directory.active.manifest ∧
    ∃ history, (history = before ∨ history = before ++ batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      let wal := oldWal.appendSelectedView retry.image.directory.active history
      wal.ReadLayout history ∧ wal.Valid history ∧
      ∃ selected : CanonicalKeeperLayout retry.image history,
        selected.range.watermark = watermark ∧ selected.target.first = oldWal.active.first ∧
        ∃ generation : UInt64,
          ((retry.image.directory.active.manifest.mapM fun bytes =>
              (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) :
              Except String UInt64) = .ok generation ∧
          ∀ raw : HealthyBoundedWalReports directory
              (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
              wal retry.image.directory.active selected.range.watermark published.durable selected.tail,
            sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
            (∀ action prior after,
              ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
              prior.effect selected.target action = some after →
              performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () after) →
            AppendCutReady directory descriptor liveRefs history published retry.image selected.target generation
              (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                (raw.reopen removeFile write sync renameFile) retry) := by
  obtain ⟨sealed, manifest, history, allowed, marker, layout, valid, selected, sameWatermark, first,
    keeper, descriptors, offsets, plan, noLater, accepted, consecutive, generation, generationRead⟩ :=
      attempts.selectsAfterBatchCut layout valid oldRange ordered committed prepared fits checkpoint effects observed
  refine ⟨sealed, manifest, history, allowed, marker, layout, valid, selected, sameWatermark, first,
    generation, generationRead, ?_⟩
  intro raw settles healthy
  exact runOpenWithInstallation_appendLayout layout consecutive selected keeper descriptors
    offsets plan noLater accepted generationRead raw liveRefs fresh acquisition unlock removeFile write sync
    renameFile settles healthy

end Alvoki.Storage.DiskSession
