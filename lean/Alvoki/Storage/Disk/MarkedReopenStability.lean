import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.WAL.Boundary
open Storage

private def markedPair (manifest : Option ByteArray) (events : List WAL.Write) :
    DirectoryPublication.Bindings :=
  ⟨manifest, some (encode (WAL.encode events).size.toUInt64)⟩

/-- A partial sync can duplicate a possible binding in the model. All visible
and surviving bindings still describe the same history. Staging names can be
left behind and are overwritten before a future publication uses them. -/
private def ExactHistory (image : ReopenImage) (manifest : Option ByteArray)
    (events : List WAL.Write) : Prop :=
  image.directory.Valid (· = markedPair manifest events) ∧
  image.wal.Valid (· = some (WAL.encode events))

private theorem ReopenImage.SettledFor.exact {image : ReopenImage}
    {manifest : Option ByteArray} {events : List WAL.Write}
    (settled : image.SettledFor manifest events) : ExactHistory image manifest events := by
  obtain ⟨pair, pairs, wal, choices⟩ := settled
  exact ⟨⟨by simp [pairs], fun candidate survives => by simpa [pairs, markedPair, pair] using survives⟩,
    ⟨by simp [choices], wal, fun _ survives => (List.mem_singleton.mp (choices ▸ survives)).trans wal⟩⟩

private theorem ExactHistory.markerBound {image : ReopenImage} {manifest : Option ByteArray}
    {events : List WAL.Write} (history : ExactHistory image manifest events) :
    MarkerBound image.directory := by
  let length := (WAL.encode events).size.toUInt64
  have marker : image.directory.active.walBoundary = some (encode length) :=
    congrArg DirectoryPublication.Bindings.walBoundary history.1.activeValid
  refine ⟨encode length, length, marker, decode_encode length, ?_⟩
  intro pair chosen
  have survives : pair ∈ image.directory.crashImages := by
    rcases List.mem_cons.mp chosen with rfl | survives
    · exact history.1.activeMaySurvive
    · exact survives
  have exactPair := history.1.crashValid pair survives
  exact ⟨encode length, length, congrArg DirectoryPublication.Bindings.walBoundary exactPair,
    decode_encode length, Nat.le_refl _⟩

private theorem ExactHistory.noRepair {image : ReopenImage} {manifest : Option ByteArray}
    {events : List WAL.Write} (history : ExactHistory image manifest events)
    (fits : (WAL.encode events).size < UInt64.size) {length : UInt64} {trimmed : ByteArray}
    (choice : image.RepairsTo length trimmed) : False := by
  obtain ⟨marker, present, decoded⟩ := choice.visibleMarker
  obtain ⟨contents, visible, selected, shorter⟩ := choice.selected
  have markerAt := congrArg DirectoryPublication.Bindings.walBoundary history.1.activeValid
  have markerEq : marker = encode (WAL.encode events).size.toUInt64 :=
    Option.some.inj (present.symm.trans markerAt)
  subst marker
  have lengthEq := Except.ok.inj ((decode_encode _).symm.trans decoded)
  have sizeEq := select_size selected
  have contentsEq := Option.some.inj (visible.symm.trans history.2.activeValid)
  rw [contentsEq, sizeEq, ← lengthEq, UInt64.toNat_ofNat_of_lt' fits] at shorter
  exact (Nat.lt_irrefl _) shorter

private theorem ExactHistory.retry {initial after : ReopenImage} {manifest : Option ByteArray}
    {events : List WAL.Write} (history : ExactHistory initial manifest events)
    (fits : (WAL.encode events).size < UInt64.size) (path : ReopenRetry initial after) :
    ExactHistory after manifest events := by
  induction path with
  | start => exact history
  | repair _ chosen _ earlier => exact (earlier.noRepair fits chosen).elim
  | syncDirectory _ earlier =>
    exact ⟨earlier.1.syncDirectory, ⟨by simp [ReopenImage.syncDirectory], earlier.2.activeValid,
      fun candidate survives => (List.mem_singleton.mp survives).trans earlier.2.activeValid⟩⟩
  | syncMetadata _ earlier => exact ⟨earlier.1.syncDirectory, earlier.2⟩
  | allowVisibleWal _ earlier =>
    refine ⟨earlier.1, ⟨by simp [ReopenImage.allowVisibleWal], earlier.2.activeValid, ?_⟩⟩
    intro candidate survives
    rcases List.mem_cons.mp survives with rfl | prior
    · exact earlier.2.activeValid
    · exact earlier.2.crashValid candidate prior
  | crash _ pairSurvives walSurvives earlier =>
    exact ⟨DirectoryPublication.Image.settled_valid (earlier.1.crashValid _ pairSurvives),
      Publication.Image.settled_valid (earlier.2.crashValid _ walSurvives)⟩

private theorem exactHistory_after_attempts {initial before : ReopenImage}
    {manifest : Option ByteArray} {events : List WAL.Write}
    (settled : initial.SettledFor manifest events) (fits : (WAL.encode events).size < UInt64.size)
    (attempts : MarkedReopenAttempts initial before) : ExactHistory before manifest events := by
  have history := settled.exact
  exact history.retry fits (attempts.toRetry history.markerBound)

/-- Reopening an already settled marked history after any sequence of modeled
reopen attempts and crashes returns the deterministic result of the shared
checkpoint loader and WAL replay. A successful attempt again settles the same
metadata and WAL. Fresh pins read the abstract replay at every retained
snapshot. Reads and effects use the locked-directory filesystem contract. -/
theorem reopenSettledHistory_refines {initial before after : ReopenImage}
    {manifest : Option ByteArray} {files : List ByteArray} {covered pending : List WAL.Write}
    {checkpoint table : PackedTable} {model : Sequential.SnapshotTable UInt64}
    (settled : initial.SettledFor manifest (covered ++ pending))
    (fits : (WAL.encode (covered ++ pending)).size < UInt64.size)
    (attempts : MarkedReopenAttempts initial before)
    {checkpointImage : CheckpointPublication.Image} {walSequence : UInt64}
    (accepted : checkpointImage.Accepts walSequence (fun header bytes =>
      CheckpointForRecovery (some (Manifest.encode header)) bytes checkpoint) manifest)
    (checkpointReads : CheckpointReadObservations checkpointImage before.directory.active.manifest)
    (walReads : MarkedWalReads before)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    (opened : runMarkedReopen
      (MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned before = .ok table after)
    (written : CheckpointForRecovery manifest files checkpoint)
    (represents : checkpoint.Refines model)
    (watermark : covered.length = checkpoint.committed.toNat)
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending)) :
    after.SettledFor manifest (covered ++ pending) ∧
    (manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun base =>
        recoverSelected base (WAL.encode (covered ++ pending))) = .ok table ∧
    table.committed.toNat = (covered ++ pending).length ∧
    ∃ abstract, SnapshotWalReplay model pending abstract ∧
      abstract.committed.toNat = (covered ++ pending).length ∧
      ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot →
        snapshot.toNat ≤ (covered ++ pending).length →
        ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (abstract.table.range start stop snapshot)) := by
  have exactHistory := exactHistory_after_attempts settled fits attempts
  have pair := exactHistory.1.activeValid
  have visibleManifest : before.directory.active.manifest = manifest :=
    congrArg DirectoryPublication.Bindings.manifest pair
  obtain ⟨base, marker, contents, selected, length, checkpointOpened, markerVisible,
    walVisible, decoded, selectedResult, replayed, directory, walActive, walChoices⟩ :=
    MarkedReopenReads.success _ exactHistory.markerBound opened
  have markerEq : marker = encode (WAL.encode (covered ++ pending)).size.toUInt64 :=
    Option.some.inj (markerVisible.symm.trans (congrArg DirectoryPublication.Bindings.walBoundary pair))
  subst marker
  have lengthEq := Except.ok.inj (decoded.symm.trans (decode_encode _))
  subst length
  have contentsEq := Option.some.inj (walVisible.symm.trans exactHistory.2.activeValid)
  subst contents
  have fullSelection :
      select (WAL.encode (covered ++ pending)).size.toUInt64 (WAL.encode (covered ++ pending)) =
        .ok (WAL.encode (covered ++ pending)) := by
    simpa using select_encoded (covered ++ pending) ByteArray.empty fits
  have selectionEq := Except.ok.inj (selectedResult.symm.trans fullSelection)
  subst selected
  change checkpointReads.result.map (fun loaded => (loaded.getD (.empty, 0)).1) = .ok base
    at checkpointOpened
  obtain ⟨loaded, loadResult, sameLoaded⟩ : ∃ loaded, checkpointReads.result = .ok loaded ∧
      (loaded.getD (.empty, 0)).1 = base := by
    cases loadResult : checkpointReads.result with
    | error => rw [loadResult] at checkpointOpened; contradiction
    | ok result =>
      rw [loadResult] at checkpointOpened
      exact ⟨result, rfl, Except.ok.inj checkpointOpened⟩
  have actualBase := CheckpointForRecovery.loaded_observation
    (visibleManifest.symm ▸ written) (visibleManifest.symm ▸ accepted) checkpointReads loadResult
  rw [visibleManifest, sameLoaded] at actualBase
  obtain ⟨referenceBase, expectedLoad, same⟩ := written.loads
  have sameBase := Except.ok.inj (actualBase.symm.trans expectedLoad)
  subst referenceBase
  have count : covered.length = base.committed.toNat := by simpa only [same.committed] using watermark
  have played := (recoverSelected_encoded base covered pending ordered count).symm.trans replayed
  have committed : table.committed.toNat = (covered ++ pending).length := by
    rw [replay_committed_count pending played, ← count, List.length_append]
  have sameCheckpoint : checkpoint.SameData base :=
    ⟨same.runs.symm, same.memory.symm, same.committed.symm, same.floor.symm⟩
  obtain ⟨reference, replay, agrees⟩ := replay_sameData sameCheckpoint pending played
  obtain ⟨abstract, modeled, refined⟩ := replay_refines represents replay
  have agreesSymm : table.SameData reference :=
    ⟨agrees.runs.symm, agrees.memory.symm, agrees.committed.symm, agrees.floor.symm⟩
  refine ⟨⟨?_, ?_, walActive, walActive.symm ▸ walChoices⟩, ?_, committed,
    abstract, modeled, ?_, ?_⟩
  · rw [directory]
    exact pair
  · rw [directory]
    rfl
  · have loadedCheckpoint : manifest.elim (Except.ok PackedTable.empty)
        (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) = .ok base := by
      cases manifest <;> exact actualBase
    rw [loadedCheckpoint]
    exact replayed
  · rw [← refined.committed, agrees.committed, committed]
  · intro snapshot retained within
    have floor : reference.pins.floor ≤ snapshot := by simpa only [refined.pins] using retained
    have upper : snapshot ≤ reference.committed := UInt64.le_iff_toNat_le.mpr (by
      simpa only [agrees.committed, committed] using within)
    simpa only [refined.table] using agreesSymm.acquireAt_reads floor upper

/-- Once the checkpoint loader and file reads succeed, an exact settled
history replays successfully and takes the aligned durability path. This
states progress under a successful sync report. -/
theorem reopenSettledHistory_completes {initial before : ReopenImage}
    {manifest : Option ByteArray} {covered pending : List WAL.Write}
    (settled : initial.SettledFor manifest (covered ++ pending))
    (fits : (WAL.encode (covered ++ pending)).size < UInt64.size)
    (attempts : MarkedReopenAttempts initial before)
    (reads : MarkedReopenReads before) {base : PackedTable} {marker contents : ByteArray}
    (checkpointRead : reads.checkpoint = .ok base)
    (markerRead : reads.marker = .ok (some marker))
    (walRead : reads.wal = .ok (some contents))
    (watermark : covered.length = base.committed.toNat)
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending))
    (report : Publication.Step → RepairReport) :
    ∃ table, runMarkedReopen reads.preflight report false .success before =
      .ok table before.syncDirectory := by
  have exactHistory := exactHistory_after_attempts settled fits attempts
  have markerEq : marker = encode (WAL.encode (covered ++ pending)).size.toUInt64 :=
    Option.some.inj ((reads.markerVisible _ markerRead).symm.trans
      (congrArg DirectoryPublication.Bindings.walBoundary exactHistory.1.activeValid))
  have contentsEq : contents = WAL.encode (covered ++ pending) :=
    Option.some.inj ((reads.walVisible _ walRead).symm.trans exactHistory.2.activeValid)
  subst marker contents
  let bytes := WAL.encode (covered ++ pending)
  have selected : select bytes.size.toUInt64 bytes = .ok bytes := by
    simpa [bytes] using select_encoded (covered ++ pending) ByteArray.empty fits
  obtain ⟨table, replayed, _⟩ := recoverSelected_encoded_complete base covered pending ordered watermark
  have recovered : recoverMarked base bytes.size.toUInt64 bytes = .ok (bytes, table) := by
    unfold recoverMarked
    rw [selected]
    change (recoverSelected base bytes >>= fun loaded => Except.ok (bytes, loaded)) = _
    rw [replayed]
    rfl
  have preflight : reads.preflight = .ok ⟨bytes, bytes, table⟩ := by
    unfold MarkedReopenReads.preflight markedReopenPreflight
    rw [checkpointRead]
    change (withOpenWal reads.marker reads.wal id _ _) = _
    rw [markerRead, withOpenWal_marked, decode_encode, walRead]
    change (recoverMarked base bytes.size.toUInt64 bytes >>= fun (selected, loaded) =>
      Except.ok (⟨bytes, selected, loaded⟩ : MarkedPreflight)) = _
    rw [recovered]
    rfl
  refine ⟨table, ?_⟩
  rw [preflight]
  simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen, Nat.lt_irrefl, ↓reduceIte]
  rfl

end Alvoki.WAL.Boundary
