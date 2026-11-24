import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.MarkedWriteTrace

namespace Alvoki.WAL.Boundary
open Storage

private theorem appendEncoding_grows (before : List WAL.Write) (event : WAL.Write) :
    (WAL.encode before).size < (WAL.encode (before ++ [event])).size := by
  simp [WAL.frameSize, Nat.mul_add]

/-- The admissible marker lengths after a write cut satisfy the bound needed
by every subsequent repair attempt. -/
theorem writeEffects_reopenMarkerBound (before : List WAL.Write) (event : WAL.Write)
    (effects : WriteEffects) (manifest : Option ByteArray)
    {stagedMarker stagedManifest stagedWal : Option (ByteArray × Bool)}
    (fits : (WAL.encode (before ++ [event])).size < UInt64.size) :
    MarkerBound ((writeFilesAfter (runWriteEffects before event effects stagedMarker)).reopenImage
      before manifest stagedManifest stagedWal).directory := by
  have cuts := runWriteEffects_hasWriteCuts before event effects manifest stagedMarker stagedManifest stagedWal
  obtain ⟨_, _, _, cut, visible, surviving⟩ := cuts _ (List.mem_cons_self ..)
  exact ReopenImage.markerBound_of_write_cut cut
    (Nat.lt_trans (appendEncoding_grows before event) fits) fits visible.symm surviving

/-- The ordered write and marked reopen effect schedules refine the recovered
history and snapshot reads. The fixed checkpoint and initially durable WAL
describe the starting database. Each attempt observes the visible files as
specified by the filesystem contract. Every acknowledged write survives. -/
theorem recoverPreparedWriteAfterReopenAttempts {state next checkpoint : PackedTable}
    {model : Sequential.SnapshotTable UInt64} {covered pending : List WAL.Write}
    {key : UInt64} {value : Option UInt64} {event : WAL.Write}
    {manifest : Option ByteArray} {files : List ByteArray} {walBytes : Nat}
    {stagedMarker stagedManifest stagedWal : Option (ByteArray × Bool)}
    (prepared : prepareWrite state key value = some (event, next))
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending))
    (sequence : (covered ++ pending).length = state.committed.toNat)
    (walLength : walBytes = (WAL.encode (covered ++ pending)).size)
    (fits : walBytes + WAL.frameSize < UInt64.size)
    (effects : WriteEffects) {after : ReopenImage}
    (attempts : MarkedReopenAttempts
      ((writeFilesAfter (runWriteEffects (covered ++ pending) event effects stagedMarker)).reopenImage
        (covered ++ pending) manifest stagedManifest stagedWal) after)
    {pair : DirectoryPublication.Bindings} {walBinding : Option ByteArray}
    (metadataChosen : pair ∈ after.directory.active :: after.directory.crashImages)
    (walChosen : walBinding ∈ after.wal.active :: after.wal.crashImages)
    (written : CheckpointForRecovery manifest files checkpoint)
    (represents : checkpoint.Refines model)
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ marker contents events base reopened abstract,
      pair.walBoundary = some marker ∧ marker = encode (WAL.encode events).size.toUInt64 ∧
      walBinding = some contents ∧
      (match pair.manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do let count ← decode marker; select count contents) = .ok (WAL.encode events) ∧
      recoverSelected base (WAL.encode events) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      (∀ writtenFiles, runWriteEffects (covered ++ pending) event effects stagedMarker = .ok () writtenFiles →
        events = (covered ++ pending) ++ [event]) ∧
      reopened.committed.toNat = events.length ∧
      SnapshotWalReplay model (events.drop covered.length) abstract ∧
      abstract.committed.toNat = events.length ∧
      ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
        ∃ pin pinned, reopened.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (abstract.table.range start stop snapshot)) := by
  let old := covered ++ pending
  let extended := old ++ [event]
  let result := runWriteEffects old event effects stagedMarker
  let physical := writeFilesAfter result
  let initial := physical.reopenImage old manifest stagedManifest stagedWal
  obtain ⟨_, _, validOrdinals, _, nextSize⟩ := prepareWrite_extends_history ordered sequence prepared
  have extendedFits : (WAL.encode extended).size < UInt64.size := by
    rwa [nextSize, ← walLength]
  have cuts := runWriteEffects_hasWriteCuts old event effects manifest stagedMarker stagedManifest stagedWal
  have nonempty := physical.reopenImage_crashWal_nonempty old manifest stagedManifest stagedWal
  have initialBound : MarkerBound initial.directory :=
    writeEffects_reopenMarkerBound old event effects manifest extendedFits
  have path := attempts.toRetry initialBound
  have checkpointAt (candidate : DirectoryPublication.Bindings)
      (chosen : candidate ∈ initial.directory.active :: initial.directory.crashImages) :
      CheckpointForRecovery candidate.manifest files checkpoint := by
    rw [physical.reopenImage_manifest_eq old manifest chosen]
    exact written
  obtain ⟨marker, contents, events, base, reopened, abstract, markerAt, markerEncoding, walAt, loaded,
      selected, recovered, history, count, abstractWrites, abstractCount, reads⟩ :=
    recoverWriteCutAfterReopenRetry path metadataChosen walChosen nonempty extendedFits cuts
      checkpointAt represents validOrdinals watermark
  refine ⟨marker, contents, events, base, reopened, abstract, markerAt, markerEncoding, walAt, loaded,
    selected, recovered, history, ?_, count, abstractWrites, abstractCount, reads⟩
  intro writtenFiles acknowledged
  have chosen := path.chosen_pair_from_initial metadataChosen
  have chosenAfterSuccess :
      let image := writtenFiles.reopenImage old manifest stagedManifest stagedWal
      pair ∈ image.directory.active :: image.directory.crashImages := by
    simpa only [initial, physical, result, acknowledged, writeFilesAfter] using chosen
  have newest := runWriteEffects_success_pair_marker acknowledged manifest chosenAfterSuccess
  have acknowledgedMarker := Option.some.inj (markerAt.symm.trans newest)
  rw [acknowledgedMarker, decode_encode] at selected
  change select (WAL.encode extended).size.toUInt64 contents = .ok (WAL.encode events) at selected
  have selectedSize := select_size selected
  rw [UInt64.toNat_ofNat_of_lt' extendedFits] at selectedSize
  rcases history with oldHistory | newHistory
  · have grows := appendEncoding_grows old event
    rw [oldHistory] at selectedSize
    exact False.elim ((Nat.ne_of_lt grows) selectedSize)
  · exact newHistory

/-- The table installed by a successful marked open has the selected
history and agrees with the abstract reads. The checkpoint and WAL reads
must follow the owned-directory filesystem contract, and the reopen
effects use the same callbacks and result as the Linux adapter.
The durable WAL and matching checkpoint describe one prepared write
followed by any number of reopen attempts and crashes. -/
theorem reopenPreparedWrite_refines {state next checkpoint table : PackedTable}
    {model : Sequential.SnapshotTable UInt64} {covered pending : List WAL.Write}
    {key : UInt64} {value : Option UInt64} {event : WAL.Write}
    {manifest : Option ByteArray} {files : List ByteArray} {walBytes : Nat}
    {stagedMarker stagedManifest stagedWal : Option (ByteArray × Bool)}
    (prepared : prepareWrite state key value = some (event, next))
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending))
    (sequence : (covered ++ pending).length = state.committed.toNat)
    (walLength : walBytes = (WAL.encode (covered ++ pending)).size)
    (fits : walBytes + WAL.frameSize < UInt64.size)
    (effects : WriteEffects) {before after : ReopenImage}
    (attempts : MarkedReopenAttempts
      ((writeFilesAfter (runWriteEffects (covered ++ pending) event effects stagedMarker)).reopenImage
        (covered ++ pending) manifest stagedManifest stagedWal) before)
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
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ events abstract,
      after.directory = before.directory.syncDirectory ∧
      after.directory.active = ⟨manifest, some (encode (WAL.encode events).size.toUInt64)⟩ ∧
      after.wal.active = some (WAL.encode events) ∧
      after.wal.crashImages = [some (WAL.encode events)] ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      (∀ writtenFiles, runWriteEffects (covered ++ pending) event effects stagedMarker = .ok () writtenFiles →
        events = (covered ++ pending) ++ [event]) ∧
      table.committed.toNat = events.length ∧
      table.RowBounds ∧
      (manifest.elim (Except.ok PackedTable.empty)
        (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun base =>
          recoverSelected base (WAL.encode events)) = .ok table ∧
      SnapshotWalReplay model (events.drop covered.length) abstract ∧
      abstract.committed.toNat = events.length ∧
      ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
        ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (abstract.table.range start stop snapshot)) := by
  let old := covered ++ pending
  let physical := writeFilesAfter (runWriteEffects old event effects stagedMarker)
  let initial := physical.reopenImage old manifest stagedManifest stagedWal
  obtain ⟨_, _, _, _, nextSize⟩ := prepareWrite_extends_history ordered sequence prepared
  have extendedFits : (WAL.encode (old ++ [event])).size < UInt64.size := by
    rwa [nextSize, ← walLength]
  have initialBound : MarkerBound initial.directory :=
    writeEffects_reopenMarkerBound old event effects manifest extendedFits
  have path := attempts.toRetry initialBound
  have chosen := path.chosen_pair_from_initial (List.mem_cons_self ..)
  have visibleManifest := physical.reopenImage_manifest_eq old manifest chosen
  obtain ⟨base, marker, contents, selected, length, checkpointOpened, markerVisible,
    walVisible, decoded, selectedResult, replayed, directory, walActive, walChoices⟩ :=
    MarkedReopenReads.success _ (path.markerBound initialBound) opened
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
  rw [sameLoaded] at actualBase
  obtain ⟨expectedMarker, expectedContents, events, expectedBase, expectedTable, abstract,
      markerAt, markerEncoding, walAt, expectedLoad, expectedSelection, expectedReplay, history, acknowledged, count,
      replay, abstractCount, reads⟩ :=
    recoverPreparedWriteAfterReopenAttempts prepared ordered sequence walLength fits effects attempts
      (pair := before.directory.active) (walBinding := before.wal.active)
      (List.mem_cons_self ..) (List.mem_cons_self ..) written represents watermark
  have sameBase := Except.ok.inj (actualBase.symm.trans expectedLoad)
  have sameMarker := Option.some.inj (markerVisible.symm.trans markerAt)
  have sameContents := Option.some.inj (walVisible.symm.trans walAt)
  rw [← sameMarker, ← sameContents, decoded] at expectedSelection
  have sameSelected := Except.ok.inj (selectedResult.symm.trans expectedSelection)
  rw [← sameBase, ← sameSelected] at expectedReplay
  have sameTable := Except.ok.inj (replayed.symm.trans expectedReplay)
  subst expectedTable
  have load : manifest.elim (Except.ok PackedTable.empty)
      (fun header => Manifest.decode header >>= fun decoded => loadRunSet decoded files) = .ok base := by
    rw [visibleManifest] at actualBase
    cases manifest <;> exact actualBase
  have recovered : (manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun base =>
        recoverSelected base (WAL.encode events)) = .ok table := by
    rw [load, ← sameSelected]
    exact replayed
  have bounded := written.recoverSelected_rowBounds recovered
  rw [sameSelected] at walActive walChoices
  have metadata : after.directory.active = ⟨manifest, some (encode (WAL.encode events).size.toUInt64)⟩ := by
    rw [directory]
    change before.directory.active = _
    calc
      before.directory.active =
          ⟨before.directory.active.manifest, before.directory.active.walBoundary⟩ := rfl
      _ = _ := by rw [visibleManifest, markerAt, markerEncoding]
  exact ⟨events, abstract, directory, metadata, walActive, walChoices, history,
    acknowledged, count, bounded, recovered, replay, abstractCount, reads⟩

/-- With a fixed checkpoint, any finite sequence of acknowledged writes and
one write reporting a publication error can be followed by crashes and open
retries. Successful open settles exactly the acknowledged history, optionally
including the last write, and returns a ready session with abstract snapshot reads. -/
theorem reopenAfterAcknowledgedWrites_refines {initial writer : MarkedWriterState}
    {submitted covered pending : List WAL.Write} {manifest : Option ByteArray}
    (ready : initial.ReadyFor manifest) (start : initial.history = covered ++ pending)
    (path : AcknowledgedWrites initial submitted writer)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {next : PackedTable}
    (prepared : prepareWrite writer.table key value = some (event, next))
    (fits : writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before after : ReopenImage}
    (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    {checkpointImage : CheckpointPublication.Image} {walSequence : UInt64}
    {checkpoint table : PackedTable} {files : List ByteArray} {model : Sequential.SnapshotTable UInt64}
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
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ events abstract,
      (⟨table, (WAL.encode events).size, after, events⟩ : MarkedWriterState).ReadyFor manifest ∧
      (events = covered ++ pending ++ submitted ∨
        events = covered ++ pending ++ submitted ++ [event]) ∧
      (manifest.elim (Except.ok PackedTable.empty)
        (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun base =>
          recoverSelected base (WAL.encode events)) = .ok table ∧
      SnapshotWalReplay model (events.drop covered.length) abstract ∧
      abstract.committed.toNat = events.length ∧
      ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
        ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ lo hi, pinned.range pin.handle lo hi = some (abstract.table.range lo hi snapshot)) := by
  obtain ⟨current, history, _⟩ := path.refines ready
  have old : writer.history = covered ++ (pending ++ submitted) := by
    rw [history, start, List.append_assoc]
  let stagedMarker := writer.image.directory.staged .walBoundary
  let stagedManifest := writer.image.directory.staged .manifest
  let stagedWal := writer.image.wal.staged
  have cutImage := runWriteEffectsFrom_failed_image current.settled failed
  have stableAttempts : MarkedReopenAttempts
      ((writeFilesAfter (runWriteEffects (covered ++ (pending ++ submitted)) event effects stagedMarker)).reopenImage
        (covered ++ (pending ++ submitted)) manifest stagedManifest stagedWal) before := by
    rw [← old, cutImage]
    exact attempts
  have ordered := old ▸ current.ordered
  have count := old ▸ current.count
  have length := old ▸ current.length
  obtain ⟨events, abstract, directory, metadata, walActive, walChoices, selected, _, committed,
      bounded, recovered, replayed, abstractCount, reads⟩ :=
    reopenPreparedWrite_refines prepared ordered count length fits effects stableAttempts
      accepted checkpointReads walReads opened written represents watermark
  have directoryChoices : after.directory.crashImages = [after.directory.active] := by
    rw [directory]
    rfl
  have settled : after.SettledFor manifest events := by
    refine ⟨metadata, directoryChoices, walActive, ?_⟩
    rwa [walActive]
  have orderedAndFits : WAL.OrdinalsFrom 1 events ∧ (WAL.encode events).size < UInt64.size := by
    obtain ⟨_, _, extended, _, size⟩ := prepareWrite_extends_history ordered count prepared
    rcases selected with rfl | rfl
    · exact ⟨ordered, length ▸ current.fits⟩
    · rw [size, ← length]
      exact ⟨extended, fits⟩
  refine ⟨events, abstract, ⟨settled, orderedAndFits.1, committed.symm, rfl, orderedAndFits.2, bounded⟩,
    ?_, recovered, replayed, abstractCount, reads⟩
  simpa only [List.append_assoc] using selected

end Alvoki.WAL.Boundary
