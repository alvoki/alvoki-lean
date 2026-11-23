import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.WalWritePublicationModel

namespace Alvoki.WAL.Boundary
open Storage

/-- The ordered write and marked reopen effect schedules refine the recovered
history and snapshot reads. The fixed checkpoint and initially durable WAL
describe the starting database. Each attempt observes the visible files as
specified by the filesystem contract. Every acknowledged write survives. -/
theorem recoverPreparedWriteAfterReopenAttempts {state next checkpoint : PackedTable}
    {model : Sequential.SnapshotTable UInt64} {covered pending : List WAL.Write}
    {key : UInt64} {value : Option UInt64} {event : WAL.Write}
    {manifest : Option ByteArray} {files : List ByteArray} {walBytes : Nat}
    (prepared : prepareWrite state key value = some (event, next))
    (ordered : WAL.OrdinalsFrom 1 (covered ++ pending))
    (sequence : (covered ++ pending).length = state.committed.toNat)
    (walLength : walBytes = (WAL.encode (covered ++ pending)).size)
    (fits : walBytes + WAL.frameSize < UInt64.size)
    (effects : WriteEffects) {after : ReopenImage}
    (attempts : MarkedReopenAttempts
      ((writeFilesAfter (runWriteEffects (covered ++ pending) event effects)).reopenImage
        (covered ++ pending) manifest) after)
    {pair : DirectoryPublication.Bindings} {walBinding : Option ByteArray}
    (metadataChosen : pair ∈ after.directory.active :: after.directory.crashImages)
    (walChosen : walBinding ∈ after.wal.active :: after.wal.crashImages)
    (written : CheckpointForRecovery manifest files checkpoint)
    (represents : checkpoint.Refines model)
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ marker contents events base reopened abstract,
      pair.walBoundary = some marker ∧ walBinding = some contents ∧
      (match pair.manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do
        let count ← decode marker
        let selected ← select count contents
        recoverSelected base selected) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      (∀ writtenFiles, runWriteEffects (covered ++ pending) event effects = .ok () writtenFiles →
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
  let result := runWriteEffects old event effects
  let physical := writeFilesAfter result
  obtain ⟨_, _, validOrdinals, _, nextSize⟩ := prepareWrite_extends_history ordered sequence prepared
  have extendedFits : (WAL.encode extended).size < UInt64.size := by
    rwa [nextSize, ← walLength]
  have oldShorter : (WAL.encode old).size < (WAL.encode extended).size := by
    change (WAL.encode (covered ++ pending)).size < (WAL.encode ((covered ++ pending) ++ [event])).size
    rw [nextSize]
    have : 0 < WAL.frameSize := by decide
    omega
  have cuts := runWriteEffects_hasWriteCuts old event effects manifest
  have nonempty := physical.reopenImage_crashWal_nonempty old manifest
  obtain ⟨_, _, _, cut, visible, surviving⟩ :=
    cuts (physical.reopenImage old manifest).wal.active (List.mem_cons_self ..)
  have initialBound := ReopenImage.markerBound_of_write_cut cut
    (Nat.lt_trans oldShorter extendedFits) extendedFits visible.symm surviving
  have path := attempts.toRetry initialBound
  have checkpointAt (candidate : DirectoryPublication.Bindings)
      (chosen : candidate ∈ (physical.reopenImage old manifest).directory.active ::
        (physical.reopenImage old manifest).directory.crashImages) :
      CheckpointForRecovery candidate.manifest files checkpoint := by
    rw [physical.reopenImage_manifest_eq old manifest chosen]
    exact written
  obtain ⟨marker, contents, events, base, reopened, abstract, markerAt, walAt, loaded,
      recovered, history, count, abstractWrites, abstractCount, reads⟩ :=
    recoverWriteCutAfterReopenRetry path metadataChosen walChosen nonempty extendedFits cuts
      checkpointAt represents validOrdinals watermark
  refine ⟨marker, contents, events, base, reopened, abstract, markerAt, walAt, loaded,
    recovered, history, ?_, count, abstractWrites, abstractCount, reads⟩
  intro writtenFiles acknowledged
  have chosen := path.chosen_pair_from_initial metadataChosen
  have chosenAfterSuccess : pair ∈ (writtenFiles.reopenImage old manifest).directory.active ::
      (writtenFiles.reopenImage old manifest).directory.crashImages := by
    simpa only [acknowledged, writeFilesAfter] using chosen
  have newest := runWriteEffects_success_pair_marker acknowledged manifest chosenAfterSuccess
  have valid := reopenRetry_valid (ReopenImage.valid_of_writeCut nonempty extendedFits cuts) path
  obtain ⟨_, _, markerVisible, walVisible, recoveredInput⟩ :=
    ReopenImage.recover_chosen valid base metadataChosen walChosen
  rw [← Option.some.inj (markerAt.symm.trans markerVisible),
    ← Option.some.inj (walAt.symm.trans walVisible), recovered] at recoveredInput
  have extendedPrefix : writeCutPrefix old event pair = WAL.encode extended := by
    simp only [writeCutPrefix, newest, Option.map_some, decode_encode]
    change (if (UInt64.ofNat (WAL.encode extended).size).toNat = (WAL.encode old).size then
      WAL.encode old else WAL.encode extended) = WAL.encode extended
    rw [UInt64.toNat_ofNat_of_lt' extendedFits, ite_eq_right (Nat.ne_of_gt oldShorter)]
  rw [extendedPrefix] at recoveredInput
  have atCheckpoint := checkpointAt pair chosen
  obtain ⟨loadedBase, loadedBaseResult, same⟩ := atCheckpoint.loads
  have baseMatches := Except.ok.inj (loadedBaseResult.symm.trans loaded)
  subst loadedBase
  have baseWatermark : covered.length = base.committed.toNat := by
    simpa only [same.committed] using watermark
  have ordinals' : WAL.OrdinalsFrom 1 (covered ++ (pending ++ [event])) := by
    simpa only [List.append_assoc] using validOrdinals
  obtain ⟨extendedState, extendedReplay, extendedCount⟩ :=
    recoverSelected_encoded_complete base covered (pending ++ [event]) ordinals' baseWatermark
  rw [← List.append_assoc] at extendedReplay
  have sameResult := Except.ok.inj (recoveredInput.trans extendedReplay)
  rcases history with oldHistory | newHistory
  · apply False.elim
    simp only [oldHistory, List.length_append, List.length_singleton] at count extendedCount
    rw [sameResult] at count
    omega
  · exact newHistory

end Alvoki.WAL.Boundary
