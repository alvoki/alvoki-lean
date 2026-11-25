import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeCheckpointSourceCrash

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- A nonempty acknowledged write changes the keeper and marker. The
directory, lock, selected checkpoint and seals pass through one frame.
The WAL hypotheses concern the reached ready observation, including
equality of the actual bindings in each joint crash map. -/
theorem ClassifiedWriteAcknowledgement.readyStorage {history log} {current : NativeReadPosition history log}
    {request : WriteRequest} {calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat)}
    {sequence : UInt64} {reached : OpenWriteFiles} {custody : NativePendingWriteCensus current.state reached.1}
    (ack : ClassifiedWriteAcknowledgement current request calls sequence reached custody)
    {entry returned : CheckpointStorageObservation} (old : NativeReadyStorage current.state entry)
    (framed : entry.Frames current.state.writeFramePath returned)
    (keeper : returned.files.Stored (current.state.session.directory.file (.walSegment current.state.writer.wal.active.first))
      (current.state.writer.wal.active.bytes ++ WAL.encodeBatch ack.report.batch))
    (marker : returned.files.Stored (current.state.session.directory.file .walBoundary)
      (WAL.Boundary.encode ack.report.nextInstalled.walBytes.toUInt64))
    (settledWrite : ∀ names ∈ returned.crashNames,
      names (current.state.session.directory.file (.walSegment current.state.writer.wal.active.first)) =
        returned.files.names (current.state.session.directory.file (.walSegment current.state.writer.wal.active.first)) ∧
      names (current.state.session.directory.file .walBoundary) = returned.files.names (current.state.session.directory.file .walBoundary)) :
    NativeReadyStorage ack.next.state returned := by
  have valid := current.readPrefix.refines.1
  have validNext := ack.next.readPrefix.refines.1
  let state := current.state.afterClassifiedAck ack.report ack.target reached.1 custody
  have sameManifest : state.writer.target.pair.manifest = current.state.writer.target.pair.manifest := by
    change ack.target.pair.manifest = _
    rw [ack.selected.1]
    change current.state.writer.files.directory.active.manifest = _
    exact congrArg DirectoryPublication.Bindings.manifest valid.retained.resumed.ready.selected
  have bytes : ack.report.nextInstalled.walBytes = (WAL.encode state.writer.history).size := by
    have counted := validNext.retained.resumed.bytes
    rw [ack.exactState] at counted
    exact counted
  have oldStart : current.state.writer.wal.active.first ≤ current.state.writer.history.length := by
    rw [← valid.retained.active, ← valid.retained.resumed.through]
    exact current.state.writer.target.firstCovered
  have keeperBytes : state.writer.wal.active.bytes =
      current.state.writer.wal.active.bytes ++ WAL.encodeBatch ack.report.batch := by
    change WAL.encode ((current.state.writer.history ++ ack.report.batch).drop current.state.writer.wal.active.first) = _
    rw [List.drop_append_of_le_length oldStart, WAL.encode_append, valid.retained.layout.activeBytes, WAL.encodeBatch_eq]
  have paths (path) : state.writeFramePath path ↔ current.state.writeFramePath path := by
    simp only [NativeReadyState.writeFramePath, sameManifest]
    rfl
  have retained := old.toNativeReadyProtectedStorage.frame framed.visible
  have keptFiles : NativeReadyProtectedStorage state returned.files := by
    refine ⟨retained.directoryBound.trans (congrArg some custody.sameDirectory.symm),
      retained.lockBound.trans (congrArg some custody.lockInode.symm), ?_, retained.sealedFiles, ?_⟩
    · rw [sameManifest]
      exact retained.manifest
    · intro payload metadata selected decoded index within runBytes known
      rw [sameManifest] at selected
      exact retained.runs _ _ selected decoded _ within _ known
  have sameNames := framed.settledFrom fun names allowed path kept =>
    old.settled names allowed path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))
  rw [ack.exactState]
  change NativeReadyStorage state returned
  refine ⟨keptFiles, by rw [← bytes]; exact marker, by rw [keeperBytes]; exact keeper, ?_⟩
  intro names allowed path selected
  rcases NativeReadyState.crashPath_iff_write.mp selected with rfl | rfl | kept
  · exact (settledWrite names allowed).2
  · exact (settledWrite names allowed).1
  · exact sameNames names allowed path ((paths path).mp kept)

end Alvoki.Storage.DiskSession
