import Alvoki.Storage.Disk.AppendRetrySession
import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WAL.Boundary

/-- A physical observation while the first append callback is still in
flight. The preceding keeper prefix is durable. The callback has yet to
return, so no marker operation has been reached. -/
structure FirstAppendCut where
  visibleTail : ByteArray
  crashTails : List ByteArray

namespace FirstAppendCut

/-- The existing write-effect interpreter can represent this file image.
The error tag stops its modeled schedule and supplies no native report. -/
def writeEffects (cut : FirstAppendCut) : WriteEffects :=
  ⟨.error cut.visibleTail, cut.crashTails, .ok (), .ok (), .success, .success⟩

def writeFiles (cut : FirstAppendCut) (history : List WAL.Write) (scratch : Option (ByteArray × Bool)) :
    WriteFiles :=
  ⟨cut.visibleTail, ByteArray.empty :: cut.crashTails, (WriteFiles.initial history scratch).marker,
    by simp⟩

theorem modeledFiles (cut : FirstAppendCut) (history : List WAL.Write) (event : WAL.Write)
    (scratch : Option (ByteArray × Bool)) :
    writeFilesAfter (runWriteEffects history event cut.writeEffects scratch) = cut.writeFiles history scratch := rfl

/-- The first callback adds bytes only to the existing keeper. The actual
metadata, sealed files, later names and unrelated staging are inherited. -/
def physical (cut : FirstAppendCut) (before : SegmentedWriterState) : FileImage :=
  let written := cut.writeFiles before.history (before.files.directory.staged .walBoundary)
  let segment := written.reopenSegment before.wal.active.first before.history before.files.directory.active.manifest
  { before.files with keeper := { segment.wal with staged := before.files.keeper.staged } }

private theorem keeperSurvivors (cut : FirstAppendCut) (before : SegmentedWriterState) :
    (cut.physical before).keeper.crashImages = (ByteArray.empty :: cut.crashTails).map
      (fun tail => some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) := rfl

/-- Power loss chooses a surviving tail and ends the held writer lock
while the append is still in flight. It starts the same bounded retry
trace used after other cuts, without a returned write outcome. -/
theorem startsRetry (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.Ready directory descriptor) (event : WAL.Write)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails) :
    let files := cut.physical before
    let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ tail
    BoundedReopenTrace directory (AppendRetryTarget before.history event before.wal.active.first)
      ⟨files, before.owners⟩
      ⟨files.crash before.target.pair (some bytes) [], before.owners.set (directory.file .lock) none⟩ := by
  intro files bytes
  apply BoundedReopenTrace.powerLoss BoundedReopenTrace.empty
  · change before.target.pair ∈ before.files.directory.crashImages
    rw [ready.resumed.ready.settled]
    exact List.mem_singleton_self _
  · change some bytes ∈ (cut.physical before).keeper.crashImages
    rw [cut.keeperSurvivors]
    exact List.mem_map_of_mem survives
  · change [] ∈ before.files.later.crashImages
    rw [ready.resumed.ready.pruned.2]
    exact List.mem_singleton_self _

/-- Each crash choice during the first append retains the old absolute
marker. Even a full surviving frame lies outside it. The selected keeper
and immutable sealed segments decode to the exact prior history. -/
theorem selectsPriorHistory (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.Ready directory descriptor)
    {pair : DirectoryPublication.Bindings} (metadata : pair ∈ (cut.physical before).directory.crashImages)
    {keeper : Option ByteArray} (payload : keeper ∈ (cut.physical before).keeper.crashImages)
    {later : List Nat} (names : later ∈ (cut.physical before).later.crashImages) :
    let crashed := (cut.physical before).crash pair keeper later
    crashed.directory = .settled before.target.pair ∧ crashed.kept = before.files.kept ∧
    crashed.later.DurablyEmpty ∧
    crashed.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
    ∃ bytes, crashed.keeper.active = some bytes ∧ crashed.keeper.crashImages = [some bytes] ∧
      (crashed.directory.active.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained before.installed.activeFirst count bytes) = .ok (some before.wal.active.bytes) ∧
      WAL.decodeOrdinals (WalSegment.concatenate before.wal.segments) = .ok before.history := by
  intro crashed
  change pair ∈ before.files.directory.crashImages at metadata
  rw [ready.resumed.ready.settled] at metadata
  have selectedPair := List.mem_singleton.mp metadata
  subst pair
  change later ∈ before.files.later.crashImages at names
  rw [ready.resumed.ready.pruned.2] at names
  have empty := List.mem_singleton.mp names
  subst later
  rw [cut.keeperSurvivors] at payload
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp payload
  have exactMarker := congrArg Publication.Image.active ready.resumed.markerImage
  change before.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64)
    at exactMarker
  rw [ready.resumed.ready.selected] at exactMarker
  have keeperBytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have accepts : before.target.Accepts
      (some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) := by
    refine ⟨tail, ?_⟩
    rw [ready.resumed.contents, ready.active]
  have selected := before.target.selectKeeper exactMarker (WAL.Boundary.decode_encode _) accepts
  rw [← ready.resumed.keeper, keeperBytes] at selected
  refine ⟨rfl, rfl, ⟨rfl, rfl⟩, exactMarker, _, rfl, rfl, ?_, ?_⟩
  · change ((before.target.pair.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained before.installed.activeFirst count
          (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) : Except String (Option ByteArray)) = _
    rw [exactMarker, Option.mapM, WAL.Boundary.decode_encode]
    change (some <$> selectRetained before.installed.activeFirst (WAL.encode before.history).size.toUInt64
      (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) = _
    rw [selected]
    rfl
  · rw [ready.chain.concatenate_eq, List.drop_zero]
    exact WAL.decodeOrdinals_encode _ ready.resumed.ordered

end FirstAppendCut

end Alvoki.Storage.DiskSession
