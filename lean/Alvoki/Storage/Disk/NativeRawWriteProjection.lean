import Alvoki.Storage.Disk.NativeOpenWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit SyncHandleRouting WAL.Boundary

section AcknowledgedWrite

variable {heap handle : Type} {directory : DiskDirectory}
  {writer : SegmentedWriterState} {descriptor : Nat}

/-- Project an acknowledged raw write through its reached callbacks.
The guard and setters frame the file projection. The append and each
issued publication callback carry their own result, including the
reached cache. The logical dispatcher derives its acknowledgement
from this projection of the same raw return. The checked request and
the commit it actually issued suffice to classify that return. -/
theorem WriteRequest.runOnRawOpenPhase_projectsAcknowledged
    (request : WriteRequest) (ready : writer.RetainedReady directory descriptor) (calls : Calls handle)
    (observe : heap → Cache handle × WriteFiles)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    {entry reached : heap} {batch : List WAL.Write} {table : PackedTable} {sequence : UInt64}
    (loaded : get phase entry = .ok (.ready writer.installed) entry)
    (initial : observe entry = (readyCall writer calls.cache).2.image)
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch writer.installed.table request.rows = some (batch, table))
    (fits : writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (returned : request.runOnRawOpenPhase directory lookup append stage sync rename phase get set entry =
      .ok sequence reached)
    (lookupProjects : ∀ {metadata after},
      lookup (directory.file (.walSegment writer.installed.activeFirst)) entry = .ok metadata after →
      calls.lookup (directory.file (.walSegment writer.installed.activeFirst)) = .ok metadata ∧
        observe after = observe entry)
    (setFrames : ∀ {value before after}, set phase value before = .ok () after → observe after = observe before)
    (appendProjects : ∀ {guarded poisoned},
      checkActiveSegmentWith directory writer.installed lookup entry = .ok () guarded →
      set phase .poisoned guarded = .ok () poisoned →
      let path := directory.file (.walSegment writer.installed.activeFirst)
      projectResult observe (append path (WAL.encodeBatch batch) poisoned) =
        calls.append path (WAL.encodeBatch batch) (observe poisoned))
    (markerProjects : ∀ {guarded poisoned},
      checkActiveSegmentWith directory writer.installed lookup entry = .ok () guarded →
      set phase .poisoned guarded = .ok () poisoned →
      let first := writer.installed.activeFirst
      let count := writer.installed.walBytes + WAL.frameSize * request.rows.length
      ∀ appended, append (directory.file (.walSegment first)) (WAL.encodeBatch batch) poisoned = .ok () appended →
      ∀ (prior : List Publication.Step) step remaining before, Publication.steps = prior ++ step :: remaining →
      let actual := performMarkerAt directory first count stage sync rename
      (prior.forM actual) appended = .ok () before →
      projectResult observe (actual step before) =
        performMarkerAt directory first count calls.stage calls.sync calls.rename step (observe before)) :
    let count := writer.installed.walBytes + WAL.frameSize * request.rows.length
    let next : Installed := { writer.installed with table, walBytes := count }
    calls.run request directory writer = .ok sequence (.ready next, ⟨observe reached, writer.owners⟩) ∧
    ∃ checked : CheckedWriteRequest request directory writer.installed calls.lookup,
      checked.batch = batch ∧ checked.next = next ∧
      commitBytesAt directory writer.installed.activeFirst (WAL.encodeBatch checked.batch)
        checked.next.walBytes calls.append calls.stage calls.sync calls.rename (readyCall writer calls.cache).2.image =
        .ok () (observe reached) := by
  intro count next
  obtain ⟨guarded, poisoned, settled, guard, excluded, committed, installed, number, checked, lookedUp⟩ :=
    request.runOnRawOpenPhase_acknowledges directory lookup append stage sync rename phase get set
      loaded nonempty prepared fits returned
  obtain ⟨selected, guardFrame⟩ := lookupProjects lookedUp
  let projectedGuard : BatchActiveGuard directory writer.installed :=
    ⟨calls.lookup, checked.metadata, selected, checked.regular, checked.privateFile, checked.extent⟩
  have poisonedImage : observe poisoned = (readyCall writer calls.cache).2.image :=
    (setFrames excluded).trans (guardFrame.trans initial)
  have projected := commitBytesAt_projects observe directory writer.installed.activeFirst (WAL.encodeBatch batch)
    next.walBytes append stage sync rename calls.append calls.stage calls.sync calls.rename
    poisoned (appendProjects guard excluded) (markerProjects guard excluded)
  rw [committed, poisonedImage] at projected
  have imageReturn : commitBytesAt directory writer.installed.activeFirst (WAL.encodeBatch batch)
      next.walBytes calls.append calls.stage calls.sync calls.rename (readyCall writer calls.cache).2.image =
        .ok () (observe reached) := by
    simpa only [projectResult, setFrames installed] using projected.symm
  have accepted := runBatchWrite_acknowledges projectedGuard nonempty prepared fits imageReturn
  refine ⟨?_, ⟨⟨batch, table, nonempty, fits, prepared, projectedGuard, rfl⟩, rfl, rfl, imageReturn⟩⟩
  rw [Calls.run, request.runReported_eq_batch ready, number]
  exact accepted

end AcknowledgedWrite
end Alvoki.Storage.DiskSession
