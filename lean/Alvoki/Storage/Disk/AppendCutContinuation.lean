import Alvoki.Storage.Disk.AppendCutSession
import Alvoki.Storage.Disk.ReopenedSegmentAppend

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- Continue from the very session returned by bounded open after the
failed append. The next submission is prepared from that
table. Once its active-file guard and actual commit callbacks succeed,
the shared publication tail acknowledges its consecutive sequence under
the same lock and the keeper is durable for the extended history. -/
theorem AppendCutReady.acknowledgeNext {directory descriptor liveRefs history published initial target generation result}
    (opened : AppendCutReady directory descriptor liveRefs history published initial target generation result) :
    ∃ checkpoint session final previous,
      result = .ok session final ∧ session.phase = .ready previous ∧ final.owners.Owns directory descriptor ∧
      final.image.directory.project .walBoundary =
        (WriteFiles.initial history (final.image.directory.staged .walBoundary)).marker ∧
      ∀ (key : UInt64) (value : Option UInt64),
        previous.walBytes + frameSize < UInt64.size →
        ∃ event table, prepareWrite previous.table key value = some (event, table) ∧
          ∀ (effects : WriteEffects)
            (append write : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
            (sync : Array FilePath → EStateM IO.Error WriteFiles Unit)
            (rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit) (written : WriteFiles),
            let scratch := final.image.directory.staged .walBoundary
            let next := { previous with table, walBytes := previous.walBytes + frameSize }
            let commit := commitAt directory previous.activeFirst event next.walBytes append write sync rename
            AppendCommitReports directory previous.activeFirst history event next.walBytes
              effects scratch append write sync rename →
            commit (WriteFiles.initial history scratch) = .ok () written →
            let after := resumedAppendFiles final.image history previous.activeFirst written
            event.sequence.toNat = history.length + 1 ∧
            runPreparedWrite next event.sequence commit
                (.ready previous, ⟨WriteFiles.initial history scratch, final.owners⟩) =
              .ok event.sequence (.ready next, ⟨written, final.owners⟩) ∧
            after.kept = initial.kept ∧ ∃ nextTarget,
              nextTarget.pair = ⟨target.pair.manifest, some (WAL.Boundary.encode next.walBytes.toUInt64)⟩ ∧
              ResumedAppendReady next after nextTarget (history ++ [event]) published checkpoint := by
  obtain ⟨through, trimmed, accepted, ordered, checkpoint, recovered, model, session, final, ran, loaded,
    sameGeneration, _, _, _, ready, durable, sealed, held, committed, bounds, refines, represents, _, _, _, _⟩ := opened
  let previous : Installed := ⟨recovered, generation, (WAL.encode history).size, target.first⟩
  have readyToAppend : ResumedAppendReady previous final.image target history published checkpoint :=
    ⟨durable, through, rfl, rfl, trimmed, sameGeneration, loaded, accepted, ordered, bounds,
      ⟨model, refines, represents⟩⟩
  refine ⟨checkpoint, session, final, previous, ran, ready, held, readyToAppend.markerImage, ?_⟩
  intro key value fits
  have sequenceFits : recovered.committed.toNat + 1 < UInt64.size := by
    change (WAL.encode history).size + frameSize < UInt64.size at fits
    rw [WAL.encode_size] at fits
    simp only [WAL.frameSize, committed] at fits ⊢
    omega
  obtain ⟨event, table, prepared⟩ : ∃ event table, prepareWrite previous.table key value = some (event, table) := by
    simp [previous, prepareWrite, PackedTable.write, sequenceFits]
  refine ⟨event, table, prepared, ?_⟩
  intro effects append write sync rename written scratch next commit reports done after
  obtain ⟨_, ordinal, nextTarget, pair, _, nextReady⟩ :=
    readyToAppend.acknowledged directory prepared fits effects append write sync rename reports done
  have kept := (resumedAppendFiles_retains final.image history previous.activeFirst written).1.trans sealed
  exact ⟨ordinal, runPreparedWrite_success previous next event.sequence done, kept, nextTarget, pair, nextReady⟩

end Alvoki.Storage.DiskSession
