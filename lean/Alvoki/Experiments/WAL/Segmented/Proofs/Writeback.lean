import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Writeback

namespace WalRecoverySlice.Segmented

open Model (Disk)
open Persistence (WalFile)

/-- A selected sealed segment already has its durable image. Writeback can
therefore change a selected file only in the active segment, where the
single-segment recovery invariant admits that exact file's settlement. -/
theorem Readable.writeback {control history pending disk} (readable : Readable control history pending disk)
    (id : Nat) (file : WalFile) : Readable control history pending (disk.writeback id file) := by
  refine ⟨readable.layout.frame readable.layout.names ?_, readable.room, ?_, ?_⟩
  · intro i selected sealed
    by_cases hit : i = id
    · simpa [Disk.writeback, hit] using file.settle_clean (disk.segment i) (readable.layout.sealed i selected sealed).2
    · simp [Disk.writeback, hit]
  · by_cases hit : control.active = id
    · simpa [Disk.writeback, hit] using
        readable.active.writeback (file.writeback (disk.segment control.active))
    · simpa [Disk.writeback, hit] using readable.active
  · intro log
    by_cases hit : control.active = id
    · simpa [Disk.writeback, hit] using
        (file.writeback (disk.segment control.active)).keepsMarkersSettled (readable.logMarkers log)
    · simpa [Disk.writeback, hit] using readable.logMarkers log

/-- Each authority keeps its own file-selection invariant across the same
physical writeback, including when the two controls select different active IDs. -/
theorem Recoverable.writeback {known request disk} (recoverable : Recoverable known request disk)
    (id : Nat) (file : WalFile) : Recoverable known request (disk.writeback id file) := by
  have preserve {c} (choice : RecoveryChoice known request c disk) :
      RecoveryChoice known request c (disk.writeback id file) := by
    obtain ⟨history, pending, readable, permitted⟩ := choice
    exact ⟨history, pending, readable.writeback id file, permitted⟩
  obtain ⟨c, live, chosen⟩ := recoverable.live
  obtain ⟨d, durable, other⟩ := recoverable.durable
  exact ⟨⟨c, live, preserve chosen⟩, ⟨d, durable, preserve other⟩⟩

end WalRecoverySlice.Segmented
