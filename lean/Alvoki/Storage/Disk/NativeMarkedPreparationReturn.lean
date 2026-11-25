import Alvoki.Storage.Disk.NativeWalSelectionReturn

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

variable {heap : Type}

/-- Replay uses the checkpoint and exactly the selected WAL result. All
replay checks are pure and stay on the heap reached by the WAL reader. -/
inductive MarkedReplayReturn (base : PackedTable) (generation length : UInt64) :
    EStateM.Result IO.Error heap (WalSegmentMarkerReads × Nat) →
    EStateM.Result IO.Error heap (Plan × Reopened × Nat) → Prop where
  | walError (cause : IO.Error) (reached : heap) :
      MarkedReplayReturn base generation length (.error cause reached) (.error cause reached)
  | replayError {reads : WalSegmentMarkerReads} {size : Nat} {reached : heap} {cause : String}
      (rejected : recoverMarkedWalSegments base length reads.files = .error cause) :
      MarkedReplayReturn base generation length (.ok (reads, size) reached) (.error (IO.userError cause) reached)
  | noKeeper {reads : WalSegmentMarkerReads} {size : Nat} {reached : heap} {selected : ByteArray} {table : PackedTable}
      (replayed : recoverMarkedWalSegments base length reads.files = .ok (selected, table))
      (absent : reads.files.getLast? = none) :
      MarkedReplayReturn base generation length (.ok (reads, size) reached)
        (.error (IO.userError "no WAL segment covers the commit marker") reached)
  | prepared {reads : WalSegmentMarkerReads} {size keeper : Nat} {reached : heap}
      {selected bytes : ByteArray} {table : PackedTable}
      (replayed : recoverMarkedWalSegments base length reads.files = .ok (selected, table))
      (found : reads.files.getLast? = some (keeper, bytes)) :
      MarkedReplayReturn base generation length (.ok (reads, size) reached)
        (.ok (⟨length.toNat / frameSize, keeper, reads.newer, bytes⟩, ⟨table, generation, length, keeper⟩, size) reached)

/-- The reached checkpoint and canonical marker determine the selected WAL
worker input. Its ordinary result is classified and then used unchanged
for replay. Earlier errors stop before the later callbacks. -/
inductive MarkedPreparationReturn (directory : DiskDirectory)
    (readCheckpoint : EStateM IO.Error heap (Option (PackedTable × UInt64)))
    (readOptional : FilePath → EStateM IO.Error heap (Option ByteArray))
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    EStateM.Result IO.Error heap (Plan × Reopened × Nat) → Prop where
  | checkpointError {cause : IO.Error} {reached : heap}
      (failed : readCheckpoint entry = .error cause reached) :
      MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry (.error cause reached)
  | markerError {checkpoint : Option (PackedTable × UInt64)} {afterCheckpoint reached : heap} {cause : IO.Error}
      (read : readCheckpoint entry = .ok checkpoint afterCheckpoint)
      (failed : readOptional (directory.file .walBoundary) afterCheckpoint = .error cause reached) :
      MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry (.error cause reached)
  | missingMarker {checkpoint : Option (PackedTable × UInt64)} {afterCheckpoint reached : heap}
      (read : readCheckpoint entry = .ok checkpoint afterCheckpoint)
      (absent : readOptional (directory.file .walBoundary) afterCheckpoint = .ok none reached) :
      MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry
        (.error (IO.userError "segmented WAL is missing its commit marker") reached)
  | invalidMarker {checkpoint : Option (PackedTable × UInt64)} {marker : ByteArray}
      {afterCheckpoint reached : heap} {cause : String}
      (read : readCheckpoint entry = .ok checkpoint afterCheckpoint)
      (found : readOptional (directory.file .walBoundary) afterCheckpoint = .ok (some marker) reached)
      (rejected : WAL.Boundary.decode marker = .error cause) :
      MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry
        (.error (IO.userError cause) reached)
  | wal {checkpoint : Option (PackedTable × UInt64)} {marker : ByteArray} {length : UInt64}
      {afterCheckpoint afterMarker : heap}
      {result : EStateM.Result IO.Error heap (Plan × Reopened × Nat)}
      (read : readCheckpoint entry = .ok checkpoint afterCheckpoint)
      (found : readOptional (directory.file .walBoundary) afterCheckpoint = .ok (some marker) afterMarker)
      (decoded : WAL.Boundary.decode marker = .ok length)
      (selected : SelectedWalReadReturn directory (checkpoint.getD (.empty, 0)).1.committed.toNat length
        list lstat readSeal readKeeper afterMarker
        (readSelectedWithCachedExtents directory (checkpoint.getD (.empty, 0)).1.committed.toNat length
          list lstat readSeal readKeeper afterMarker))
      (replayed : MarkedReplayReturn (checkpoint.getD (.empty, 0)).1 (checkpoint.getD (.empty, 0)).2 length
        (readSelectedWithCachedExtents directory (checkpoint.getD (.empty, 0)).1.committed.toNat length
          list lstat readSeal readKeeper afterMarker) result) :
      MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry result

/-- Classify the actual ordinary read-only preparation from its fixed
callbacks, including the reached guard, scan or payload result of the
cached WAL worker. No success or rejection report is an input. -/
theorem MarkedPreparationReturn.classifies (directory : DiskDirectory)
    (readCheckpoint : EStateM IO.Error heap (Option (PackedTable × UInt64)))
    (readOptional : FilePath → EStateM IO.Error heap (Option ByteArray))
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry
      (prepareBoundedMarkedFromReaders directory readCheckpoint readOptional
        (fun watermark length => readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper)
        entry) := by
  simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind]
  cases checked : readCheckpoint entry with
  | error cause reached => exact .checkpointError checked
  | ok checkpoint afterCheckpoint =>
    dsimp only
    cases markerRead : readOptional (directory.file .walBoundary) afterCheckpoint with
    | error cause reached => exact .markerError checked markerRead
    | ok found afterMarker =>
      cases found with
      | none => exact .missingMarker checked markerRead
      | some marker =>
        dsimp only
        cases decoded : WAL.Boundary.decode marker with
        | error cause =>
          simpa [decoded, liftExcept, Except.mapError, Bind.bind, EStateM.bind, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw] using
            (MarkedPreparationReturn.invalidMarker (list := list) (lstat := lstat) (readSeal := readSeal)
              (readKeeper := readKeeper) checked markerRead decoded)
        | ok length =>
          have selected := SelectedWalReadReturn.classifies directory (checkpoint.getD (.empty, 0)).1.committed.toNat
            length list lstat readSeal readKeeper afterMarker
          refine .wal checked markerRead decoded selected ?_
          simp only [liftExcept, Except.mapError, Pure.pure, EStateM.pure, EStateM.bind]
          cases walRead : readSelectedWithCachedExtents directory (checkpoint.getD (.empty, 0)).1.committed.toNat length
              list lstat readSeal readKeeper afterMarker with
          | error cause reached => exact .walError cause reached
          | ok payload reached =>
            obtain ⟨reads, size⟩ := payload
            dsimp only
            cases replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length reads.files with
            | error cause =>
              simpa [replayed, liftExcept, Except.mapError, Bind.bind, EStateM.bind, throw, throwThe,
                MonadExceptOf.throw, EStateM.throw] using
                (MarkedReplayReturn.replayError (generation := (checkpoint.getD (.empty, 0)).2) (size := size)
                  (reached := reached) replayed)
            | ok replay =>
              obtain ⟨selected, table⟩ := replay
              simp only [EStateM.pure]
              cases found : reads.files.getLast? with
              | none => exact .noKeeper replayed found
              | some payload =>
                obtain ⟨keeper, bytes⟩ := payload
                exact .prepared replayed found

/-- The production cached-extent marked worker invokes the finisher only
after that preparation succeeds, with the exact plan, result and heap it
produced. A preparation error is the returned worker error on that heap. -/
theorem reopenMarkedBoundedWithCachedExtents_classifies (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error heap (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error heap Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) (entry : heap) :
    let readCheckpoint := readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
      readRunSize readRunPrefix
    let prepared := prepareBoundedMarkedFromReaders directory readCheckpoint readOptional
      (fun watermark length => readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper)
      entry
    let returned := reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper remove write sync rename entry
    MarkedPreparationReturn directory readCheckpoint readOptional list lstat readSeal readKeeper entry prepared ∧
      match prepared with
      | .error cause reached => returned = .error cause reached
      | .ok (plan, opened, size) reached =>
        returned = ((finishBoundedMarkedOpen directory plan size remove write sync rename) >>= fun _ => pure opened) reached := by
  intro readCheckpoint prepared returned
  refine ⟨MarkedPreparationReturn.classifies directory readCheckpoint readOptional list lstat readSeal readKeeper entry, ?_⟩
  simp only [returned, reopenMarkedBoundedWithCachedExtents, Bind.bind, EStateM.bind]
  rw [show prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (readOptional (directory.file .manifest)) readRunSize readRunPrefix)
    readOptional (fun watermark length => readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper)
    entry = prepared from rfl]
  cases prepared with
  | error cause reached => rfl
  | ok payload reached =>
    obtain ⟨plan, opened, size⟩ := payload
    rfl

end Alvoki.Storage.WalSegmentRepair
