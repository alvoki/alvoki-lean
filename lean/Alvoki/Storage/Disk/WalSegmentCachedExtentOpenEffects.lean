import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen
import Alvoki.Storage.Disk.WalSegmentRetryReadEffects

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- The exact inventory observations are read-only in the repair interpreter. -/
theorem readWalSegmentExtentsWith_liftReports {state : Type} (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) :
    (readWalSegmentExtentsWith dir (fun path => liftExcept (lstat path)) names :
      EStateM IO.Error state (List (Nat × IO.FS.Metadata))) =
      liftExcept (readWalSegmentExtentsWith dir lstat names) := by
  have extent (name : String) :
      (readWalSegmentExtentWith dir (fun path => liftExcept (lstat path)) name :
        EStateM IO.Error state (Option (Nat × IO.FS.Metadata))) =
        liftExcept (readWalSegmentExtentWith dir lstat name) := by
    unfold readWalSegmentExtentWith
    cases parseWalSegmentName name with
    | none => rfl
    | some first =>
      dsimp only
      rw [← bind_readReport (lstat (dir.file (.walSegment first)))]
      congr 1
      funext report
      cases classifyWalSegmentLookup (dir.file (.walSegment first)) first report with
      | error _ => rfl
      | ok selected => cases selected <;> rfl
  unfold readWalSegmentExtentsWith
  rw [show readWalSegmentExtentWith dir (fun path => liftExcept (lstat path)) =
    (fun name => liftExcept (readWalSegmentExtentWith dir lstat name)) from funext extent,
    filterMapM_readReport, ← bind_readReport]
  rfl

/-- Exact accepted reports reach the selected bytes and keeper extent before
any repair callback and leave the interpreter state untouched. -/
theorem readSelectedWithCachedExtents_reportedEffects {state : Type} (dir : DiskDirectory)
    (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list dir.path = .ok entries)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith dir lstat (entries.toList.map (·.fileName)) = .ok extents)
    (selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, newer))
    {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports dir (length.toNat / frameSize) readSeal readKeeper required files fileSize)
    (initial : state) :
    readSelectedWithCachedExtents (m := EStateM IO.Error state) dir watermark length (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path count => liftExcept (readSeal path count))
      (fun path count size => liftExcept (readKeeper path count size)) initial =
        .ok (⟨files, newer⟩, fileSize) initial := by
  have exactList : (liftExcept (list dir.path) : EStateM IO.Error state (Array IO.FS.DirEntry)) initial =
      .ok entries initial := by rw [listed]; rfl
  have exactScan : readWalSegmentExtentsWith (m := EStateM IO.Error state) dir (fun path => liftExcept (lstat path))
      (entries.toList.map (·.fileName)) initial = .ok extents initial := by
    rw [readWalSegmentExtentsWith_liftReports, scanned]
    rfl
  have exactPayload :=
    congrFun (readCachedWalPayloads_reportedEffects (state := state) reports) initial
  simp [readSelectedWithCachedExtents, checked, Bind.bind, EStateM.bind, exactList, exactScan, selected,
    exactPayload, Pure.pure, EStateM.pure]

end Alvoki.Storage.WalSegmentRepair
