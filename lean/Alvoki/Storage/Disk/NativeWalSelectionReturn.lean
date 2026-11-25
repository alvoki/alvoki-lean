import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen

namespace Alvoki.Storage

open System WalSegmentRepair
open WAL (frameSize)

variable {heap : Type}

/-- On an ordinary extent scan failure, every earlier listed name is
processed in order. The failing name selects an exact canonical path and
the fixed no-follow callback is entered on the heap left by that prefix. -/
def WalExtentScanFailure (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (names : List String) (entry : heap) (cause : IO.Error) (reached : heap) : Prop :=
  ∃ prefixNames name remaining found atIssue first,
    names = prefixNames ++ name :: remaining ∧
    (prefixNames.filterMapM (readWalSegmentExtentWith directory lstat)) entry = .ok found atIssue ∧
    parseWalSegmentName name = some first ∧
    let path := directory.file (.walSegment first)
    lstat path atIssue = .error cause reached ∨
      ∃ reported, lstat path atIssue = .ok reported reached ∧
        classifyWalSegmentLookup path first reported = .error cause

private theorem filterMapM_firstError {α β : Type} (read : α → EStateM IO.Error heap (Option β))
    (names : List α) {entry reached : heap} {cause : IO.Error}
    (failed : (names.filterMapM read) entry = .error cause reached) :
    ∃ prefixNames name remaining found atIssue,
      names = prefixNames ++ name :: remaining ∧
      (prefixNames.filterMapM read) entry = .ok found atIssue ∧ read name atIssue = .error cause reached := by
  induction names generalizing entry with
  | nil => simp [Pure.pure, EStateM.pure] at failed
  | cons name rest ih =>
    cases first : read name entry with
    | error error after =>
      have failedFirst : read name entry = .error cause reached := by
        simp only [List.filterMapM_cons, Bind.bind, EStateM.bind, first, EStateM.Result.error.injEq] at failed
        obtain ⟨rfl, rfl⟩ := failed
        exact first
      exact ⟨[], name, rest, [], entry, rfl, rfl, failedFirst⟩
    | ok result after =>
      have failedRest : (rest.filterMapM read) after = .error cause reached := by
        cases tail : (rest.filterMapM read) after with
        | error error next =>
          cases result <;>
            simpa only [List.filterMapM_cons, Bind.bind, EStateM.bind, first, tail] using failed
        | ok values next =>
          cases result <;>
            simp [List.filterMapM_cons, Bind.bind, EStateM.bind, first, tail, Pure.pure, EStateM.pure] at failed
      obtain ⟨prefixNames, failedName, remaining, found, atIssue, order, prefixRead, rejected⟩ := ih failedRest
      refine ⟨name :: prefixNames, failedName, remaining, result.toList ++ found, atIssue,
        congrArg (List.cons name) order, ?_, rejected⟩
      cases result <;>
        simp [List.filterMapM_cons, Bind.bind, EStateM.bind, first, prefixRead, Pure.pure, EStateM.pure]

/-- Take the error out of the actual ordered scan. The canonical callback
can itself fail, or its returned no-follow result can fail the native
classifier. Sorting and payload reads are downstream of this scan. -/
theorem readWalSegmentExtentsWith_firstError (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (names : List String) {entry reached : heap} {cause : IO.Error}
    (failed : readWalSegmentExtentsWith directory lstat names entry = .error cause reached) :
    WalExtentScanFailure directory lstat names entry cause reached := by
  have scanFailed : (names.filterMapM (readWalSegmentExtentWith directory lstat)) entry = .error cause reached := by
    cases scanned : (names.filterMapM (readWalSegmentExtentWith directory lstat)) entry with
    | error error after =>
      simpa [readWalSegmentExtentsWith, Bind.bind, EStateM.bind, scanned] using failed
    | ok extents after =>
      simp [readWalSegmentExtentsWith, Bind.bind, EStateM.bind, scanned, Pure.pure, EStateM.pure] at failed
  obtain ⟨prefixNames, name, remaining, found, atIssue, order, prefixRead, rejected⟩ :=
    filterMapM_firstError _ names scanFailed
  cases parsed : parseWalSegmentName name with
  | none => simp [readWalSegmentExtentWith, parsed, Pure.pure, EStateM.pure] at rejected
  | some first =>
    refine ⟨prefixNames, name, remaining, found, atIssue, first, order, prefixRead, parsed, ?_⟩
    dsimp only
    unfold readWalSegmentExtentWith at rejected
    simp only [parsed, Bind.bind, EStateM.bind] at rejected
    cases issued : lstat (directory.file (.walSegment first)) atIssue with
    | error error after =>
      simp only [issued, EStateM.Result.error.injEq] at rejected
      obtain ⟨rfl, rfl⟩ := rejected
      exact .inl rfl
    | ok reported after =>
      rw [issued] at rejected
      cases classified : classifyWalSegmentLookup (directory.file (.walSegment first)) first reported with
      | error error =>
        simp [classified, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at rejected
        obtain ⟨rfl, rfl⟩ := rejected
        exact .inr ⟨reported, rfl, classified⟩
      | ok accepted =>
        cases accepted <;> simp [classified, Pure.pure, EStateM.pure] at rejected

/-- After a successful scan, the pure selection either returns the absent
coverage diagnostic or determines the exact ordered payload read and later
names. The payload worker receives the scan's reached heap. -/
inductive SelectedWalPayloadReturn (directory : DiskDirectory) (watermark through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    (extents : List (Nat × IO.FS.Metadata)) (entry : heap) :
    EStateM.Result IO.Error heap (WalSegmentMarkerReads × Nat) → Prop where
  | noCoverage (absent : selectWalExtentsThrough extents watermark through = none) :
      SelectedWalPayloadReturn directory watermark through readSeal readKeeper extents entry
        (.error (IO.userError "no WAL segment covers the checkpoint watermark") entry)
  | payloadError {required : List (Nat × IO.FS.Metadata)} {later : List Nat}
      {cause : IO.Error} {reached : heap}
      (selected : selectWalExtentsThrough extents watermark through = some (required, later))
      (failed : readCachedWalPayloads directory through readSeal readKeeper required entry = .error cause reached) :
      SelectedWalPayloadReturn directory watermark through readSeal readKeeper extents entry (.error cause reached)
  | payloadReturned {required : List (Nat × IO.FS.Metadata)} {later : List Nat}
      {files : List (Nat × ByteArray)} {size : Nat} {reached : heap}
      (selected : selectWalExtentsThrough extents watermark through = some (required, later))
      (read : readCachedWalPayloads directory through readSeal readKeeper required entry = .ok (files, size) reached) :
      SelectedWalPayloadReturn directory watermark through readSeal readKeeper extents entry
        (.ok (⟨files, later⟩, size) reached)

/-- The actual ordinary selected WAL reader either stops at its guard, at
its one directory listing, at the first failing extent, or reaches the
payload decision with the exact successful scan observation. -/
inductive SelectedWalReadReturn (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    EStateM.Result IO.Error heap (WalSegmentMarkerReads × Nat) → Prop where
  | invalidMarker (invalid : ¬ (length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)) :
      SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry
        (.error (IO.userError "invalid absolute WAL segment marker") entry)
  | listingError {cause : IO.Error} {reached : heap}
      (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
      (failed : list directory.path entry = .error cause reached) :
      SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry (.error cause reached)
  | extentError {entries : Array IO.FS.DirEntry} {listed reached : heap} {cause : IO.Error}
      (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
      (read : list directory.path entry = .ok entries listed)
      (failed : WalExtentScanFailure directory lstat (entries.toList.map (·.fileName)) listed cause reached) :
      SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry (.error cause reached)
  | scanned {entries : Array IO.FS.DirEntry} {listed scanned : heap} {extents : List (Nat × IO.FS.Metadata)}
      {result : EStateM.Result IO.Error heap (WalSegmentMarkerReads × Nat)}
      (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
      (read : list directory.path entry = .ok entries listed)
      (scan : readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) listed = .ok extents scanned)
      (payload : SelectedWalPayloadReturn directory watermark (length.toNat / frameSize)
        readSeal readKeeper extents scanned result) :
      SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry result

/-- Derive the ordinary outcome from one fixed execution of the production
selected WAL worker. No classified outcome or successful payload is an
input. Primitive identity, cleanup and interruption are separate. -/
theorem SelectedWalReadReturn.classifies (directory : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry
      (readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper entry) := by
  unfold readSelectedWithCachedExtents
  by_cases checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize
  · simp only [ite_eq_left checked, Bind.bind, EStateM.bind, Pure.pure]
    cases listed : list directory.path entry with
    | error cause reached => exact .listingError checked listed
    | ok entries afterListing =>
      dsimp only
      cases scanned : readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) afterListing with
      | error cause reached =>
        exact .extentError checked listed (readWalSegmentExtentsWith_firstError _ _ _ scanned)
      | ok extents afterScan =>
        dsimp only
        refine .scanned checked listed scanned ?_
        cases selection : selectWalExtentsThrough extents watermark (length.toNat / frameSize) with
        | none => exact .noCoverage selection
        | some chosen =>
          obtain ⟨required, later⟩ := chosen
          simp only [EStateM.bind]
          cases payload : readCachedWalPayloads directory (length.toNat / frameSize) readSeal readKeeper required afterScan with
          | error cause reached => exact .payloadError selection payload
          | ok reads reached =>
            obtain ⟨files, size⟩ := reads
            exact .payloadReturned selection payload
  · simpa [checked, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using
      (SelectedWalReadReturn.invalidMarker (directory := directory) (list := list) (lstat := lstat)
        (readSeal := readSeal) (readKeeper := readKeeper) (entry := entry) checked)

end Alvoki.Storage
