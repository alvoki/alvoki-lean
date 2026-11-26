import Alvoki.Storage.Disk.NativeWalPayloadReturn

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
      (failed : readCachedWalPayloads directory through readSeal readKeeper required entry = .error cause reached)
      (ordered : CachedWalPayloadReturn directory through readSeal readKeeper required entry (.error cause reached)) :
      SelectedWalPayloadReturn directory watermark through readSeal readKeeper extents entry (.error cause reached)
  | payloadReturned {required : List (Nat × IO.FS.Metadata)} {later : List Nat}
      {files : List (Nat × ByteArray)} {size : Nat} {reached : heap}
      (selected : selectWalExtentsThrough extents watermark through = some (required, later))
      (read : readCachedWalPayloads directory through readSeal readKeeper required entry = .ok (files, size) reached)
      (ordered : CachedWalPayloadReturn directory through readSeal readKeeper required entry (.ok (files, size) reached)) :
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
  rw [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate]
  by_cases checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize
  · simp only [ite_eq_left checked, Bind.bind, EStateM.bind]
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
          have ordered := CachedWalPayloadReturn.classifies directory (length.toNat / frameSize)
            readSeal readKeeper required afterScan
          cases payload : readCachedWalPayloads directory (length.toNat / frameSize) readSeal readKeeper required afterScan with
          | error cause reached => exact .payloadError selection payload (by simpa only [payload] using ordered)
          | ok reads reached =>
            obtain ⟨files, size⟩ := reads
            exact .payloadReturned selection payload (by simpa only [payload] using ordered)
  · simpa [checked, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using
      (SelectedWalReadReturn.invalidMarker (directory := directory) (list := list) (lstat := lstat)
        (readSeal := readSeal) (readKeeper := readKeeper) (entry := entry) checked)

/-- A successful selected read supplies the one reached listing and scan,
the selected extents and later names, and the exact payload returns. -/
theorem SelectedWalReadReturn.successfulPayloads
    {directory : DiskDirectory} {watermark : Nat} {length : UInt64}
    {list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    {entry reached : heap} {reads : WalSegmentMarkerReads} {size : Nat}
    (observed : SelectedWalReadReturn directory watermark length list lstat readSeal readKeeper entry
      (.ok (reads, size) reached)) :
    ∃ entries listed extents scanned required,
      (length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize) ∧
      list directory.path entry = .ok entries listed ∧
      readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) listed = .ok extents scanned ∧
      selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, reads.newer) ∧
      readCachedWalPayloads directory (length.toNat / frameSize) readSeal readKeeper required scanned =
        .ok (reads.files, size) reached ∧
      CachedWalPayloadReturn directory (length.toNat / frameSize) readSeal readKeeper required scanned
        (.ok (reads.files, size) reached) := by
  cases observed with
  | scanned checked listed scan payload =>
    cases payload with
    | payloadReturned selected read ordered =>
      exact ⟨_, _, _, _, _, checked, listed, scan, selected, read, ordered⟩

/-- A completed probe is either a noncanonical name, a positive stat, or
an exact Linux ENOENT. The positive result keeps the stat's metadata intact. -/
private theorem returnedExtentResult (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {name : String} {before reached : heap} {found : Option (Nat × IO.FS.Metadata)}
    (returned : readWalSegmentExtentWith directory lstat name before = .ok found reached) :
    (parseWalSegmentName name = none ∧ found = none) ∨
      ∃ first, parseWalSegmentName name = some first ∧
        ((∃ metadata, lstat (directory.file (.walSegment first)) before = .ok (.ok metadata) reached ∧
          found = some (first, metadata)) ∨
        (∃ filename message, lstat (directory.file (.walSegment first)) before =
          .ok (.error (.noFileOrDirectory filename 2 message)) reached ∧ found = none)) := by
  cases parsed : parseWalSegmentName name with
  | none =>
    simp [readWalSegmentExtentWith, parsed, Pure.pure, EStateM.pure] at returned
    exact .inl ⟨rfl, returned.1.symm⟩
  | some first =>
    refine .inr ⟨first, rfl, ?_⟩
    simp only [readWalSegmentExtentWith, parsed, Bind.bind, EStateM.bind] at returned
    cases probed : lstat (directory.file (.walSegment first)) before with
    | error cause after => simp [probed] at returned
    | ok report after =>
      rw [probed] at returned
      cases report with
      | ok metadata =>
        by_cases regular : (metadata.type == .file) = true
        · simp [classifyWalSegmentLookup, regular, Pure.pure, Except.toOption] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact .inl ⟨metadata, rfl, rfl⟩
        · simp [classifyWalSegmentLookup, regular, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      | error cause =>
        cases cause <;> simp [classifyWalSegmentLookup, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
        rename_i filename code message
        by_cases missing : code = 2
        · subst code
          simp [Pure.pure, EStateM.pure] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact .inr ⟨filename, message, rfl, rfl⟩
        · simp [missing, EStateM.throw] at returned

private theorem returnedExtentOffsetOn (directory : DiskDirectory) (relevant : Nat → Bool)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {name : String} {before reached : heap} {found : Option (Nat × IO.FS.Metadata)}
    (returned : readWalSegmentExtentWith directory lstat name before = .ok found reached)
    (present : ∀ {first statHeap filename message}, parseWalSegmentName name = some first → relevant first = true →
      lstat (directory.file (.walSegment first)) before ≠
        .ok (.error (.noFileOrDirectory filename 2 message)) statHeap) :
    (found.map Prod.fst).filter relevant = (parseWalSegmentName name).filter relevant := by
  rcases returnedExtentResult directory lstat returned with ⟨parsed, rfl⟩ | ⟨first, parsed, positive | missing⟩
  · simp only [parsed, Option.map_none]
  · obtain ⟨metadata, _, rfl⟩ := positive
    simp only [parsed, Option.map_some]
  · obtain ⟨_, _, stat, rfl⟩ := missing
    cases kept : relevant first with
    | false => simp [parsed, Option.filter, kept]
    | true => exact (present parsed kept stat).elim

private theorem filterMapM_extend {α β : Type}
    (read : α → EStateM IO.Error heap (Option β)) (scanned : List α) (name : α)
    {entry before after : heap} {found : List β} {value : Option β}
    (earlier : (scanned.filterMapM read) entry = .ok found before)
    (called : read name before = .ok value after) :
    ((scanned ++ [name]).filterMapM read) entry = .ok (found ++ value.toList) after := by
  induction scanned generalizing entry found with
  | nil =>
    simp [Pure.pure, EStateM.pure] at earlier
    obtain ⟨rfl, rfl⟩ := earlier
    cases value <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, called, Pure.pure, EStateM.pure]
  | cons first rest ih =>
    cases head : read first entry with
    | error cause reached => simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head] at earlier
    | ok kept atTail =>
      cases tail : (rest.filterMapM read) atTail with
      | error cause reached =>
        cases kept <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, tail] at earlier
      | ok foundTail next =>
        have extended := ih (entry := atTail) (found := foundTail)
        cases kept <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, tail,
          Pure.pure, EStateM.pure] at earlier <;> obtain ⟨rfl, rfl⟩ := earlier <;>
          simp [List.cons_append, List.filterMapM_cons, Bind.bind, EStateM.bind, head, extended tail,
            Pure.pure, EStateM.pure]

private theorem filterMapM_member {α β : Type} (read : α → EStateM IO.Error heap (Option β))
    (names : List α) {entry reached : heap} {found : List β} {value : β}
    (returned : (names.filterMapM read) entry = .ok found reached) (member : value ∈ found) :
    ∃ earlier name rest collected issued after,
      names = earlier ++ name :: rest ∧
      (earlier.filterMapM read) entry = .ok collected issued ∧
      read name issued = .ok (some value) after := by
  induction names generalizing entry reached found with
  | nil =>
    simp [Pure.pure, EStateM.pure] at returned
    obtain ⟨rfl, _⟩ := returned
    simp at member
  | cons name rest ih =>
    cases head : read name entry with
    | error cause after => simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head] at returned
    | ok kept after =>
      cases tail : (rest.filterMapM read) after with
      | error cause atError =>
        cases kept <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, tail] at returned
      | ok collected atEnd =>
        have prepend (member : value ∈ collected) :
            ∃ earlier issuedName remaining previous issued afterRead,
              name :: rest = earlier ++ issuedName :: remaining ∧
              (earlier.filterMapM read) entry = .ok previous issued ∧
              read issuedName issued = .ok (some value) afterRead := by
          obtain ⟨earlier, issuedName, remaining, previous, issued, afterRead, order, scanned, probed⟩ := ih tail member
          refine ⟨name :: earlier, issuedName, remaining, kept.toList ++ previous, issued, afterRead,
            congrArg (List.cons name) order, ?_, probed⟩
          cases kept <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, scanned, Pure.pure, EStateM.pure]
        cases kept with
        | none =>
          simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, tail] at returned
          obtain ⟨rfl, _⟩ := returned
          exact prepend member
        | some kept =>
          simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, tail, Pure.pure, EStateM.pure] at returned
          obtain ⟨rfl, _⟩ := returned
          rcases List.mem_cons.mp member with rfl | inTail
          · exact ⟨[], name, rest, [], entry, after, rfl, rfl, head⟩
          · exact prepend inTail

/-- Sorting only reorders the retained extents. Each returned pair was
admitted by the exact stat at its reached position in the original list. -/
theorem readWalSegmentExtentsWith_memberStat (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (names : List String) {entry reached : heap} {extents : List (Nat × IO.FS.Metadata)}
    {first : Nat} {metadata : IO.FS.Metadata}
    (returned : readWalSegmentExtentsWith directory lstat names entry = .ok extents reached)
    (member : (first, metadata) ∈ extents) :
    ∃ earlier name rest collected issued after,
      names = earlier ++ name :: rest ∧ parseWalSegmentName name = some first ∧
      (earlier.filterMapM (readWalSegmentExtentWith directory lstat)) entry = .ok collected issued ∧
      lstat (directory.file (.walSegment first)) issued = .ok (.ok metadata) after := by
  let read := readWalSegmentExtentWith directory lstat
  change ((names.filterMapM read) >>= fun result => pure (result.mergeSort _)) entry = _ at returned
  cases scanned : (names.filterMapM read) entry with
  | error cause after =>
    simp [Bind.bind, EStateM.bind, scanned] at returned
  | ok values after =>
    simp [Bind.bind, EStateM.bind, scanned,
      Pure.pure, EStateM.pure] at returned
    obtain ⟨rfl, rfl⟩ := returned
    obtain ⟨earlier, name, rest, collected, issued, after, order, steps, called⟩ :=
      filterMapM_member read names scanned (List.mem_mergeSort.mp member)
    rcases returnedExtentResult directory lstat called with ⟨_, contradiction⟩ | ⟨offset, parsed, positive | missing⟩
    · cases contradiction
    · obtain ⟨exactMetadata, probed, same⟩ := positive
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨earlier, name, rest, collected, issued, after, order, parsed, steps, probed⟩
    · obtain ⟨_, _, _, contradiction⟩ := missing
      cases contradiction

private theorem sortedOffsets (offsets : List Nat) : offsets.mergeSort.Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun _ _ _ ab bc => decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
    (fun a b => Bool.or_eq_true_iff.mpr ((Nat.le_total a b).imp decide_eq_true decide_eq_true)) offsets).imp
      (fun bound => of_decide_eq_true bound)

/-- The sorted extent scan retains every relevant listed offset whose
reached probe cannot report ENOENT. Other offsets can be omitted. -/
theorem readWalSegmentExtentsWith_exactOffsetsOn (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (names : List String) (relevant : Nat → Bool) {before reached : heap} {extents : List (Nat × IO.FS.Metadata)}
    (scanned : readWalSegmentExtentsWith directory lstat names before = .ok extents reached)
    (present : ∀ {scanned rest : List String} {name : String} {first : Nat},
      names = scanned ++ name :: rest → parseWalSegmentName name = some first → relevant first = true →
      ∀ {earlier : List (Nat × IO.FS.Metadata)} {atStat after filename message},
      (scanned.filterMapM (readWalSegmentExtentWith directory lstat)) before = .ok earlier atStat →
      lstat (directory.file (.walSegment first)) atStat ≠ .ok (.error (.noFileOrDirectory filename 2 message)) after) :
    (extents.map Prod.fst).Pairwise (· ≤ ·) ∧
      ((extents.map Prod.fst).filter relevant).Perm ((names.filterMap parseWalSegmentName).filter relevant) := by
  let probe := readWalSegmentExtentWith directory lstat
  have collect (items scanned : List String) (order : names = scanned ++ items) {atStat after : heap}
      {earlier results : List (Nat × IO.FS.Metadata)}
      (entered : (scanned.filterMapM probe) before = .ok earlier atStat)
      (returned : (items.filterMapM probe) atStat = .ok results after) :
      (results.map Prod.fst).filter relevant = (items.filterMap parseWalSegmentName).filter relevant := by
    induction items generalizing scanned atStat after earlier results with
    | nil =>
      simp [Pure.pure, EStateM.pure] at returned
      rw [returned.1]
      rfl
    | cons name rest ih =>
      cases head : probe name atStat with
      | error cause heap => simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head] at returned
      | ok value heap =>
        have offset := returnedExtentOffsetOn directory relevant lstat head
          (fun parsed kept missing => present order parsed kept entered missing)
        have enteredTail := filterMapM_extend probe scanned name entered head
        have restOrder : names = (scanned ++ [name]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using order
        cases runTail : (rest.filterMapM probe) heap with
        | error cause reached =>
          cases value <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, runTail] at returned
        | ok values next =>
          have map := ih (scanned ++ [name]) restOrder enteredTail runTail
          have complete : ((name :: rest).filterMapM probe) atStat = .ok (value.toList ++ values) next := by
            cases value <;> simp [List.filterMapM_cons, Bind.bind, EStateM.bind, head, runTail, Pure.pure, EStateM.pure]
          obtain ⟨rfl, _⟩ := EStateM.Result.ok.inj (returned.symm.trans complete)
          have listed : (name :: rest).filterMap parseWalSegmentName =
              (parseWalSegmentName name).toList ++ rest.filterMap parseWalSegmentName := by
            cases parsed : parseWalSegmentName name <;> simp [parsed]
          rw [listed, List.map_append, List.filter_append, List.filter_append, map,
            ← Option.toList_map, ← Option.toList_filter, ← Option.toList_filter, offset]
  change ((names.filterMapM probe) >>= fun result => pure (result.mergeSort _)) before = _ at scanned
  cases collected : (names.filterMapM probe) before with
  | error cause after => simp [Bind.bind, EStateM.bind, collected] at scanned
  | ok entries after =>
    simp [Bind.bind, EStateM.bind, collected, Pure.pure, EStateM.pure] at scanned
    obtain ⟨rfl, _⟩ := scanned
    rw [List.map_mergeSort (f := Prod.fst) (s := fun a b : Nat => decide (a ≤ b)) (fun _ _ _ _ => rfl)]
    exact ⟨sortedOffsets _, ((List.mergeSort_perm _ _).filter relevant).trans
      (collect names [] rfl rfl collected ▸ List.Perm.refl _)⟩

/-- With truthful absence for every canonical name, the scan retains
exactly the sorted offsets of the listing. -/
theorem readWalSegmentExtentsWith_exactOffsets (directory : DiskDirectory)
    (lstat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (names : List String) {before reached : heap} {extents : List (Nat × IO.FS.Metadata)}
    (scanned : readWalSegmentExtentsWith directory lstat names before = .ok extents reached)
    (present : ∀ {scanned rest : List String} {name : String} {first : Nat},
      names = scanned ++ name :: rest → parseWalSegmentName name = some first →
      ∀ {earlier : List (Nat × IO.FS.Metadata)} {atStat after filename message},
      (scanned.filterMapM (readWalSegmentExtentWith directory lstat)) before = .ok earlier atStat →
      lstat (directory.file (.walSegment first)) atStat ≠ .ok (.error (.noFileOrDirectory filename 2 message)) after) :
    extents.map Prod.fst = (names.filterMap parseWalSegmentName).mergeSort := by
  obtain ⟨ordered, offsets⟩ := readWalSegmentExtentsWith_exactOffsetsOn directory lstat names (fun _ => true) scanned
    (fun order parsed _ => present order parsed)
  have keepsAll (values : List Nat) : values.filter (fun _ => true) = values :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  have all : (extents.map Prod.fst).Perm (names.filterMap parseWalSegmentName) := by
    simpa only [keepsAll] using offsets
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => Nat.le_antisymm ab ba) ordered (sortedOffsets _)
    (all.trans (List.mergeSort_perm _ _).symm)

private theorem dropWhileCovered (through : Nat) (offsets : List Nat) (ordered : offsets.Pairwise (· ≤ ·)) :
    offsets.dropWhile (fun start => decide (start ≤ through)) =
      offsets.filter (fun start => decide (through < start)) := by
  induction offsets with
  | nil => rfl
  | cons start rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    by_cases below : start ≤ through
    · simp [below, Nat.not_lt.mpr below, ih tail]
    · have later : through < start := Nat.lt_of_not_ge below
      have allLater : rest.filter (fun start => decide (through < start)) = rest :=
        List.filter_eq_self.mpr fun next inside => decide_eq_true (Nat.lt_of_lt_of_le later (before next inside))
      simp [below, later, allLater]

/-- The selector reports every present start after the marker, regardless
of which covered names it skipped before the checkpoint watermark. -/
theorem selectWalSegmentReadsThrough_later {offsets required later : List Nat} {watermark through : Nat}
    (selected : selectWalSegmentReadsThrough offsets watermark through = some (required, later))
    (covers : watermark ≤ through) (ordered : offsets.Pairwise (· ≤ ·)) :
    later = offsets.filter (fun start => decide (through < start)) := by
  unfold selectWalSegmentReadsThrough selectWalSegmentReads at selected
  cases first : (offsets.filter (fun start => decide (start ≤ watermark))).max? with
  | none => simp [first, Bind.bind, Option.bind] at selected
  | some start =>
    simp [first, Bind.bind, Option.bind, Pure.pure] at selected
    have lower := of_decide_eq_true ((List.mem_filter.mp (List.max?_mem first)).2)
    rw [← selected.2, dropWhileCovered through _ (List.Pairwise.filter _ ordered), List.filter_filter]
    apply List.filter_congr
    intro next _
    by_cases beyond : through < next
    · simp [beyond, Nat.le_trans lower (Nat.le_trans covers (Nat.le_of_lt beyond))]
    · simp [beyond]

private theorem takesBoundedOffsets (through : Nat) (offsets : List Nat)
    (ordered : offsets.Pairwise (· ≤ ·)) :
    offsets.takeWhile (fun start => decide (start ≤ through)) =
      offsets.filter (fun start => decide (start ≤ through)) := by
  induction offsets with
  | nil => rfl
  | cons start rest ih =>
    obtain ⟨following, sorted⟩ := List.pairwise_cons.mp ordered
    by_cases within : start ≤ through
    · simp [within, ih sorted]
    · have later : rest.filter (fun next => decide (next ≤ through)) = [] :=
        List.filter_eq_nil_iff.mpr fun next member found =>
          within (Nat.le_trans (following _ member) (of_decide_eq_true found))
      simp [within, later]

/-- Match the actual sorted WAL selection to a canonical recovery window.
Older names before the covering start are unconstrained. Existing names
inside that window must agree exactly, since an extra start can change
the file chosen to cover the checkpoint. Keep the actual later set. -/
theorem WalSegmentRepair.selectWalExtentsThrough_matchesWindow
    {extents required : List (Nat × IO.FS.Metadata)} {first watermark through : Nat}
    {expected later : List Nat}
    (ordered : (extents.map Prod.fst).Pairwise (· ≤ ·))
    (selected : selectWalExtentsThrough extents watermark through = some (required, later))
    (strict : (required.map Prod.fst).Pairwise (· < ·))
    (canonical : (first :: expected).Pairwise (· < ·))
    (covers : first ≤ watermark) (bounded : watermark ≤ through)
    (within : ∀ start ∈ expected, watermark < start ∧ start ≤ through)
    (catalog : ∀ start, first ≤ start → start ≤ through →
      (start ∈ extents.map Prod.fst ↔ start ∈ first :: expected)) :
    required.map Prod.fst = first :: expected ∧
      later = (extents.map Prod.fst).filter (fun start => decide (through < start)) := by
  let offsets := extents.map Prod.fst
  have present : first ∈ offsets := (catalog first (Nat.le_refl _) (Nat.le_trans covers bounded)).mpr List.mem_cons_self
  have greatest : (offsets.filter fun start => decide (start ≤ watermark)).max? = some first := by
    apply List.max?_eq_some_iff.mpr
    refine ⟨List.mem_filter.mpr ⟨present, decide_eq_true covers⟩, ?_⟩
    intro start filtered
    obtain ⟨inList, lower⟩ := List.mem_filter.mp filtered
    by_cases le : start ≤ first
    · exact le
    · exfalso
      have beyond := Nat.lt_of_not_ge le
      have atMarker := of_decide_eq_true lower
      have wanted := (catalog start (Nat.le_of_lt beyond) (Nat.le_trans atMarker bounded)).mp inList
      rcases List.mem_cons.mp wanted with rfl | expectedStart
      · exact Nat.lt_irrefl _ beyond
      · exact Nat.not_lt_of_ge atMarker (within _ expectedStart).1
  have exactOffsets := selectWalExtentsThrough_offsets extents watermark through
  rw [selected, Option.map_some] at exactOffsets
  have dropped := selectWalSegmentReadsThrough_later exactOffsets.symm bounded ordered
  have logical := exactOffsets
  change some (required.map Prod.fst, later) = selectWalSegmentReadsThrough offsets watermark through at logical
  simp only [selectWalSegmentReadsThrough, selectWalSegmentReads, greatest, Bind.bind, Option.bind, Pure.pure] at logical
  have needed := (Prod.mk.inj (Option.some.inj logical)).1
  let keeps := fun start => decide (start ≤ through) && decide (first ≤ start)
  have window : required.map Prod.fst = offsets.filter keeps := by
    rw [needed, takesBoundedOffsets through _ (List.Pairwise.filter _ ordered), List.filter_filter]
  have sorted := window ▸ strict
  have perm : (offsets.filter keeps).Perm (first :: expected) := by
    apply (List.perm_ext_iff_of_nodup (sorted.imp Nat.ne_of_lt) (canonical.imp Nat.ne_of_lt)).mpr
    intro start
    simp only [List.mem_filter, keeps, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨member, upper, lower⟩
      exact (catalog start lower upper).mp member
    · intro member
      have range : first ≤ start ∧ start ≤ through := by
        rcases List.mem_cons.mp member with rfl | among
        · exact ⟨Nat.le_refl _, Nat.le_trans covers bounded⟩
        · exact ⟨Nat.le_trans covers (Nat.le_of_lt (within _ among).1), (within _ among).2⟩
      exact ⟨(catalog start range.1 range.2).mpr member, range.2, range.1⟩
  exact ⟨window.trans (List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => False.elim (Nat.lt_asymm ab ba))
    sorted canonical perm), dropped⟩

end Alvoki.Storage
