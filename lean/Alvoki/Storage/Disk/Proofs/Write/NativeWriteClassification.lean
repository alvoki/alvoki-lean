import Alvoki.Storage.Disk.Proofs.Write.ClientWriteTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

/-- A successful native no-follow guard determines the exact metadata
that was checked, including the regular-file, link and extent tests. -/
theorem BatchActiveGuard.ofChecked {directory : DiskDirectory} {installed : Installed}
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (checked : checkActiveSegmentWith directory installed lookup = .ok ()) :
    ∃ guard : BatchActiveGuard directory installed, guard.lookup = lookup := by
  cases found : lookup (directory.file (.walSegment installed.activeFirst)) with
  | error cause =>
    simp [checkActiveSegmentWith, found, Bind.bind, Except.bind] at checked
  | ok metadata =>
    have allowed : (metadata.type == .file && metadata.numLinks == 1) = true := by
      cases safe : metadata.type == .file && metadata.numLinks == 1
      · simp [checkActiveSegmentWith, found, checkPrivateRegularWith, Bind.bind, Except.bind, safe,
          throw, throwThe, MonadExceptOf.throw] at checked
      · rfl
    have kind : metadata.type = .file := by
      have kind := (Bool.and_eq_true_iff.mp allowed).1
      cases reported : metadata.type
      case file => rfl
      all_goals
        rw [reported] at kind
        cases kind
    have privateFile : metadata.numLinks = 1 := by
      simpa using (Bool.and_eq_true_iff.mp allowed).2
    have extent : metadata.byteSize.toNat = installed.walBytes - installed.activeFirst * WAL.frameSize := by
      by_cases same : metadata.byteSize.toNat = installed.walBytes - installed.activeFirst * WAL.frameSize
      · exact same
      · simp [checkActiveSegmentWith, found, checkPrivateRegularWith, Bind.bind, Except.bind, allowed,
          same, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at checked
    exact ⟨⟨lookup, metadata, found, kind, privateFile, extent⟩, rfl⟩

/-- A reached nonempty request before the first phase assignment. The
metadata and prepared rows are computed from the actual request. -/
structure CheckedWriteRequest (request : WriteRequest) (directory : DiskDirectory)
    (installed : Installed) (lookup : FilePath → Except IO.Error IO.FS.Metadata) where
  batch : List WAL.Write
  table : PackedTable
  nonempty : request.rows ≠ []
  fits : installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size
  prepared : prepareBatch installed.table request.rows = some (batch, table)
  guard : BatchActiveGuard directory installed
  sameLookup : guard.lookup = lookup

namespace CheckedWriteRequest

variable {request : WriteRequest} {directory : DiskDirectory} {installed : Installed}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata}

def next (checked : CheckedWriteRequest request directory installed lookup) : Installed :=
  { installed with table := checked.table, walBytes := installed.walBytes + WAL.frameSize * request.rows.length }

end CheckedWriteRequest

/-- A classified return of the shared production dispatch. The last
argument is indexed by the exact response and reached file/cache state.
The accepted branches record the same cached commit callback's result. -/
inductive ReadyWriteReturn {image : Type} (request : WriteRequest) (directory : DiskDirectory)
    (installed : Installed) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit)
    (before : LockedFileState image) : EStateM.Result DiskWriteError (Phase Installed × LockedFileState image) UInt64 → Prop where
  | empty (rows : request.rows = []) :
      ReadyWriteReturn request directory installed lookup append stage sync rename before
        (.ok installed.table.committed (.ready installed, before))
  | rejected {cause : IO.Error} (guard : BatchPreflightRejection directory installed request.rows lookup cause) :
      ReadyWriteReturn request directory installed lookup append stage sync rename before
        (.error (.rejected cause) (.ready installed, before))
  | acknowledged (checked : CheckedWriteRequest request directory installed lookup) {reached : image}
      (committed : commitBytesAt directory installed.activeFirst (WAL.encodeBatch checked.batch) checked.next.walBytes
        append stage sync rename before.image = .ok () reached) :
      ReadyWriteReturn request directory installed lookup append stage sync rename before
        (.ok checked.table.committed (.ready checked.next, { before with image := reached }))
  | uncertain (checked : CheckedWriteRequest request directory installed lookup) {error : IO.Error} {reached : image}
      (failed : commitBytesAt directory installed.activeFirst (WAL.encodeBatch checked.batch) checked.next.walBytes
        append stage sync rename before.image = .error error reached) :
      ReadyWriteReturn request directory installed lookup append stage sync rename before
        (.error (.commitUnknown error) (.poisoned, { before with image := reached }))

/-- Classify the exact result of either returned native write schedule
from one fixed set of callbacks. No preselected guard, success or error
branch is supplied. The singleton rewrite requires a retained-ready
writer, which prevents its earlier sequence guard from masking a count
error. The acknowledged and uncertain cases inspect the same commit. -/
theorem WriteRequest.classifiesReadyReturn {image : Type} {directory : DiskDirectory} {descriptor : Nat}
    {writer : SegmentedWriterState} (ready : writer.RetainedReady directory descriptor)
    (request : WriteRequest) (before : LockedFileState image)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    ReadyWriteReturn request directory writer.installed lookup append stage sync rename before
      (request.runReported directory lookup append stage sync rename (.ready writer.installed, before)) := by
  rw [request.runReported_eq_batch ready]
  by_cases empty : request.rows = []
  · rw [show runBatchWrite directory request.rows lookup append stage sync rename (.ready writer.installed, before) =
        .ok writer.installed.table.committed (.ready writer.installed, before) from
      empty ▸ runBatchWrite_empty directory writer.installed before lookup append stage sync rename]
    exact .empty empty
  by_cases fits : writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size
  · cases prepared : prepareBatch writer.installed.table request.rows with
    | none =>
      have rejected := BatchPreflightRejection.sequence (directory := directory) (lookup := lookup) empty fits prepared
      rw [rejected.run before append stage sync rename]
      exact .rejected rejected
    | some pair =>
      obtain ⟨batch, table⟩ := pair
      cases checked : checkActiveSegmentWith directory writer.installed lookup with
      | error cause =>
        have rejected := BatchPreflightRejection.active empty fits prepared checked
        rw [rejected.run before append stage sync rename]
        exact .rejected rejected
      | ok result =>
        cases result
        obtain ⟨guard, sameLookup⟩ := BatchActiveGuard.ofChecked lookup checked
        let selected : CheckedWriteRequest request directory writer.installed lookup :=
          ⟨batch, table, empty, fits, prepared, guard, sameLookup⟩
        cases returned : commitBytesAt directory writer.installed.activeFirst (WAL.encodeBatch batch)
            (writer.installed.walBytes + WAL.frameSize * request.rows.length) append stage sync rename before.image with
        | ok result reached =>
          cases result
          have published := runBatchWrite_acknowledges guard empty prepared fits returned
          rw [sameLookup] at published
          rw [published]
          exact .acknowledged selected returned
        | error cause reached =>
          have failed := runBatchWrite_commitUnknown guard empty prepared fits returned
          rw [sameLookup] at failed
          rw [failed]
          exact .uncertain selected returned
  · have rejected := BatchPreflightRejection.byteCount (directory := directory) (lookup := lookup) empty (Nat.le_of_not_gt fits)
    rw [rejected.run before append stage sync rename]
    exact .rejected rejected

/-- Connect a reached publication's primitive file effects to the fixed
cached callbacks. Both reports describe effects at issue and apply to
any returned result of those callbacks. -/
structure WriteCallPublication {handle : Type} {request : WriteRequest} {directory : DiskDirectory}
    {before : SegmentedWriterState} (calls : WriteRequest.Calls handle)
    (checked : CheckedWriteRequest request directory before.installed calls.lookup) where
  effects : WriteEffects
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  observed : ObservedBatchPublication directory before.installed.activeFirst (WAL.encodeBatch checked.batch)
    checked.next.walBytes (WriteFiles.initial before.history (before.files.directory.staged .walBoundary))
    append stage sync rename handle
  sameCalls : (⟨observed.cache, calls.lookup, observed.append, observed.stage, observed.sync, observed.rename⟩ :
    WriteRequest.Calls handle) = calls
  reports : BatchCommitReports directory before.installed.activeFirst before.history checked.batch checked.next.walBytes
    (effects := effects) (before.files.directory.staged .walBoundary) append stage sync rename

namespace WriteCallPublication

variable {handle : Type} {request : WriteRequest} {directory : DiskDirectory} {before : SegmentedWriterState}
  {calls : WriteRequest.Calls handle} {checked : CheckedWriteRequest request directory before.installed calls.lookup}
  (seen : WriteCallPublication calls checked)

/-- The entire commit projection follows the ordered primitive reports
and retains both the original diagnostic and the reached file image. -/
theorem projects :
    let initial := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
    withoutWriteGroupCache (commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch checked.batch)
      checked.next.walBytes calls.append calls.stage calls.sync calls.rename (calls.cache, initial)) =
    commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch checked.batch)
      checked.next.walBytes seen.append seen.stage seen.sync seen.rename initial := by
  intro initial
  let returnOf (source : WriteRequest.Calls handle) :=
    withoutWriteGroupCache (commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch checked.batch)
      checked.next.walBytes source.append source.stage source.sync source.rename (source.cache, initial))
  exact (congrArg returnOf seen.sameCalls).symm.trans seen.observed.projectsReturn

include seen in
/-- Interpret the exact committed result of one checked request. The
scoped publication describes these callbacks and the returned files. -/
theorem acknowledgesReturnedCommit {reached : SyncHandleRouting.Cache handle × WriteFiles}
    (committed : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch checked.batch)
      checked.next.walBytes calls.append calls.stage calls.sync calls.rename
      (calls.cache, WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) = .ok () reached) :
    WriteRequest.ReturnedReports request directory before handle calls := by
  have projected := seen.projects
  dsimp only at projected
  rw [committed] at projected
  let report : SegmentedBatchAppendReport directory before := {
    rows := request.rows, batch := checked.batch, table := checked.table, effects := seen.effects
    append := seen.append, stage := seen.stage, sync := seen.sync, rename := seen.rename
    written := reached.2, nonempty := checked.nonempty, prepared := checked.prepared, fits := checked.fits
    reports := seen.reports, committed := projected.symm }
  let observed : ObservedBatchWrite report handle := ⟨seen.observed, checked.guard⟩
  have same : WriteRequest.Calls.ofSuccess observed = calls := by
    unfold WriteRequest.Calls.ofSuccess
    change (⟨seen.observed.cache, checked.guard.lookup, seen.observed.append, seen.observed.stage,
      seen.observed.sync, seen.observed.rename⟩ : WriteRequest.Calls handle) = calls
    rw [checked.sameLookup, seen.sameCalls]
  exact same ▸ .acknowledged report observed rfl

end WriteCallPublication

/-- Recover the existing client-facing report from the actual schedule.
Only a checked nonempty call requests primitive effect facts, and its
observed return decides acknowledgement or uncertain commit. -/
theorem WriteRequest.Calls.classifiesReturnedReports {handle : Type} {directory : DiskDirectory} {descriptor : Nat}
    {before : SegmentedWriterState} (ready : before.RetainedReady directory descriptor)
    (calls : Calls handle) (request : WriteRequest)
    (observe : ∀ checked : CheckedWriteRequest request directory before.installed calls.lookup,
      Nonempty (WriteCallPublication calls checked)) :
    ReturnedReports request directory before handle calls := by
  have classified := request.classifiesReadyReturn ready (readyCall before calls.cache).2
    calls.lookup calls.append calls.stage calls.sync calls.rename
  generalize request.runReported directory calls.lookup calls.append calls.stage calls.sync calls.rename
    (readyCall before calls.cache) = returned at classified
  cases classified with
  | empty rows => exact .empty rows
  | rejected guard => exact .rejected guard
  | acknowledged checked committed =>
    obtain ⟨seen⟩ := observe checked
    exact seen.acknowledgesReturnedCommit committed
  | uncertain checked stopped =>
    obtain ⟨seen⟩ := observe checked
    have projected := seen.projects
    dsimp only at projected
    rw [stopped] at projected
    have scratch := ready.directoryFiles
    rw [scratch] at projected
    let failure : SegmentedBatchFailure directory before := {
      rows := request.rows, batch := checked.batch, table := checked.table, effects := seen.effects
      append := seen.append, stage := seen.stage, sync := seen.sync, rename := seen.rename
      cause := _, failed := _, nonempty := checked.nonempty, prepared := checked.prepared, fits := checked.fits
      reports := by
        rw [← scratch]
        exact seen.reports
      ran := projected.symm }
    let observed : ObservedBatchFailure failure handle := {
      cache := seen.observed.cache
      append := seen.observed.append
      stage := seen.observed.stage
      sync := seen.observed.sync
      rename := seen.observed.rename
      appendProjects := by
        rw [← scratch]
        exact seen.observed.appendProjects
      markerProjects := by
        rw [← scratch]
        exact seen.observed.markerProjects
      guard := checked.guard }
    have same : Calls.ofFailure observed = calls := by
      unfold Calls.ofFailure
      change (⟨seen.observed.cache, checked.guard.lookup, seen.observed.append, seen.observed.stage,
        seen.observed.sync, seen.observed.rename⟩ : Calls handle) = calls
      rw [checked.sameLookup, seen.sameCalls]
    exact same ▸ .unknown failure observed rfl

end Alvoki.Storage.DiskSession
