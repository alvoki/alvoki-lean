import Alvoki.Storage.Disk.WalSegmentBoundedOpenReports
import Alvoki.Storage.Disk.WalSegmentSizedCheckpointOpen
import Alvoki.Storage.Disk.AppendCutSession

namespace Alvoki.Storage.WalSegmentRepair

open System Manifest

/-- Run size acquisition uses the metadata at the exact path selected by
the manifest. This interprets the native regular-file guard on no-follow reports. -/
def checkpointRunSizeReport (reports : OpenPathReadReports) (path : FilePath) :
    Except IO.Error Nat := do
  let metadata ← reports.lstat path
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  pure metadata.byteSize.toNat

/-- Successful no-follow metadata and prefix reports agree with the bytes
of each selected published run. Unselected run paths need no observation. -/
structure SizedCheckpointRunReports (directory : DiskDirectory) (reports : OpenPathReadReports)
    (binding : Option ByteArray) (durable : CheckpointPublication.RunFiles) where
  readPrefix : FilePath → Nat → Except IO.Error ByteArray
  runs : ∀ bytes manifest, binding = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
    ∀ index, index < manifest.header.runCount.toNat → ∀ payload,
      durable manifest.header.generation index = some payload →
      ∃ metadata, reports.lstat (directory.file (.run manifest.header.generation index)) = .ok metadata ∧
        metadata.type = .file ∧ metadata.byteSize.toNat = payload.size ∧
        readPrefix (directory.file (.run manifest.header.generation index)) payload.size = .ok payload

private theorem getElem?_mapM_option {α β : Type} {read : α → Option β} {inputs : List α}
    {outputs : List β} (observed : inputs.mapM read = some outputs) (index : Nat) :
    outputs[index]? = inputs[index]?.bind read := by
  induction inputs generalizing outputs index with
  | nil =>
    have empty : outputs = [] := by simpa using observed.symm
    subst outputs
    simp
  | cons input rest ih =>
    cases head : read input with
    | none => simp [List.mapM_cons, head, Bind.bind, Option.bind] at observed
    | some output =>
      cases tail : rest.mapM read with
      | none => simp [List.mapM_cons, head, tail, Bind.bind, Option.bind] at observed
      | some remaining =>
        have exactList : output :: remaining = outputs := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Option.bind] using observed
        subst outputs
        cases index with
        | zero => simp [head]
        | succ index => simpa using ih tail index

private theorem loadedRun_fits {files : List ByteArray} {runs : List Alvoki.Compaction.CheckedRun}
    (parsed : files.mapM Alvoki.Compaction.CheckedRun.openBytes = .ok runs) :
    ∀ file ∈ files, file.size < USize.size := by
  induction files generalizing runs with
  | nil => simp
  | cons head rest ih =>
    cases next : Alvoki.Compaction.CheckedRun.openBytes head with
    | error message => simp [List.mapM_cons, next, Bind.bind, Except.bind] at parsed
    | ok run =>
      cases tail : rest.mapM Alvoki.Compaction.CheckedRun.openBytes with
      | error message => simp [List.mapM_cons, next, tail, Bind.bind, Except.bind] at parsed
      | ok remaining =>
        intro file member
        rcases List.mem_cons.mp member with same | later
        · rw [same, ← (Alvoki.Compaction.CheckedRun.openBytes_spec next).2]
          exact run.fits
        · exact ih tail file later

/-- A run named by an accepted manifest already has a representable byte
count. The checked loader fixes this bound for the exact durable payload. -/
theorem _root_.Alvoki.Storage.SelectedIntegrityCheckpoint.runSizeFits {durable binding checkpoint}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (visible : binding = some bytes) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    {index : Nat} (within : index < manifest.header.runCount.toNat)
    {payload : ByteArray} (stored : durable manifest.header.generation index = some payload) :
    payload.size < USize.size := by
  cases selected with
  | absent => contradiction
  | @present actual selectedManifest files table accepted reads loaded =>
    cases visible
    cases Except.ok.inj (decoded.symm.trans accepted)
    have atIndex : files[index]? = some payload := by
      simpa [List.getElem?_range within, stored] using getElem?_mapM_option reads index
    obtain ⟨_, restored⟩ := loadIntegrityRunSet_iff.mp loaded
    obtain ⟨_, parsed, _⟩ := loadRunSet_restored restored
    exact loadedRun_fits parsed payload (List.mem_of_getElem? atIndex)

/-- The strict manifest determines how many run reads are reached. -/
def selectedRunCount (binding : Option ByteArray) : Nat :=
  ((binding.bind fun bytes => (IntegrityCheckpoint.decode bytes).toOption).map
    (fun manifest => manifest.header.runCount.toNat)).getD 0

/-- Reconstruct the selected checkpoint from the actual sized callbacks and
the accepted durable run map, carrying the reached state through each run. -/
theorem SizedCheckpointRunReports.readExactWithState {state : Type} {directory reports binding durable}
    (sizes : SizedCheckpointRunReports directory reports binding durable)
    {checkpoint : Option (PackedTable × UInt64)} (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    (readManifest : EStateM IO.Error state (Option ByteArray))
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray) (initial : state) (atIndex : Nat → state)
    (manifestSeen : readManifest initial = .ok binding (atIndex 0))
    (advances : ∀ bytes manifest, binding = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
      ∀ index < manifest.header.runCount.toNat, ∀ payload,
        durable manifest.header.generation index = some payload →
          readPrefix (directory.file (.run manifest.header.generation index)) payload.size (atIndex index) =
            .ok payload (atIndex (index + 1))) :
    readIntegrityCheckpointSized directory readManifest (fun path => liftExcept (checkpointRunSizeReport reports path))
      readPrefix initial = .ok checkpoint (atIndex (selectedRunCount binding)) := by
  cases selected with
  | absent => simp [readIntegrityCheckpointSized, selectedRunCount, manifestSeen, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure]
  | @present bytes manifest files table decoded stored loaded =>
    obtain ⟨validated, restored⟩ := loadIntegrityRunSet_iff.mp loaded
    obtain ⟨count, length, stamped⟩ := (manifest.validateRuns_iff files).mp validated
    obtain ⟨_, parsed, _⟩ := loadRunSet_restored restored
    let payload (index : Nat) := files[index]?.getD ByteArray.empty
    have numberOfFiles : files.length = manifest.header.runCount.toNat := length.symm.trans count
    have exactFiles : (List.range manifest.header.runCount.toNat).map payload = files := by
      apply List.ext_getElem?
      intro index
      by_cases within : index < manifest.header.runCount.toNat
      · have fileBound : index < files.length := by rw [numberOfFiles]; exact within
        simp [payload, List.getElem?_range within, List.getElem?_eq_getElem fileBound]
      · have beyond := Nat.le_of_not_gt within
        have noIndex : (List.range manifest.header.runCount.toNat)[index]? = none :=
          List.getElem?_eq_none (by simpa using beyond)
        have noFile : files[index]? = none := List.getElem?_eq_none (numberOfFiles ▸ beyond)
        simp [noIndex, noFile]
    have filesRead := readIntegrityRunBytesSized_effects directory manifest
      (fun path => liftExcept (checkpointRunSizeReport reports path)) readPrefix atIndex payload (by
        intro index within
        have stampBound : index < manifest.runs.length := count.symm ▸ within
        have fileBound : index < files.length := length ▸ stampBound
        let stamp := manifest.runs[index]'stampBound
        have stampAt : manifest.runs[index]? = some stamp := List.getElem?_eq_getElem stampBound
        have fileAt : files[index]? = some (payload index) := by simp [payload, List.getElem?_eq_getElem fileBound]
        have durableAt : durable manifest.header.generation index = some (payload index) := by
          have mapped := getElem?_mapM_option stored index
          rw [fileAt, List.getElem?_range within] at mapped
          exact mapped.symm
        have expected := (stamped index stamp (payload index) stampAt fileAt).1
        have fits := loadedRun_fits parsed (payload index) (List.mem_of_getElem? fileAt)
        obtain ⟨metadata, stat, regular, measured, _⟩ :=
          sizes.runs bytes manifest rfl decoded index within _ durableAt
        refine ⟨stamp, stampAt, expected ▸ fits, expected, ?_, ?_⟩
        · have sized : checkpointRunSizeReport reports (directory.file (.run manifest.header.generation index)) =
              .ok stamp.byteCount.toNat := by
            simp [checkpointRunSizeReport, stat, regular, measured, expected, Bind.bind, Except.bind,
              Pure.pure, Except.pure]
            rfl
          rw [sized]
          rfl
        · rw [← expected]
          exact advances bytes manifest rfl decoded index within _ durableAt)
    have readRuns : readIntegrityRunBytesSized (m := EStateM IO.Error state) directory manifest
        (fun path => liftExcept (checkpointRunSizeReport reports path)) readPrefix (atIndex 0) =
          .ok files (atIndex manifest.header.runCount.toNat) := by
      simpa only [exactFiles] using filesRead
    have decodedState : (liftExcept ((IntegrityCheckpoint.decode bytes).mapError IO.userError) :
        EStateM IO.Error state _) (atIndex 0) = .ok manifest (atIndex 0) := by rw [decoded]; rfl
    simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, manifestSeen, decodedState, readRuns, loaded]
    simp [selectedRunCount, decoded, liftExcept, Except.mapError, Pure.pure, EStateM.pure, Except.toOption]

/-- Reconstruct the selected checkpoint in the read-only projection. -/
theorem SizedCheckpointRunReports.readExact {state : Type} {directory reports binding durable}
    (sizes : SizedCheckpointRunReports directory reports binding durable)
    {checkpoint : Option (PackedTable × UInt64)} (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    (readManifest : reports.readOptional (directory.file .manifest) = .ok binding) (initial : state) :
    (readIntegrityCheckpointSized directory (liftExcept (reports.readOptional (directory.file .manifest)))
      (fun path => liftExcept (checkpointRunSizeReport reports path))
      (fun path count => liftExcept (sizes.readPrefix path count)) : EStateM IO.Error state _) initial =
      .ok checkpoint initial := by
  apply sizes.readExactWithState selected _ _ initial (fun _ => initial)
  · rw [readManifest]
    rfl
  · intro bytes manifest visible decoded index within payload stored
    obtain ⟨_, _, _, _, read⟩ := sizes.runs bytes manifest visible decoded index within payload stored
    rw [read]
    rfl

/-- The bounded checkpoint stage and the original checkpoint stage agree
as stateful report programs. The accepted checkpoint proves each selected
payload's exact length and machine-size bound. -/
theorem HealthyBoundedWalReports.readSizedCheckpoint_eq {state : Type}
    {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint) :
    (readIntegrityCheckpointSized directory (liftExcept (raw.reports.readOptional (directory.file .manifest)))
      (fun path => liftExcept (checkpointRunSizeReport raw.reports path))
      (fun path count => liftExcept (sizes.readPrefix path count)) : EStateM IO.Error state _) =
      readIntegrityCheckpoint (m := EStateM IO.Error state)
        (liftExcept (raw.reports.readOptional (directory.file .manifest)))
        (fun generation index => liftExcept (raw.reports.readBin (directory.file (.run generation index))))
        (fun report => liftExcept (report.mapError IO.userError)) := by
  funext initial
  rw [sizes.readExact selected raw.manifest initial, readCheckpoint_liftReports]
  · rw [raw.readCheckpoint selected]
    rfl
  · intro α report
    rfl

/-- The actual sized checkpoint worker executed on held path reports. Only
preparation uses lifted reads. Repair has the same effectful callbacks. -/
def HealthyBoundedWalReports.reopenSizedCheckpointWithState {directory owners descriptor wal pair watermark durable tail}
    {state : Type}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit) : EStateM IO.Error state Reopened :=
  reopenMarkedBoundedWithSizedCheckpoint directory (fun path => liftExcept (raw.reports.readOptional path))
    (fun path => liftExcept (checkpointRunSizeReport raw.reports path))
    (fun path count => liftExcept (sizes.readPrefix path count))
    (fun path => liftExcept (raw.list path))
    (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
    (fun path => liftExcept (raw.reports.readBin path)) (fun path count => liftExcept (raw.readPrefix path count))
    removeFile write sync renameFile

/-- An installation or failure theorem for the reported bounded reopen
applies to the sized route with these exact checkpoint reports, including
the final effect state and the returned table. -/
theorem HealthyBoundedWalReports.reopenSizedCheckpointWithState_eq {directory owners descriptor wal pair watermark durable tail}
    {state : Type}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit) :
    raw.reopenSizedCheckpointWithState sizes removeFile write sync renameFile =
      raw.reopenWithState removeFile write sync renameFile := by
  unfold HealthyBoundedWalReports.reopenSizedCheckpointWithState HealthyBoundedWalReports.reopenWithState
  exact reopenMarkedBoundedWithSizedCheckpoint_eq_of_checkpoint _ _ _ _ _ _ _ _ _ _ _ _
    (raw.readSizedCheckpoint_eq sizes selected)

abbrev HealthyBoundedWalReports.reopenSizedCheckpoint {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail) :=
  raw.reopenSizedCheckpointWithState (state := FileImage)

theorem HealthyBoundedWalReports.reopenSizedCheckpoint_eq {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports pair.manifest durable)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    raw.reopenSizedCheckpoint sizes removeFile write sync renameFile =
      raw.reopen removeFile write sync renameFile :=
  raw.reopenSizedCheckpointWithState_eq sizes selected removeFile write sync renameFile

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact ready session proved by an append or checkpoint retry
is also returned by the sized checkpoint route under the same effects. -/
theorem AppendCutReady.withSizedCheckpoint
    {directory descriptor nextRef liveRefs history published target generation owners wal tail}
    {before : LockedFileState FileImage}
    (raw : HealthyBoundedWalReports directory owners descriptor wal target.pair target.range.watermark
      published.durable tail)
    (sizes : SizedCheckpointRunReports directory raw.reports target.pair.manifest published.durable)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (ready : AppendCutReady directory descriptor liveRefs history published before.image target generation
      (runOpenWithInstallation directory descriptor nextRef acquired unlock
        (raw.reopen removeFile write sync renameFile) before)) :
    AppendCutReady directory descriptor liveRefs history published before.image target generation
      (runOpenWithInstallation directory descriptor nextRef acquired unlock
        (raw.reopenSizedCheckpoint sizes removeFile write sync renameFile) before) := by
  obtain ⟨_, _, _, _, _, _, selected, _⟩ := ready.2.2.2.2
  rw [raw.reopenSizedCheckpoint_eq sizes selected]
  exact ready

end Alvoki.Storage.DiskSession
