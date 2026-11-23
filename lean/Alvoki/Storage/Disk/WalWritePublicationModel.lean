import Alvoki.Storage.Disk.MarkedWalReopenModel

namespace Alvoki.WAL.Boundary
open Storage

/-- With the old prefix already durable, an unsuccessful sync can leave any
of the supplied append tails. A completed WAL sync leaves the visible tail. -/
inductive WalSyncEffect where
  | incomplete (crashTails : List ByteArray)
  | complete

structure GroupSyncFailure where
  wal : WalSyncEffect
  stagedMarkerSynced : Bool

inductive OperationResult where
  | success
  | errorBeforeEffect
  | errorAfterEffect

/-- Effects of one marked write. Append errors supply the visible tail;
staging errors supply the bytes left at the scratch name. In either case
the next operation is skipped. A grouped-sync error records both effects
independently, since either target can have been synced before the error. -/
structure WriteEffects where
  append : Except ByteArray Unit
  appendCrashTails : List ByteArray
  stage : Except (Option ByteArray) Unit
  sync : Except GroupSyncFailure Unit
  rename : OperationResult
  directorySync : OperationResult

/-- WAL effects extend the immutable acknowledged prefix. The checkpoint is
fixed throughout this schedule; its manifest is paired with the marker when
exposing the resulting directory image. -/
structure WriteFiles where
  visibleTail : ByteArray
  crashTails : List ByteArray
  marker : Publication.Image
  crashPossible : crashTails ≠ []

private def markerFor (events : List WAL.Write) : ByteArray :=
  encode (WAL.encode events).size.toUInt64

private def WriteFiles.start (before : List WAL.Write) : WriteFiles :=
  ⟨ByteArray.empty, [ByteArray.empty], .settled (some (markerFor before)), by simp⟩

def WriteFiles.reopenImage (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) : ReopenImage :=
  let pair := fun boundary => DirectoryPublication.Bindings.mk manifest boundary
  let contents := fun tail => some (WAL.encode before ++ tail)
  ⟨⟨pair files.marker.active, files.marker.crashImages.map pair,
      fun entry => if entry = .walBoundary then files.marker.staged else none⟩,
    ⟨contents files.visibleTail, files.crashTails.map contents, none⟩⟩

theorem WriteFiles.reopenImage_crashWal_nonempty (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) : (files.reopenImage before manifest).wal.crashImages ≠ [] := by
  simpa [reopenImage] using files.crashPossible

private def appendEffect (event : WAL.Write) (effects : WriteEffects) : EStateM Unit WriteFiles Unit :=
  fun files =>
    let candidates := ByteArray.empty :: effects.appendCrashTails
    match effects.append with
    | .ok () => .ok ()
      { files with visibleTail := WAL.encodeFrame event, crashTails := candidates, crashPossible := by simp [candidates] }
    | .error visible => .error ()
      { files with visibleTail := visible, crashTails := candidates, crashPossible := by simp [candidates] }

private def WriteFiles.stepMarker (files : WriteFiles) (bytes : ByteArray) (step : Publication.Step) :
    Option WriteFiles :=
  (files.marker.step bytes step).map fun marker => { files with marker }

private def stepMarker (bytes : ByteArray) (step : Publication.Step) (report : OperationResult) :
    EStateM Unit WriteFiles Unit := fun files =>
  match report with
  | .errorBeforeEffect => .error () files
  | .success =>
    match files.stepMarker bytes step with
    | some after => .ok () after
    | none => .error () files
  | .errorAfterEffect => .error () ((files.stepMarker bytes step).getD files)

private def WriteFiles.syncWal (files : WriteFiles) : WalSyncEffect → WriteFiles
  | .complete => { files with crashTails := [files.visibleTail], crashPossible := by simp }
  | .incomplete tails => { files with crashTails := ByteArray.empty :: tails, crashPossible := by simp }

private def perform (bytes : ByteArray) (effects : WriteEffects) :
    Publication.Step → EStateM Unit WriteFiles Unit
  | .writeStaged => fun files =>
    match effects.stage with
    | .ok () => stepMarker bytes .writeStaged .success files
    | .error contents => .error ()
      { files with marker := { files.marker with staged := contents.map (·, false) } }
  | .syncStaged => fun files =>
    match effects.sync with
    | .ok () => stepMarker bytes .syncStaged .success (files.syncWal .complete)
    | .error effects =>
      let afterWal := files.syncWal effects.wal
      let after := if effects.stagedMarkerSynced then
        (afterWal.stepMarker bytes .syncStaged).getD afterWal else afterWal
      .error () after
  | .renameStaged => stepMarker bytes .renameStaged effects.rename
  | .syncDirectory => stepMarker bytes .syncDirectory effects.directorySync

/-- Run the writable adapter's append/marker schedules in an error-and-state
monad so an operation can report an error after changing persistence. -/
def runWriteEffects (before : List WAL.Write) (event : WAL.Write) (effects : WriteEffects) :
    EStateM.Result Unit WriteFiles Unit :=
  commit (appendEffect event effects)
    (Publication.run (perform (markerFor (before ++ [event])) effects)) (WriteFiles.start before)

def writeFilesAfter : EStateM.Result Unit WriteFiles Unit → WriteFiles
  | .ok () files | .error () files => files

/-- Each physical WAL outcome has its own write-cut witness. The witness
agrees on the visible marker and covers every marker of a surviving pair. -/
def WriteFiles.HasWriteCuts (files : WriteFiles) (before : List WAL.Write)
    (event : WAL.Write) (manifest : Option ByteArray) : Prop :=
  let image := files.reopenImage before manifest
  ∀ candidate ∈ image.wal.active :: image.wal.crashImages,
    ∃ contents markerImage, candidate = some contents ∧ WriteCut before event contents markerImage ∧
      markerImage.active = image.directory.active.walBoundary ∧
      ∀ pair ∈ image.directory.crashImages, pair.walBoundary ∈ markerImage.crashImages

private theorem WriteFiles.candidate_from_tail (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) {candidate : Option ByteArray}
    (chosen : candidate ∈ (files.reopenImage before manifest).wal.active ::
      (files.reopenImage before manifest).wal.crashImages) :
    ∃ tail ∈ files.visibleTail :: files.crashTails, candidate = some (WAL.encode before ++ tail) := by
  rcases List.mem_cons.mp chosen with h | h
  · exact ⟨files.visibleTail, List.mem_cons_self .., h⟩
  · obtain ⟨tail, present, bytes⟩ := List.mem_map.mp h
    exact ⟨tail, List.mem_cons_of_mem _ present, bytes.symm⟩

private theorem WriteFiles.appendingCuts {files : WriteFiles} {before : List WAL.Write}
    (event : WAL.Write) (manifest : Option ByteArray)
    (visible : files.marker.active = some (markerFor before))
    (surviving : ∀ marker ∈ files.marker.crashImages, marker = some (markerFor before)) :
    files.HasWriteCuts before event manifest := by
  intro candidate chosen
  obtain ⟨tail, _, contents⟩ := files.candidate_from_tail before manifest chosen
  refine ⟨WAL.encode before ++ tail, .settled (some (markerFor before)), contents,
    WriteCut.appending tail, visible.symm, ?_⟩
  intro pair survives
  obtain ⟨binding, canSurvive, rfl⟩ := List.mem_map.mp survives
  exact List.mem_singleton.mpr (surviving binding canSurvive)

private theorem WriteFiles.publishingCuts {files : WriteFiles} {before : List WAL.Write}
    (event : WAL.Write) (manifest : Option ByteArray)
    (visible : files.visibleTail = WAL.encodeFrame event)
    (surviving : ∀ tail ∈ files.crashTails, tail = WAL.encodeFrame event)
    (cut : Nat) (ran : (Publication.Image.settled (some (markerFor before))).execute
      (markerFor (before ++ [event])) (Publication.steps.take cut) = some files.marker) :
    files.HasWriteCuts before event manifest := by
  intro candidate chosen
  obtain ⟨tail, possible, bytes⟩ := files.candidate_from_tail before manifest chosen
  have complete : tail = WAL.encodeFrame event :=
    (List.mem_cons.mp possible).elim (·.trans visible) (surviving tail)
  have appended : WAL.encode before ++ WAL.encodeFrame event = WAL.encode (before ++ [event]) := by
    rw [WAL.encode_append]
    simp [WAL.encode]
  rw [complete, appended] at bytes
  refine ⟨WAL.encode (before ++ [event]), files.marker, bytes,
    WriteCut.publishing (.attempt (.refl _) rfl cut ran), rfl, ?_⟩
  intro pair survives
  obtain ⟨binding, present, rfl⟩ := List.mem_map.mp survives
  exact present

/-- Each effect outcome of the ordered append and marker schedule supplies a
write-cut witness for every visible or crash-surviving WAL candidate. -/
theorem runWriteEffects_hasWriteCuts (before : List WAL.Write) (event : WAL.Write)
    (effects : WriteEffects) (manifest : Option ByteArray) :
    (writeFilesAfter (runWriteEffects before event effects)).HasWriteCuts before event manifest := by
  rcases effects with ⟨append, crashTails, stage, sync, rename, directory⟩
  rcases append with tail | ⟨⟩
  · exact WriteFiles.appendingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h)
  rcases stage with scratchContents | ⟨⟩
  · exact WriteFiles.appendingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h)
  rcases sync with ⟨walEffect, stagedMarkerSynced⟩ | ⟨⟩
  · cases walEffect <;> cases stagedMarkerSynced <;>
      exact WriteFiles.appendingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h)
  cases rename with
  | errorBeforeEffect =>
    exact WriteFiles.publishingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h) 2 rfl
  | errorAfterEffect =>
    exact WriteFiles.publishingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h) 3 rfl
  | success =>
    cases directory with
    | errorBeforeEffect =>
      exact WriteFiles.publishingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h) 3 rfl
    | success | errorAfterEffect =>
      exact WriteFiles.publishingCuts event manifest rfl (fun _ h => List.mem_singleton.mp h) 4 rfl

/-- A reported success leaves the complete WAL and the newly published,
settled marker. A failed report can have reached the same physical state. -/
theorem runWriteEffects_success {before : List WAL.Write} {event : WAL.Write}
    {effects : WriteEffects} {files : WriteFiles}
    (ran : runWriteEffects before event effects = .ok () files) :
    files.visibleTail = WAL.encodeFrame event ∧ files.crashTails = [WAL.encodeFrame event] ∧
      files.marker = .settled (some (encode (WAL.encode (before ++ [event])).size.toUInt64)) := by
  rcases effects with ⟨append, crashTails, stage, sync, rename, directory⟩
  rcases append with tail | ⟨⟩
  · contradiction
  rcases stage with scratchContents | ⟨⟩
  · contradiction
  rcases sync with ⟨walEffect, stagedMarkerSynced⟩ | ⟨⟩
  · cases walEffect <;> cases stagedMarkerSynced <;> contradiction
  cases rename with
  | errorBeforeEffect | errorAfterEffect => contradiction
  | success =>
    cases directory with
    | errorBeforeEffect | errorAfterEffect => contradiction
    | success => cases ran; exact ⟨rfl, rfl, rfl⟩

end Alvoki.WAL.Boundary
