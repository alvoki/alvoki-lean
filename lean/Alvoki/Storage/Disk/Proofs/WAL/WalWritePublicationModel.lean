import Alvoki.Storage.Disk.Proofs.WAL.MarkedWalReopenModel

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

/-- The writer's byte count after one append produces the exact marker used
by the model for the extended history. A ready writer supplies the old count. -/
theorem markerFor_append_frame {before : List WAL.Write} {walBytes : Nat}
    (event : WAL.Write) (count : walBytes = (WAL.encode before).size) :
    encode (walBytes + WAL.frameSize).toUInt64 = markerFor (before ++ [event]) := by
  simp [markerFor, count, WAL.encode_size, List.length_append, Nat.mul_add]

/-- Both live names have one durable outcome. The write protocol owns the
marker scratch name even when a previous attempt left contents there. -/
def ReopenImage.SettledFor (image : ReopenImage) (manifest : Option ByteArray)
    (history : List WAL.Write) : Prop :=
  image.directory.active = ⟨manifest, some (encode (WAL.encode history).size.toUInt64)⟩ ∧
    image.directory.crashImages = [image.directory.active] ∧
    image.wal.active = some (WAL.encode history) ∧ image.wal.crashImages = [image.wal.active]

private def WriteFiles.start (marker : Publication.Image) : WriteFiles :=
  ⟨ByteArray.empty, [ByteArray.empty], marker, by simp⟩

private def WriteFiles.withPrefix (files : WriteFiles) (oldContents : Option ByteArray)
    (manifest : Option ByteArray) (stagedManifest stagedWal : Option (ByteArray × Bool)) :
    ReopenImage :=
  let pair := fun boundary => DirectoryPublication.Bindings.mk manifest boundary
  let contents := fun tail => oldContents.map (· ++ tail)
  ⟨⟨pair files.marker.active, files.marker.crashImages.map pair,
      fun entry => if entry = .walBoundary then files.marker.staged else stagedManifest⟩,
    ⟨contents files.visibleTail, files.crashTails.map contents, stagedWal⟩⟩

def WriteFiles.reopenImage (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) (stagedManifest stagedWal : Option (ByteArray × Bool) := none) :
    ReopenImage :=
  files.withPrefix (some (WAL.encode before)) manifest stagedManifest stagedWal

theorem WriteFiles.reopenImage_crashWal_nonempty (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) (stagedManifest stagedWal : Option (ByteArray × Bool) := none) :
    (files.reopenImage before manifest stagedManifest stagedWal).wal.crashImages ≠ [] := by
  simpa [reopenImage, withPrefix] using files.crashPossible

theorem WriteFiles.reopenImage_manifest_eq (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) {stagedManifest stagedWal : Option (ByteArray × Bool)}
    {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ (files.reopenImage before manifest stagedManifest stagedWal).directory.active ::
      (files.reopenImage before manifest stagedManifest stagedWal).directory.crashImages) :
    pair.manifest = manifest := by
  rcases List.mem_cons.mp chosen with rfl | survives
  · rfl
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp survives
    rfl

def WriteEffects.appendFrame (effects : WriteEffects) (event : WAL.Write) : EStateM Unit WriteFiles Unit :=
  fun files =>
    let candidates := ByteArray.empty :: effects.appendCrashTails
    match effects.append with
    | .ok () => .ok ()
      { files with visibleTail := WAL.encodeFrame event, crashTails := candidates, crashPossible := by simp [candidates] }
    | .error visible => .error ()
      { files with visibleTail := visible, crashTails := candidates, crashPossible := by simp [candidates] }

/-- Interpret one marker step on the reached write image. -/
def WriteFiles.stepMarker (files : WriteFiles) (bytes : ByteArray) (step : Publication.Step) :
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

/-- Record the authorized survival choices of the observed keeper sync. -/
def WriteFiles.syncWal (files : WriteFiles) : WalSyncEffect → WriteFiles
  | .complete => { files with crashTails := [files.visibleTail], crashPossible := by simp }
  | .incomplete tails => { files with crashTails := ByteArray.empty :: tails, crashPossible := by simp }

def WriteEffects.markerStep (effects : WriteEffects) (bytes : ByteArray) :
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

/-- The successful grouped barrier commits both effects when the staged
marker is present. -/
theorem WriteEffects.markerStep_syncStaged_success (effects : WriteEffects) (bytes : ByteArray)
    {before : WriteFiles} (staged : before.marker.staged = some (bytes, false))
    (reported : effects.sync = .ok ()) :
    let afterWal := before.syncWal .complete
    effects.markerStep bytes .syncStaged before = .ok () ((afterWal.stepMarker bytes .syncStaged).getD afterWal) := by
  simp [markerStep, reported, WAL.Boundary.stepMarker, WriteFiles.stepMarker, WriteFiles.syncWal,
    Publication.Image.step, staged]

/-- A completed append and marker stage supply exactly the prior crash
choices and unsynced marker bytes for the next grouped barrier. -/
theorem WriteEffects.reachedWriteGroup (effects : WriteEffects) (event : WAL.Write) (bytes : ByteArray)
    {before appended staged : WriteFiles} (append : effects.appendFrame event before = .ok () appended)
    (stage : effects.markerStep bytes .writeStaged appended = .ok () staged) :
    staged.crashTails = ByteArray.empty :: effects.appendCrashTails ∧ staged.marker.staged = some (bytes, false) := by
  cases appendResult : effects.append with
  | error => simp [appendFrame, appendResult] at append
  | ok result =>
    cases result
    simp [appendFrame, appendResult] at append
    subst appended
    cases stageResult : effects.stage with
    | error => simp [markerStep, stageResult] at stage
    | ok result =>
      cases result
      simp [markerStep, stageResult, WAL.Boundary.stepMarker, WriteFiles.stepMarker, Publication.Image.step] at stage
      subst staged
      exact ⟨rfl, rfl⟩

/-- The settled marker and empty appended tail at the start of one write. -/
def WriteFiles.initial (before : List WAL.Write) (stagedMarker : Option (ByteArray × Bool)) : WriteFiles :=
  WriteFiles.start { Publication.Image.settled (some (markerFor before)) with staged := stagedMarker }

private def runWriteSchedule (before : List WAL.Write) (event : WAL.Write) (effects : WriteEffects)
    (initial : WriteFiles) : EStateM.Result Unit WriteFiles Unit :=
  commit (effects.appendFrame event)
    (Publication.run (effects.markerStep (markerFor (before ++ [event])))) initial

/-- Run the writable adapter's append/marker schedules from a settled WAL,
retaining state even when an operation reports an error. -/
def runWriteEffects (before : List WAL.Write) (event : WAL.Write) (effects : WriteEffects)
    (stagedMarker : Option (ByteArray × Bool) := none) : EStateM.Result Unit WriteFiles Unit :=
  runWriteSchedule before event effects (WriteFiles.initial before stagedMarker)

theorem runWriteEffects_eq_commit (before : List WAL.Write) (event : WAL.Write) (effects : WriteEffects)
    (stagedMarker : Option (ByteArray × Bool)) :
    runWriteEffects before event effects stagedMarker =
      commit (effects.appendFrame event)
        (Publication.run (effects.markerStep (encode (WAL.encode (before ++ [event])).size.toUInt64)))
        (WriteFiles.initial before stagedMarker) := rfl

def writeFilesAfter : EStateM.Result Unit WriteFiles Unit → WriteFiles
  | .ok () files | .error () files => files

/-- Apply the same schedule to a physical image with an already durable WAL
prefix. `SettledFor` identifies that prefix. The marker is taken from the
input image, and the other staging files carry through unchanged. -/
def runWriteEffectsFrom (before : List WAL.Write) (event : WAL.Write) (effects : WriteEffects)
    (initial : ReopenImage) : EStateM.Result Unit ReopenImage Unit :=
  let toImage := fun files : WriteFiles => files.withPrefix initial.wal.active
    initial.directory.active.manifest (initial.directory.staged .manifest) initial.wal.staged
  match runWriteSchedule before event effects (WriteFiles.start (initial.directory.project .walBoundary)) with
  | .ok () files => .ok () (toImage files)
  | .error () files => .error () (toImage files)

private theorem ReopenImage.SettledFor.marker_image {initial : ReopenImage}
    {manifest : Option ByteArray} {before : List WAL.Write}
    (settled : initial.SettledFor manifest before) :
    initial.directory.project .walBoundary =
      { Publication.Image.settled (some (markerFor before)) with
        staged := initial.directory.staged .walBoundary } := by
  rcases settled with ⟨visible, surviving, _, _⟩
  simp [DirectoryPublication.Image.project, surviving, visible, DirectoryPublication.Bindings.get,
    Publication.Image.settled, markerFor]

theorem runWriteEffectsFrom_eq {initial : ReopenImage} {manifest : Option ByteArray}
    {before : List WAL.Write} (settled : initial.SettledFor manifest before)
    (event : WAL.Write) (effects : WriteEffects) :
    let toImage := fun files : WriteFiles => files.reopenImage before manifest
      (initial.directory.staged .manifest) initial.wal.staged
    runWriteEffectsFrom before event effects initial =
      match runWriteEffects before event effects (initial.directory.staged .walBoundary) with
      | .ok () files => .ok () (toImage files)
      | .error () files => .error () (toImage files) := by
  simp [runWriteEffectsFrom, runWriteEffects, WriteFiles.initial, WriteFiles.reopenImage, settled.marker_image,
    settled.1, settled.2.2.1]

/-- Recover the modeled write-cut image after a reported error from a
settled writer. The marker, WAL and other staging names come from that image. -/
theorem runWriteEffectsFrom_failed_image {initial cut : ReopenImage}
    {manifest : Option ByteArray} {before : List WAL.Write}
    (settled : initial.SettledFor manifest before) {event : WAL.Write} {effects : WriteEffects}
    (failed : runWriteEffectsFrom before event effects initial = .error () cut) :
    (writeFilesAfter (runWriteEffects before event effects (initial.directory.staged .walBoundary))).reopenImage
      before manifest (initial.directory.staged .manifest) initial.wal.staged = cut := by
  rw [runWriteEffectsFrom_eq settled] at failed
  dsimp only at failed
  cases result : runWriteEffects before event effects (initial.directory.staged .walBoundary) with
  | ok value files => cases value; rw [result] at failed; contradiction
  | error error files =>
    cases error
    rw [result] at failed
    exact (EStateM.Result.error.inj failed).2

/-- Each physical WAL outcome has its own write-cut witness. The witness
agrees on the visible marker and covers every marker of a surviving pair. -/
def WriteFiles.HasWriteCuts (files : WriteFiles) (before : List WAL.Write)
    (event : WAL.Write) (manifest : Option ByteArray)
    (stagedManifest stagedWal : Option (ByteArray × Bool) := none) : Prop :=
  let image := files.reopenImage before manifest stagedManifest stagedWal
  ∀ candidate ∈ image.wal.active :: image.wal.crashImages,
    ∃ contents markerImage, candidate = some contents ∧ WriteCut before event contents markerImage ∧
      markerImage.active = image.directory.active.walBoundary ∧
      ∀ pair ∈ image.directory.crashImages, pair.walBoundary ∈ markerImage.crashImages

theorem WriteFiles.candidate_from_tail (files : WriteFiles) (before : List WAL.Write)
    (manifest : Option ByteArray) {stagedManifest stagedWal : Option (ByteArray × Bool)}
    {candidate : Option ByteArray}
    (chosen : candidate ∈ (files.reopenImage before manifest stagedManifest stagedWal).wal.active ::
      (files.reopenImage before manifest stagedManifest stagedWal).wal.crashImages) :
    ∃ tail ∈ files.visibleTail :: files.crashTails, candidate = some (WAL.encode before ++ tail) := by
  rcases List.mem_cons.mp chosen with h | h
  · exact ⟨files.visibleTail, List.mem_cons_self .., h⟩
  · obtain ⟨tail, present, bytes⟩ := List.mem_map.mp h
    exact ⟨tail, List.mem_cons_of_mem _ present, bytes.symm⟩

private theorem WriteFiles.appendingCuts {files : WriteFiles} {before : List WAL.Write}
    (event : WAL.Write) (manifest : Option ByteArray) {stagedManifest stagedWal : Option (ByteArray × Bool)}
    (visible : files.marker.active = some (markerFor before))
    (surviving : ∀ marker ∈ files.marker.crashImages, marker = some (markerFor before)) :
    files.HasWriteCuts before event manifest stagedManifest stagedWal := by
  intro candidate chosen
  obtain ⟨tail, _, contents⟩ := files.candidate_from_tail before manifest chosen
  refine ⟨WAL.encode before ++ tail, .settled (some (markerFor before)), contents,
    WriteCut.appending tail, visible.symm, ?_⟩
  intro pair survives
  obtain ⟨binding, canSurvive, rfl⟩ := List.mem_map.mp survives
  exact List.mem_singleton.mpr (surviving binding canSurvive)

private theorem WriteFiles.publishingCuts {files : WriteFiles} {before : List WAL.Write}
    (event : WAL.Write) (manifest : Option ByteArray) {stagedManifest stagedWal : Option (ByteArray × Bool)}
    (visible : files.visibleTail = WAL.encodeFrame event)
    (surviving : ∀ tail ∈ files.crashTails, tail = WAL.encodeFrame event)
    (cut : Nat) (ran : (Publication.Image.settled (some (markerFor before))).execute
      (markerFor (before ++ [event])) (Publication.steps.take cut) = some files.marker) :
    files.HasWriteCuts before event manifest stagedManifest stagedWal := by
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
    (effects : WriteEffects) (manifest : Option ByteArray)
    (stagedMarker stagedManifest stagedWal : Option (ByteArray × Bool) := none) :
    (writeFilesAfter (runWriteEffects before event effects stagedMarker)).HasWriteCuts before event manifest
      stagedManifest stagedWal := by
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
    {effects : WriteEffects} {files : WriteFiles} {stagedMarker : Option (ByteArray × Bool)}
    (ran : runWriteEffects before event effects stagedMarker = .ok () files) :
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

/-- A successful write leaves the new marker in every selectable metadata pair. -/
theorem runWriteEffects_success_pair_marker {before : List WAL.Write} {event : WAL.Write}
    {effects : WriteEffects} {files : WriteFiles} {stagedMarker stagedManifest stagedWal : Option (ByteArray × Bool)}
    (ran : runWriteEffects before event effects stagedMarker = .ok () files) (manifest : Option ByteArray)
    {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ (files.reopenImage before manifest stagedManifest stagedWal).directory.active ::
      (files.reopenImage before manifest stagedManifest stagedWal).directory.crashImages) :
    pair.walBoundary = some (encode (WAL.encode (before ++ [event])).size.toUInt64) := by
  have settled := (runWriteEffects_success ran).2.2
  have selected : pair = ⟨manifest, some (encode (WAL.encode (before ++ [event])).size.toUInt64)⟩ := by
    simpa [WriteFiles.reopenImage, WriteFiles.withPrefix, settled, Publication.Image.settled] using chosen
  rw [selected]

/-- A successful write leaves the extended history selected and wholly durable. -/
theorem runWriteEffectsFrom_success {initial after : ReopenImage} {manifest : Option ByteArray}
    {before : List WAL.Write} {event : WAL.Write} {effects : WriteEffects}
    (settled : initial.SettledFor manifest before)
    (ran : runWriteEffectsFrom before event effects initial = .ok () after) :
    after.SettledFor manifest (before ++ [event]) := by
  rw [runWriteEffectsFrom_eq settled] at ran
  split at ran
  · rename_i files written
    cases ran
    obtain ⟨visible, surviving, marker⟩ := runWriteEffects_success written
    have appended : WAL.encode before ++ WAL.encodeFrame event = WAL.encode (before ++ [event]) := by
      rw [WAL.encode_append]
      simp [WAL.encode]
    simp [ReopenImage.SettledFor, WriteFiles.reopenImage, WriteFiles.withPrefix, visible, surviving, marker,
      Publication.Image.settled, appended]
  · contradiction

end Alvoki.WAL.Boundary
