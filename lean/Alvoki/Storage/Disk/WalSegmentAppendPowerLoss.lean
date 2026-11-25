import Alvoki.Storage.Disk.AppendRetrySession
import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.RetainedWriterReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- Bytes appended beyond a settled marker cannot change its selected
keeper prefix, even if the append reaches disk before power loss. -/
theorem SegmentedWriterState.RetainedReady.selectPriorKeeper {directory descriptor} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) (tail : ByteArray) :
    before.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
    selectRetained before.installed.activeFirst (WAL.encode before.history).size.toUInt64
      (WAL.encode (before.history.drop before.wal.active.first) ++ tail) = .ok before.wal.active.bytes := by
  have marker := congrArg Publication.Image.active ready.resumed.markerImage
  change before.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64)
    at marker
  rw [ready.resumed.ready.selected] at marker
  have keeperBytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have accepts : before.target.Accepts
      (some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) := by
    refine ⟨tail, ?_⟩
    rw [ready.resumed.contents, ready.active]
  have selected := before.target.selectKeeper marker (WAL.Boundary.decode_encode _) accepts
  rw [← ready.resumed.keeper, keeperBytes] at selected
  exact ⟨marker, selected⟩

/-- A physical observation while the first append callback is still in
flight. The preceding keeper prefix is durable. The callback has yet to
return, so no marker operation has been reached. -/
structure FirstAppendCut where
  visibleTail : ByteArray
  crashTails : List ByteArray

namespace FirstAppendCut

/-- The existing write-effect interpreter can represent this file image.
The error tag stops its modeled schedule and supplies no native report. -/
def writeEffects (cut : FirstAppendCut) : WriteEffects :=
  ⟨.error cut.visibleTail, cut.crashTails, .ok (), .ok (), .success, .success⟩

def writeFiles (cut : FirstAppendCut) (history : List WAL.Write) (scratch : Option (ByteArray × Bool)) :
    WriteFiles :=
  ⟨cut.visibleTail, ByteArray.empty :: cut.crashTails, (WriteFiles.initial history scratch).marker,
    by simp⟩

theorem modeledFiles (cut : FirstAppendCut) (history : List WAL.Write) (event : WAL.Write)
    (scratch : Option (ByteArray × Bool)) :
    writeFilesAfter (runWriteEffects history event cut.writeEffects scratch) = cut.writeFiles history scratch := rfl

/-- Project the reached append bytes onto the existing keeper. Metadata,
sealed files, later names and unrelated staging come from the prior image. -/
def projectReached (before : SegmentedWriterState) (written : WriteFiles) : FileImage :=
  let segment := written.reopenSegment before.wal.active.first before.history before.files.directory.active.manifest
  { before.files with keeper := { segment.wal with staged := before.files.keeper.staged } }

def physical (cut : FirstAppendCut) (before : SegmentedWriterState) : FileImage :=
  projectReached before (cut.writeFiles before.history (before.files.directory.staged .walBoundary))

def crashed (cut : FirstAppendCut) (before : SegmentedWriterState) (directory : DiskDirectory) (tail : ByteArray) :
    LockedFileState FileImage :=
  let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ tail
  ⟨(cut.physical before).crash before.target.pair (some bytes) [],
    before.owners.set (directory.file .lock) none⟩

private theorem keeperSurvivors (cut : FirstAppendCut) (before : SegmentedWriterState) :
    (cut.physical before).keeper.crashImages = (ByteArray.empty :: cut.crashTails).map
      (fun tail => some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) := rfl

/-- Every keeper outcome reported during the append preserves the
previously durable prefix. -/
theorem survivorKeepsPrefix (cut : FirstAppendCut) {before : SegmentedWriterState}
    (layout : before.wal.ReadLayout before.history) {bytes : Option ByteArray}
    (survives : bytes ∈ (cut.physical before).keeper.crashImages) :
    ∃ tail, bytes = some (before.wal.active.bytes ++ tail) := by
  rw [cut.keeperSurvivors] at survives
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp survives
  exact ⟨tail, by rw [layout.activeBytes]⟩

/-- Power loss during the append starts a retry at the old marker and
the observed surviving keeper bytes. -/
theorem powersOff (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor) (admits : Target → Prop)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails) :
    BoundedReopenTrace directory admits ⟨cut.physical before, before.owners⟩ (cut.crashed before directory tail) := by
  apply BoundedReopenTrace.powerLoss BoundedReopenTrace.empty
  · change before.target.pair ∈ before.files.directory.crashImages
    rw [ready.resumed.ready.settled]
    exact List.mem_singleton_self _
  · change some (WAL.encode (before.history.drop before.wal.active.first) ++ tail) ∈ (cut.physical before).keeper.crashImages
    rw [cut.keeperSurvivors]
    exact List.mem_map_of_mem survives
  · change [] ∈ before.files.later.crashImages
    rw [ready.resumed.ready.pruned.2]
    exact List.mem_singleton_self _

/-- Power loss chooses a surviving tail and ends the held writer lock
while the append is still in flight. It starts the same bounded retry
trace used after other cuts, without a returned write outcome. -/
theorem startsRetry (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.Ready directory descriptor) (event : WAL.Write)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails) :
    let files := cut.physical before
    let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ tail
    BoundedReopenTrace directory (AppendRetryTarget before.history event before.wal.active.first)
      ⟨files, before.owners⟩
      ⟨files.crash before.target.pair (some bytes) [], before.owners.set (directory.file .lock) none⟩ :=
  cut.powersOff ready.toRetained _ survives

/-- Each crash choice during the first append retains the old absolute
marker. Even a full surviving frame lies outside it. The selected keeper
and immutable sealed segments decode to the exact prior history. -/
theorem selectsPriorHistory (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.Ready directory descriptor)
    {pair : DirectoryPublication.Bindings} (metadata : pair ∈ (cut.physical before).directory.crashImages)
    {keeper : Option ByteArray} (payload : keeper ∈ (cut.physical before).keeper.crashImages)
    {later : List Nat} (names : later ∈ (cut.physical before).later.crashImages) :
    let crashed := (cut.physical before).crash pair keeper later
    crashed.directory = .settled before.target.pair ∧ crashed.kept = before.files.kept ∧
    crashed.later.DurablyEmpty ∧
    crashed.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
    ∃ bytes, crashed.keeper.active = some bytes ∧ crashed.keeper.crashImages = [some bytes] ∧
      (crashed.directory.active.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained before.installed.activeFirst count bytes) = .ok (some before.wal.active.bytes) ∧
      WAL.decodeOrdinals (WalSegment.concatenate before.wal.segments) = .ok before.history := by
  intro crashed
  change pair ∈ before.files.directory.crashImages at metadata
  rw [ready.resumed.ready.settled] at metadata
  have selectedPair := List.mem_singleton.mp metadata
  subst pair
  change later ∈ before.files.later.crashImages at names
  rw [ready.resumed.ready.pruned.2] at names
  have empty := List.mem_singleton.mp names
  subst later
  rw [cut.keeperSurvivors] at payload
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp payload
  obtain ⟨exactMarker, selected⟩ := ready.toRetained.selectPriorKeeper tail
  refine ⟨rfl, rfl, ⟨rfl, rfl⟩, exactMarker, _, rfl, rfl, ?_, ?_⟩
  · change ((before.target.pair.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained before.installed.activeFirst count
          (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) : Except String (Option ByteArray)) = _
    rw [exactMarker, Option.mapM, WAL.Boundary.decode_encode]
    change (some <$> selectRetained before.installed.activeFirst (WAL.encode before.history).size.toUInt64
      (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) = _
    rw [selected]
    rfl
  · rw [ready.chain.concatenate_eq, List.drop_zero]
    exact WAL.decodeOrdinals_encode _ ready.resumed.ordered

private theorem layoutWithTail {directory descriptor} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) (files : FileImage) (tail : ByteArray)
    (observed : before.wal.CheckpointReopenDirectory files.directory)
    (pair : files.directory.active = before.target.pair)
    (visible : files.keeper.active = some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) :
    ∃ selected : CanonicalKeeperLayout files before.history,
      selected.target = before.target ∧ selected.keeper = before.wal.active ∧
      selected.tail = tail ∧
      selected.sealed ++ [selected.keeper] = before.wal.readDescriptors selected.range.watermark ∧
      selectWalSegmentReads (before.wal.segments.map WalSegment.first) selected.range.watermark =
        some (selected.first, (before.wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
  have decoded : files.directory.active.walRange = some before.target.range := pair ▸ before.target.decoded
  obtain ⟨base, range, keeper, _, descriptors, offsets, _, _, _, _⟩ :=
    ready.layout.checkpointReopenLayout ready.valid observed decoded ready.resumed.through none
  let source : CanonicalKeeperLayout files before.history :=
    { range := base.range
      decoded := base.decoded
      through := base.through
      first := base.first
      sealed := base.sealed
      keeper := base.keeper
      chain := base.chain
      covers := base.covers
      tail := tail
      visible := by rw [keeper, ready.layout.activeBytes]; exact visible }
  have start : source.target.first = before.target.first :=
    (congrArg WalSegment.first keeper).trans ready.active.symm
  have bytes : source.target.trimmed = before.target.trimmed := by
    change base.keeper.bytes = before.target.trimmed
    rw [keeper, ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have target : source.target = before.target := by
    change source.target.pair = before.target.pair at pair
    have exactRange : source.target.range = before.target.range := range
    generalize source.target = a at pair start bytes exactRange ⊢
    generalize before.target = b at pair start bytes exactRange ⊢
    cases a
    cases b
    cases pair
    cases exactRange
    cases start
    cases bytes
    rfl
  exact ⟨source, target, keeper, rfl, range.symm ▸ descriptors, range.symm ▸ offsets⟩

/-- The selected layout after a machine crash during the first append. -/
theorem crashedLayout (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor) (tail : ByteArray) :
    let files := (cut.crashed before directory tail).image
    ∃ selected : CanonicalKeeperLayout files before.history,
      selected.target = before.target ∧ selected.keeper = before.wal.active ∧
      selected.sealed ++ [selected.keeper] = before.wal.readDescriptors selected.range.watermark ∧
      selectWalSegmentReads (before.wal.segments.map WalSegment.first) selected.range.watermark =
        some (selected.first, (before.wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
      Prepared files selected.target selected.plan := by
  intro files
  have pairSurvives : before.target.pair ∈ before.wal.directory.crashImages := by
    rw [← ready.directoryFiles, ready.resumed.ready.settled]
    exact List.mem_singleton_self _
  obtain ⟨source, target, keeper, _, descriptors, offsets⟩ :=
    layoutWithTail ready files tail (.crash pairSurvives) rfl rfl
  have prepared := source.prepared (by simp [files, crashed, FileImage.crash, Publication.Image.settled])
    (fun _ present => ⟨tail, by rw [List.mem_singleton.mp present, keeper, ready.layout.activeBytes]⟩)
    (by simp [files, crashed, FileImage.crash, LaterNames.settled, LaterNames.Beyond])
  exact ⟨source, target, keeper, descriptors, offsets, prepared⟩

/-- An observation of the live append cut selects the prior keeper. Its
unsynced tail and every crash candidate remain in the file image. -/
theorem liveLayout (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor) :
    let files := cut.physical before
    files.syncDirectory = files ∧ files.later.visible = [] ∧
    ∃ selected : CanonicalKeeperLayout files before.history,
      selected.target = before.target ∧ selected.keeper = before.wal.active ∧
      selected.tail = cut.visibleTail ∧
      selected.sealed ++ [selected.keeper] = before.wal.readDescriptors selected.range.watermark ∧
      selectWalSegmentReads (before.wal.segments.map WalSegment.first) selected.range.watermark =
        some (selected.first, (before.wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
      Prepared files selected.target selected.plan := by
  intro files
  have observed : before.wal.CheckpointReopenDirectory files.directory := by
    change before.wal.CheckpointReopenDirectory before.files.directory
    rw [ready.directoryFiles]
    exact .visible
  obtain ⟨source, target, keeper, tail, descriptors, offsets⟩ :=
    layoutWithTail ready files cut.visibleTail observed ready.resumed.ready.selected rfl
  have compatible : ∀ bytes ∈ files.keeper.crashImages, ∃ suffix, bytes = some (source.keeper.bytes ++ suffix) := by
    intro bytes present
    rw [cut.keeperSurvivors] at present
    obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp present
    exact ⟨suffix, by rw [keeper, ready.layout.activeBytes]⟩
  have choices : files.keeper.crashImages ≠ [] := by rw [cut.keeperSurvivors]; simp
  have empty := ready.resumed.ready.pruned.1
  have durable := ready.resumed.ready.pruned.2
  have later : files.later.Beyond source.range.through := by
    change before.files.later.Beyond source.range.through
    intro names presented first listed
    rw [empty, durable] at presented
    have absent : names = [] := by simpa using presented
    rw [absent] at listed
    exact (List.not_mem_nil listed).elim
  have fixed : files.syncDirectory = files := by
    have metadata : files.directory.syncDirectory = files.directory := by
      have settled : [files.directory.active] = files.directory.crashImages := by
        change [before.files.directory.active] = before.files.directory.crashImages
        rw [ready.resumed.ready.selected, ready.resumed.ready.settled]
      unfold DirectoryPublication.Image.syncDirectory
      rw [settled]
    have names : files.later.syncDirectory = files.later := by
      have settled : [files.later.visible] = files.later.crashImages := by
        change [before.files.later.visible] = before.files.later.crashImages
        rw [empty, durable]
      unfold LaterNames.syncDirectory LaterNames.settled
      rw [settled]
    rw [FileImage.syncDirectory, metadata, names]
  exact ⟨fixed, empty, source, target, keeper, tail, descriptors, offsets, source.prepared choices compatible later⟩

private theorem reopensPriorMarker (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails)
    {retry : LockedFileState FileImage}
    (failures : BoundedReopenTrace directory (fun target => target = before.target)
      (cut.crashed before directory tail) retry)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨cut.physical before, before.owners⟩ (cut.crashed before directory tail) ∧
    retry.image.kept = before.files.kept ∧
    ∃ selected : CanonicalKeeperLayout retry.image before.history,
      selected.target = before.target ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
          nextDescriptor before.wal retry.image.directory.active selected.range.watermark
          before.published.durable selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
        (∀ action prior next,
          ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
          prior.effect selected.target action = some next →
          performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
        AppendCutReady directory nextDescriptor liveRefs before.history before.published retry.image selected.target
          before.installed.generation
          (runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
            (raw.reopen removeFile write sync renameFile) retry) := by
  refine ⟨cut.powersOff ready _ survives, ?_⟩
  obtain ⟨source, target, keeper, descriptors, offsets, prepared⟩ := cut.crashedLayout ready tail
  have attempts : BoundedReopenTrace directory (fun target => target = source.target)
      (cut.crashed before directory tail) retry := target.symm ▸ failures
  obtain ⟨kept, selected, selectedTarget, install⟩ := attempts.installsAfterFixedAuthority
    ready.layout ready.resumed.ordered source keeper descriptors offsets prepared rfl rfl
    ready.resumed.accepted ready.resumed.generationRead liveRefs fresh acquisition unlock removeFile write sync renameFile
  have selectedTarget := selectedTarget.trans target
  exact ⟨kept, selected, selectedTarget, install⟩

/-- From a power loss inside the append callback, any finite prefix of
failed bounded opens keeps the prior marker authoritative. A healthy
bounded open installs the prior history and exact checkpoint under the
new owner, trimming any surviving unselected tail. -/
theorem reopens (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.Ready directory descriptor)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails)
    {retry : LockedFileState FileImage}
    (failures : BoundedReopenTrace directory (fun target => target = before.target)
      (cut.crashed before directory tail) retry)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨cut.physical before, before.owners⟩ (cut.crashed before directory tail) ∧
    ∃ selected : CanonicalKeeperLayout retry.image before.history,
      selected.target = before.target ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
          nextDescriptor before.wal retry.image.directory.active selected.range.watermark
          before.published.durable selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
        (∀ action prior next,
          ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
          prior.effect selected.target action = some next →
          performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
        let attempt : BoundedReopenAttempt :=
          ⟨nextDescriptor, nextRef, .ok true, unlock, raw.reports.readOptional, raw.list,
            (fun path => .ok (raw.reports.lstat path)), raw.reports.readBin, raw.readPrefix,
            removeFile, write, sync, renameFile⟩
        ∃ session final, ∃ writer : SegmentedWriterState,
          attempt.run directory retry = .ok session final ∧ session.directory = directory ∧
          session.descriptor = nextDescriptor ∧ session.phase = .ready writer.installed ∧
          writer.files = final.image ∧ writer.owners = final.owners ∧
          writer.wal = { before.wal with directory := final.image.directory } ∧
          writer.target = before.target ∧ writer.history = before.history ∧
          writer.published.durable = before.published.durable ∧ writer.checkpoint = before.checkpoint ∧
          writer.installed.generation = before.installed.generation ∧ writer.Ready directory nextDescriptor := by
  obtain ⟨powerLoss, kept, selected, selectedTarget, install⟩ := cut.reopensPriorMarker ready.toRetained survives failures
    (nextDescriptor := nextDescriptor) liveRefs fresh acquisition unlock removeFile write sync renameFile
  refine ⟨powerLoss, selected, selectedTarget, ?_⟩
  intro raw settles healthy attempt
  have installed := install raw settles healthy
  have first := (congrArg Target.first selectedTarget).trans ready.active
  obtain ⟨session, final, writer, ran, path, lock, phase, files, owners, wal, writerTarget, history, durable, nextReady⟩ :=
    installed.writerReady ready.layout ready.chain first (kept.trans ready.sealedFiles)
  have exactTarget := writerTarget.trans selectedTarget
  have pair : retry.image.directory.active = before.target.pair := congrArg Target.pair selectedTarget
  have selectedCheckpoint := nextReady.resumed.selected
  rw [exactTarget, durable, ← pair] at selectedCheckpoint
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := by rw [pair]; exact ready.resumed.selected
  have checkpoint := Except.ok.inj
    ((raw.readCheckpoint selectedCheckpoint).symm.trans (raw.readCheckpoint oldCheckpoint))
  have generation : writer.installed.generation = before.installed.generation := by
    rw [nextReady.resumed.generation, checkpoint, ← ready.resumed.generation]
  exact ⟨session, final, writer, ran, path, lock, phase, files, owners, wal, exactTarget, history, durable,
    checkpoint, generation, nextReady⟩

/-- The fixed prior marker still determines the keeper after covered WAL
deletion. A healthy bounded open installs the same history and checkpoint
from the selected retained suffix after any admitted retry prefix. -/
theorem reopensRetained (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails)
    {retry : LockedFileState FileImage}
    (failures : BoundedReopenTrace directory (fun target => target = before.target)
      (cut.crashed before directory tail) retry)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨cut.physical before, before.owners⟩ (cut.crashed before directory tail) ∧
    ∃ selected : CanonicalKeeperLayout retry.image before.history,
      selected.target = before.target ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
          nextDescriptor before.wal retry.image.directory.active selected.range.watermark
          before.published.durable selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
        (∀ action prior next,
          ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
          prior.effect selected.target action = some next →
          performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
        let attempt : BoundedReopenAttempt :=
          ⟨nextDescriptor, nextRef, .ok true, unlock, raw.reports.readOptional, raw.list,
            (fun path => .ok (raw.reports.lstat path)), raw.reports.readBin, raw.readPrefix,
            removeFile, write, sync, renameFile⟩
        ∃ session final, ∃ writer : SegmentedWriterState,
          attempt.run directory retry = .ok session final ∧ session.directory = directory ∧
          session.descriptor = nextDescriptor ∧ session.phase = .ready writer.installed ∧
          writer.files = final.image ∧ writer.owners = final.owners ∧
          writer.wal = { before.wal with directory := final.image.directory } ∧
          writer.target = before.target ∧ writer.history = before.history ∧
          writer.published.durable = before.published.durable ∧ writer.checkpoint = before.checkpoint ∧
          writer.installed.generation = before.installed.generation ∧ writer.RetainedReady directory nextDescriptor := by
  obtain ⟨powerLoss, kept, selected, selectedTarget, install⟩ := cut.reopensPriorMarker ready survives failures
    (nextDescriptor := nextDescriptor) liveRefs fresh acquisition unlock removeFile write sync renameFile
  refine ⟨powerLoss, selected, selectedTarget, ?_⟩
  intro raw settles healthy attempt
  have installed := install raw settles healthy
  have first := (congrArg Target.first selectedTarget).trans ready.active
  have pair : retry.image.directory.active = before.target.pair := congrArg Target.pair selectedTarget
  have active : before.wal.directory.active = selected.target.pair := ready.walPair.trans pair.symm
  obtain ⟨session, final, writer, ran, path, lock, phase, files, owners, wal, writerTarget, history, generation, durable, nextReady⟩ :=
    installed.writerRetained ready.layout ready.valid ready.spans active first (kept.trans ready.sealedFiles)
  have exactTarget := writerTarget.trans selectedTarget
  have selectedCheckpoint := nextReady.resumed.selected
  rw [exactTarget, durable, ← pair] at selectedCheckpoint
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := by rw [pair]; exact ready.resumed.selected
  have checkpoint := Except.ok.inj
    ((raw.readCheckpoint selectedCheckpoint).symm.trans (raw.readCheckpoint oldCheckpoint))
  exact ⟨session, final, writer, ran, path, lock, phase, files, owners, wal, exactTarget, history, durable,
    checkpoint, generation, nextReady⟩

end FirstAppendCut

end Alvoki.Storage.DiskSession
