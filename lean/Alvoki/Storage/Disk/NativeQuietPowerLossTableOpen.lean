import Alvoki.Storage.Disk.NativeQuietPowerLossRaw
import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

section

variable {heap stream : Type} {state : NativeReadyState} {input : FilePath}
  {crash : NativeReadyQuietCrash state}
  {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    crash.retry.image.directory.active.manifest state.writer.checkpoint}
  {reader : NativeReadyRestartReads crash input layout selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before after : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The report that selects the reboot files is also the input to the
raw marked worker. Its existing read and release chronology indexes
each primitive report through the final allocation. -/
structure RawQuietRestartEffects (reader : NativeReadyRestartReads crash input layout selected)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (before after : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    (beforeCensus : DescriptorInventory := state.census)
    extends RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init after
      phaseIdentity tokenIdentity allocatePhase allocateToken stream where
  reboot : RawQuietRebootEntry crash view names bytes before after beforeCensus

/-- The admission and cache allocator are those of the same aligned
reader used by the raw opener. -/
def RawQuietRestartEffects.admission {beforeCensus : DescriptorInventory}
    (seen : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus) :
    RawQuietRestartAdmission reader view calls init names bytes before after beforeCensus :=
  ⟨seen.reboot, seen.raw, seen.seed⟩

/-- The source open schedule, interpreted from the observed reboot heap
with the actual admission and held worker callbacks. -/
def RawQuietRestartEffects.openTable
    {beforeCensus : DescriptorInventory}
    (seen : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  seen.toRawAlignedCheckpointReopenEffects.openTable remove write rename bootstrap assemble makeCache

/-- Project one quiet reboot reader into the aligned marked proof. This
keeps its exact admission, captured reads and repair worker. -/
def NativeReadyRestartReads.markedReport (seen : NativeReadyRestartReads crash input layout selected)
    (retained : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := crash.reboot
  retry := crash.retry
  layout := layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := selected
  vacant := crash.vacant
  opening := ⟨seen.opening.admission, seen.opening.callbacks, seen.opening.reads, .aligned seen.opening.finish,
    seen.capturedChronology, seen.opening.marker, seen.opening.markerFound⟩
  prepared := prepared
  following := seen.opening.reads.walReads.selectedAfterWatermark offsets descriptors
  accepted := retained.resumed.accepted
  ordered := retained.resumed.ordered
  wal := state.writer.wal
  walLayout := retained.layout
  walValid := retained.valid
  spans := retained.spans
  active := retained.walPair.trans (congrArg Target.pair target).symm
  keeper := congrArg WalSegment.first keeper
  kept := retained.sealedFiles
  pending := pending
  bounded := bounded

/-- Install the exact selected reader at the reached admission, which
may follow read-only failed attempts after the original reboot. -/
theorem RawAlignedCheckpointReopenEffects.installsQuietSelectionAt
    (seen : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init after
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (valid : state.Valid) (sameHistory : state.writer.history = history)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (next : NativeReadPosition history log)
    (sameReturn : reader.run = next.opened)
    (reached : reader.ReachedSession next.state history log next.reads)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    Nonempty (seen.ReturnedAt next remove write rename bootstrap assemble get set ptrEq) := by
  have pending : PendingClientReplay log next.reads state.writer.history :=
    sameHistory.symm ▸ next.readPrefix.refines.2.2
  have bounded : ∀ read ∈ next.reads, read.BoundedBy state.writer.history.length :=
    sameHistory.symm ▸ next.readPrefix.readsBounded
  let report := reader.markedReport valid.retained target keeper descriptors offsets prepared pending bounded
  obtain ⟨readyPrefix, _, owner, slot, cache, _⟩ := reached
  exact seen.installsAtReportedPosition (report := report)
    next remove write rename bootstrap assemble ptrEq sameHistory sameReturn
    (sameReturn.symm.trans readyPrefix.frames.1) cache owner slot constructs effects

/-- Install the exact session of the one chosen chronological reader.
The same marked callbacks and cache allocation produce the returned
table used by the next public call. -/
theorem RawQuietRestartEffects.installsAligned
    {beforeCensus : DescriptorInventory}
    (seen : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus)
    (valid : state.Valid) (sameHistory : state.writer.history = history)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (next : NativeReadPosition history log)
    (sameReturn : reader.run = next.opened)
    (reached : reader.ReachedSession next.state history log next.reads)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨history, log, next⟩ ∧
      handle.lock = seen.admission.raw.lock ∧
      handle.files.UsesCacheReferences seen.admission.seed.activeRef seen.admission.seed.pendingRef
        seen.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.admission.seed.directoryRef seen.admission.seed.activeRef
        seen.admission.seed.pendingRef = next.state.cache := by
  obtain ⟨returned⟩ := seen.toRawAlignedCheckpointReopenEffects.installsQuietSelectionAt valid sameHistory target keeper
    descriptors offsets prepared next sameReturn reached remove write rename bootstrap assemble constructs effects ptrEq
  exact ⟨returned.cacheOpen, returned.makeCache, returned.handle, returned.start, returned.cacheAction,
    returned.cacheSource, returned.rawOpen, returned.position, returned.lock, returned.references,
    returned.directory, returned.contents, returned.readsPhase, returned.writesPhase,
    returned.comparesTokens, returned.pins, returned.files, returned.census, returned.cache⟩

variable {opened : NativeOpenedHandle heap} {initial current : NativeOpenedPosition opened}

/-- Start a new raw opened-table trace after one settled power loss.
One selected reader supplies the exact physical survivor, the marked
worker, the returned table and the next common ready position. -/
theorem NativeOpenedTrace.restartsThenOpensAligned
    (prior : NativeOpenedTrace initial instructions events current)
    (crash : NativeReadyQuietCrash current.current.ready.state)
    {layout : CanonicalKeeperLayout crash.retry.image current.current.ready.state.writer.history}
    (target : layout.target = current.current.ready.state.writer.target)
    (keeper : layout.keeper = current.current.ready.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] =
      current.current.ready.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first)
      layout.range.watermark = some (layout.first,
        (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    {selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.current.ready.state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash input layout selected}
    (seen : RawQuietRestartEffects reader view calls init names bytes current.reached after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let state := current.current.ready.state
    (view.descriptors after, view.files after) = (crash.reboot, crash.retry) ∧ (view.descriptors after).slots = [] ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      reader.ReachedSession next.state current.current.history current.current.submissions current.current.ready.reads ∧
      reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      NativeReadRecoveryStep current.current.ready (.restart input) next ∧
      NativeExecutionTrace initial.current (events ++ [.readOrRestart (.restart input)]) start.current ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.admission.raw.lock ∧
      handle.files.UsesCacheReferences seen.admission.seed.activeRef seen.admission.seed.pendingRef
        seen.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.admission.seed.directoryRef seen.admission.seed.activeRef
        seen.admission.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨valid, rows, priorReplay⟩ := current.current.ready.readPrefix.refines
  obtain ⟨lost, reached, restart⟩ := crash.restartsAt valid rows priorReplay current.current.ready.readPrefix.readsBounded
    layout target keeper descriptors offsets prepared selected reader
  have reachedSession := restart
  obtain ⟨readyPrefix, directory, owner, slot, cache, census, freshToken, freshPhase, lockInode, directoryInode, _,
    table, checkpoint, durable, _⟩ := restart
  let next : NativeReadPosition current.current.history current.current.submissions :=
    ⟨reader.run, reached, reached, current.current.ready.reads, readyPrefix⟩
  have step : NativeReadRecoveryStep current.current.ready (.restart input) next :=
    .restart current.current.ready crash lost layout selected reader reached readyPrefix owner slot cache census freshToken freshPhase
      ⟨directory, directoryInode, lockInode, table, checkpoint, durable⟩
  obtain ⟨cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ran, currentEq, lock, references, cacheDirectory,
    contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩ :=
    seen.installsAligned valid rows target keeper descriptors offsets prepared next rfl reachedSession
      remove write rename bootstrap assemble constructs effects ptrEq
  refine ⟨Prod.ext seen.admission.raw.entryCensus seen.admission.raw.entryFiles, ?_, next, cacheOpen, makeCache, handle, start,
    cacheAction, cacheSource, reachedSession, rfl, readyPrefix.frames.1, step, ?_, ran, currentEq, lock, references,
    cacheDirectory, contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩
  · rw [seen.admission.raw.entryCensus]
    rfl
  · rw [currentEq]
    exact .step prior.common (.readOrRestart current.current step)

end

section

variable {heap stream : Type} {history : List WAL.Write} {log : List DatabaseSubmissions}
  (current : NativeReadPosition history log) {input : FilePath}
  {crash : NativeReadyQuietCrash current.state}
  {layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history}
  {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
    crash.retry.image.directory.active.manifest current.state.writer.checkpoint}
  {reader : NativeReadyRestartReads crash input layout selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before after : heap} {beforeCensus : DescriptorInventory}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The chosen reader and installer are independent of the operations
that reached this entry, provided they still select the same files. -/
theorem RawAlignedCheckpointReopenEffects.reopensQuietSelection
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init after
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (target : layout.target = current.state.writer.target) (keeper : layout.keeper = current.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = current.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (current.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set) :
    ∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq) := by
  obtain ⟨valid, history, pending⟩ := current.readPrefix.refines
  obtain ⟨_, installed, reached⟩ := crash.restartsAt valid history pending current.readPrefix.readsBounded
    layout target keeper descriptors offsets prepared selected reader
  let next : NativeReadPosition _ _ := ⟨reader.run, installed, installed, current.reads, reached.1⟩
  exact ⟨next, rfl, rfl, reached,
    raw.installsQuietSelectionAt valid history target keeper descriptors offsets prepared next rfl reached
      remove write rename bootstrap assemble constructs effects ptrEq⟩

namespace RawQuietRestartEffects

variable
    (raw : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

/-- The selected files, returned table and next client position are
observed on one reboot and through one chronological reader. -/
structure ReopenedSelected where
  rebooted : (view.descriptors after, view.files after) = (crash.reboot, crash.retry)
  emptyCensus : (view.descriptors after).slots = []
  selectedBytes : ∀ path payload,
    checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
    reader.ReadsSurvivor path payload → ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names before path = some read.object ∧ names after path = some read.object ∧ bytes after read.object = payload
  next : NativeReadPosition history log
  sameReads : next.reads = current.reads
  sameReader : next.opened = reader.run
  session : reader.ReachedSession next.state history log current.reads
  installed : raw.toRawAlignedCheckpointReopenEffects.ReturnedAt next remove write rename bootstrap assemble get set ptrEq

variable {get set}

/-- Recover from one choice that leaves the selected checkpoint and WAL
unchanged. A cut proof can supply any exact pre-reboot inventory, including
one that still holds the issuing run descriptor. -/
theorem reopensSelected
    (target : layout.target = current.state.writer.target) (keeper : layout.keeper = current.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = current.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (current.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set) :
    Nonempty (ReopenedSelected current raw remove write rename bootstrap assemble get set ptrEq) := by
  obtain ⟨next, sameReads, sameReader, reached, ⟨returned⟩⟩ :=
    raw.toRawAlignedCheckpointReopenEffects.reopensQuietSelection current remove write rename bootstrap assemble ptrEq
      target keeper descriptors offsets prepared constructs effects
  refine ⟨⟨Prod.ext raw.admission.raw.entryCensus raw.admission.raw.entryFiles,
    ?_, ?_, next, sameReads, sameReader, reached, returned⟩⟩
  · rw [raw.admission.raw.entryCensus]
    rfl
  · intro path payload isSelected observed
    obtain ⟨read, bound, durable⟩ := raw.admission.reboot.readsSurvivingFile isSelected observed
    have protectedPath : current.state.crashPath path := .inr (.inr isSelected)
    have live := raw.admission.reboot.liveNames path protectedPath
    have survived := crash.settled crash.names crash.chosen path protectedPath
    have restarted := raw.admission.reboot.survivorNames path protectedPath
    exact ⟨read, (live.trans (survived.symm.trans restarted.symm)).trans bound, bound, durable⟩

end RawQuietRestartEffects

end

end Alvoki.Storage.DiskSession
