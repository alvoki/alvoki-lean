import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.NativeOpenWrite
import Alvoki.Storage.Disk.NativeUncertainWritePowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {state : NativeReadyState} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {failed rebooted : heap} {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

def NativeReadyWriteFailure.openCalls (write : NativeReadyWriteFailure state) :
    WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat) :=
  { WriteRequest.Calls.ofFailure write.observed with cache := state.cache }

/-- Project the actual returned single or batch request into its same
reported uncertain diagnostic, cache and files. -/
theorem NativeOpenedPosition.classifiesReportedUncertainWrite (current : NativeOpenedPosition opened)
    (observed : NativeUncertainWriteCrashObservation current.current.ready.state input)
    {cause : IO.Error} {after : OpenWriteFiles}
    (returned : observed.write.request.runOnOpenPhase current.current.ready.state.session.directory observed.write.openCalls
      opened.phase opened.get opened.set (current.reached,
        (WriteRequest.readyCall current.current.ready.state.writer current.current.ready.state.cache).2.image) =
        .error (.commitUnknown cause) (failed, after)) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
      cause = observed.write.failure.cause ∧ after = (observed.cache, observed.write.failure.failed) ∧
      opened.contents failed opened.phase = some .poisoned := by
  intro state
  obtain ⟨source, projected⟩ := current.current.ready.classifiesWriteOnOpenPhase opened.table current.uses
    opened.phaseEffects current.stored observed.write.request observed.write.openCalls rfl
  change projectOpenWriteResult opened.contents opened.phase state.writer.owners
    (observed.write.request.runOnOpenPhase state.session.directory observed.write.openCalls opened.phase opened.get opened.set
      (current.reached, (WriteRequest.readyCall state.writer state.cache).2.image)) = _ at projected
  have known := observed.returned
  change observed.write.openCalls.run observed.write.request state.session.directory state.writer = _ at known
  rw [returned, known] at projected
  cases phase : opened.contents failed opened.phase with
  | none => simp [projectOpenWriteResult, phase] at projected
  | some reached =>
    simp only [projectOpenWriteResult, phase, Option.map_some] at projected
    obtain ⟨diagnostic, effect⟩ := EStateM.Result.error.inj (Option.some.inj projected)
    exact ⟨source, DiskWriteError.commitUnknown.inj diagnostic,
      congrArg (fun result => result.2.image) effect, congrArg some (congrArg Prod.fst effect)⟩

section

variable {crash : WriteCrashView} {history : List WAL.Write} {retry : LockedFileState FileImage}
  {vacant : TryLockObserves retry.owners state.session.directory (.ok true)}
  {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    retry.image.directory.active.manifest state.writer.checkpoint}
  {reader : NativeWriteCrashReads crash input vacant layout selected}
  {finish : CapturedAlignedFinish reader.opening.callbacks reader.opening.reads vacant selected}
  {chosen : CapturedKeeperFinish reader.opening.callbacks reader.opening.reads vacant selected}

private def alignedChronology (chronology : CapturedMarkedReadCensus reader.opening.reads chosen.reader)
    (aligned : chosen = .aligned finish) : CapturedMarkedReadCensus reader.opening.reads finish.readCustody := by
  subst chosen
  exact chronology

private theorem alignedRun (chronology : CapturedMarkedReadCensus reader.opening.reads chosen.reader)
    (aligned : chosen = .aligned finish) :
    (CapturedKeeperFinish.aligned finish).run (alignedChronology chronology aligned) = chosen.run chronology := by
  subst chosen
  rfl

/-- The reader's child identities and read custody provide the same
aligned schedule used by the raw marked opener. -/
private def NativeWriteCrashReads.alignedOpening (reader : NativeWriteCrashReads crash input vacant layout selected)
    (finish : CapturedAlignedFinish reader.opening.callbacks reader.opening.reads vacant selected) :
    CheckpointBarrierAlignedReports input state.session.directory crash.reboot retry layout state.writer.published
      vacant selected crash.names :=
  ⟨reader.opening.admission, reader.opening.callbacks, reader.opening.reads, finish, reader.opening.marker,
    reader.opening.markerFound, reader.manifest, reader.marker,
    reader.wal _ (List.mem_append_right _ (by simp)), fun segment member => reader.wal _ (List.mem_append_left _ member),
    reader.runs⟩

end

variable {observed : NativeUncertainWriteCrashObservation state input}
  {finish : CapturedAlignedFinish observed.effects.reader.opening.callbacks observed.effects.reader.opening.reads
    observed.effects.crash.vacant observed.effects.plan.selected}
  {aligned : observed.effects.reader.opening.finish = .aligned finish}

/-- The reboot starts from the same returned uncertain-write projection
and uses one observed survivor and one aligned raw reader. -/
structure RawUncertainWriteReopenEffects (observed : NativeUncertainWriteCrashObservation state input)
    (finish : CapturedAlignedFinish observed.effects.reader.opening.callbacks observed.effects.reader.opening.reads
      observed.effects.crash.vacant observed.effects.plan.selected)
    (aligned : observed.effects.reader.opening.finish = .aligned finish)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (failed rebooted : heap) (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    extends RawAlignedCheckpointReopenEffects (observed.effects.reader.alignedOpening finish)
      (alignedChronology observed.effects.reader.opening.chronology aligned) view calls init rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream where
  returnedFiles : view.files failed = ⟨observed.write.failure.released.image, state.writer.owners⟩
  returnedCensus : view.descriptors failed = observed.effects.census.reached
  survivorNames : ∀ path, path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
    checkpointSurvivorPath state.session.directory state.writer observed.effects.crash.retry.image.directory.active.manifest path →
    names rebooted path = observed.effects.crash.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer
    observed.effects.crash.retry.image.directory.active.manifest path →
    ∀ inode, observed.effects.crash.names path = some inode → bytes rebooted inode = observed.effects.crash.contents inode

private def NativeUncertainWriteCrashObservation.markedReport (observed : NativeUncertainWriteCrashObservation state input)
    (finish : CapturedAlignedFinish observed.effects.reader.opening.callbacks observed.effects.reader.opening.reads
      observed.effects.crash.vacant observed.effects.plan.selected)
    (aligned : observed.effects.reader.opening.finish = .aligned finish) (valid : state.Valid)
    (pending : PendingClientReplay log reads observed.effects.plan.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy observed.effects.plan.history.length) :
    MarkedOpenSuccessReports input state.session.directory observed.effects.plan.history log reads where
  inventory := observed.effects.crash.reboot
  retry := observed.effects.crash.retry
  layout := observed.effects.plan.layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := observed.effects.plan.selected
  vacant := observed.effects.crash.vacant
  opening := ⟨observed.effects.reader.opening.admission, observed.effects.reader.opening.callbacks,
    observed.effects.reader.opening.reads, .aligned finish, alignedChronology observed.effects.reader.opening.chronology aligned,
    observed.effects.reader.opening.marker, observed.effects.reader.opening.markerFound⟩
  prepared := observed.effects.plan.prepared
  following := observed.effects.reader.opening.reads.walReads.selectedAfterWatermark
    observed.effects.plan.offsets observed.effects.plan.descriptors
  accepted := observed.effects.plan.accepted
  ordered := observed.effects.plan.ordered
  wal := observed.effects.crash.wal observed.effects.plan.history
  walLayout := observed.effects.plan.walLayout
  walValid := observed.effects.plan.walValid
  spans := valid.retained.spans
  active := observed.effects.plan.prepared.pair
  keeper := observed.effects.plan.first
  kept := observed.effects.plan.kept
  pending := pending
  bounded := bounded

section

variable (current : NativeOpenedPosition opened)
  {observed : NativeUncertainWriteCrashObservation current.current.ready.state input}
  {finish : CapturedAlignedFinish observed.effects.reader.opening.callbacks observed.effects.reader.opening.reads
    observed.effects.crash.vacant observed.effects.plan.selected}
  {aligned : observed.effects.reader.opening.finish = .aligned finish}

/-- The returned uncertain diagnostic leads to the exact table admitted
from one reported power-loss survivor. The selected marker determines
the retained whole batch or empty suffix of the common event. -/
theorem NativeOpenedPosition.opensAfterUncertainWrite
    (seen : RawUncertainWriteReopenEffects observed finish aligned view calls init names bytes failed rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    {cause : IO.Error} {after : OpenWriteFiles}
    (returned : observed.write.request.runOnOpenPhase current.current.ready.state.session.directory observed.write.openCalls
      opened.phase opened.get opened.set (current.reached,
        (WriteRequest.readyCall current.current.ready.state.writer current.current.ready.state.cache).2.image) =
        .error (.commitUnknown cause) (failed, after))
    (samePhase : view.phase = opened.contents)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    let effects := observed.effects
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    cause = observed.write.failure.cause ∧ after = (observed.cache, observed.write.failure.failed) ∧
    view.phase failed opened.phase = some .poisoned ∧
    (view.descriptors failed, view.files failed) =
      (effects.census.reached, ⟨observed.write.failure.released.image, state.writer.owners⟩) ∧
    (view.descriptors rebooted, view.files rebooted) = (effects.crash.reboot, effects.crash.retry) ∧
    (view.descriptors rebooted).slots = [] ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer
      effects.crash.retry.image.directory.active.manifest path → effects.reader.ReadsSurvivor path payload →
      ∃ read : effects.reader.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (retained : List WAL.Write)
      (next : NativeReadPosition (current.current.history ++ retained)
        (current.current.submissions ++ [.uncertainBatch observed.write.failure.batch]))
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativeUncertainWriteCrashContinuation current.current.ready observed retained next ∧
      NativeExecutionStep current.current (.uncertainWriteCrashRecovered observed.write.request input cause
        observed.write.failure.batch retained) start.current ∧
      seen.toRawAlignedCheckpointReopenEffects.openTable remove write rename bootstrap assemble makeCache =
        .ok handle.table start.reached ∧
      start.current = ⟨current.current.history ++ retained,
        current.current.submissions ++ [.uncertainBatch observed.write.failure.batch], next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache := by
  intro state effects
  obtain ⟨source, diagnostic, afterEq, poison⟩ := current.classifiesReportedUncertainWrite observed returned
  obtain ⟨retained, next, reopened⟩ := current.current.ready.recoversUncertainWriteAfterPowerLoss observed
  obtain ⟨chosen, _, sameReturn, nextReturned, _, cache, _, owner, slot, _, _⟩ := reopened.exactOpen
  have pending := next.readPrefix.refines.2.2
  have bounded := next.readPrefix.readsBounded
  rw [reopened.reads, ← chosen] at pending bounded
  let marked := observed.markedReport finish aligned current.current.ready.readPrefix.refines.1 pending bounded
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, ran⟩ := marked.opensAlignedFromAdmission seen.raw seen.seed
    finish rfl seen.checkpoint seen.listing seen.extents seen.seals seen.keeper seen.sameLookup seen.flat seen.marked
    remove write rename bootstrap assemble constructs seen.allocations
  have worker : marked.opening.finish.run marked.opening.chronology = next.opened :=
    (alignedRun effects.reader.opening.chronology aligned).trans sameReturn.symm
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, getEq, setEq, compareEq, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen chosen next worker nextReturned cache owner slot phaseEffects opened.ptrEq
  refine ⟨source, diagnostic, afterEq, ?_, Prod.ext seen.returnedCensus seen.returnedFiles,
    Prod.ext seen.raw.entryCensus seen.raw.entryFiles, ?_, ?_, ?_, ?_, retained, next, cacheOpen, makeCache, handle,
    start, cacheAction, cacheSource, reopened, ?_, ?_, currentEq, lock, files.symm ▸ installed.cacheReferences,
    files.symm ▸ installed.cacheDirectory, contents, getEq, setEq, compareEq, token, pins, sameFiles, sameCensus, sameCache⟩
  · rw [samePhase]
    exact poison
  · rw [seen.raw.entryCensus]
    rfl
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact (seen.survivorNames _ (.inr (.inl rfl))).trans
      ((effects.reader.opening.reads.sameObjects.2.1.symm).trans effects.reader.lock).symm
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact (seen.survivorNames _ (.inl rfl)).trans
      ((effects.reader.opening.reads.sameObjects.1.symm).trans effects.reader.directory).symm
  · intro path payload pathSelected ⟨file, bound, returnedBytes⟩
    exact ⟨file, (seen.survivorNames path (.inr (.inr pathSelected))).trans bound,
      (seen.survivorBytes path pathSelected file.object bound).trans returnedBytes⟩
  · rw [currentEq, diagnostic]
    exact .recoverUncertainWriteCrash current.current observed retained next reopened
  · rw [rawTable, reachedHeap]
    exact ran

end

end Alvoki.Storage.DiskSession
