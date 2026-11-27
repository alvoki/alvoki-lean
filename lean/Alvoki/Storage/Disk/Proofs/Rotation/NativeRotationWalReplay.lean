import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationReadyStorage
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationWalWindow
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRawRotationReboot
import Alvoki.Storage.Disk.NativeAlignedReadyCalls

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {opened : NativeOpenedHandle heap} {current position : NativeOpenedPosition opened}

local notation "old" => current.current.ready.state
local notation "rotated" => position.current.ready.state

/-- A successful nonempty rotation provides the next write entry. Gaps in the
old WAL interval, apart from the successor, determine the interval available
to later calls. A reboot in that interval reuses the ordinary WAL reader. -/
def OpenRotationObservation.ContinuesWal
    {read create sync entry settled reset} (seen : OpenRotationObservation current read create sync entry settled reset)
    (position : NativeOpenedPosition opened) (root : DeviceInode)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop :=
  NativeReadyStorage old (storage current.reached) →
  seen.LocalFrames (fun a b => (storage a).Frames (old).crashPath (storage b)) →
  (seen.view.files position.reached).image.ObservesWalChild root position.current.ready.state.session.directory
    position.current.ready.state.writer.wal.active.first (storage position.reached) (visible position.reached) →
  position.WriteStorageEntry seen.view (seen.writeCache position) (storage position.reached) (visible position.reached) ∧
  ∀ through,
    (∀ start ≤ through, start ≠ (old).writer.wal.active.last →
      (old).writer.wal.SettledNamespaceWindow (old).session.directory start start (storage current.reached)) →
    seen.LocalFrames (fun a b => RotationWalNameFrame (old).session.directory 0 through (old).writer.wal.active.last
      (storage a) (storage b)) →
    position.WalWindowAt storage 0 through ∧
    ∀ {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
      (images : heap → FileImage) {rebooted : heap} (namespaceView : DirectoryReadNamespace) (heldRoot : DeviceInode),
      let view := seen.view.withFileProjection (fun h => ⟨images h, (seen.view.files h).owners⟩)
      ∀ sample : RawWriteRebootEntry position.current.ready.state view storage (fun h => (storage h).files.names) visible position.reached rebooted,
        sample.DurableReset → position.current.ready.state.writer.target.range.through ≤ through → (old).writer.target.pair.manifest = none →
        source.ReadsClientHistoryAtOpen view position.current.ready.state.session.directory
          storage visible rebooted namespaceView heldRoot
          current.current.submissions current.current.ready.reads current.current.history

private theorem OpenRotationObservation.Reached.continuesWal
    {read create sync entry settled reset} {seen : OpenRotationObservation current read create sync entry settled reset}
    {lookup} (returned : seen.Reached lookup position)
    {next : NativeReadPosition current.current.history current.current.submissions}
    (atState : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    (rotation : NativeRotationFrame current.current.ready next)
    (manifest : (rotated).writer.target.pair.manifest = (old).writer.target.pair.manifest)
    {root storage visible}
    (entryAt : NativeReadyStorage old (storage current.reached) →
      seen.LocalFrames (fun a b => (storage a).Frames (old).crashPath (storage b)) →
      (seen.view.files position.reached).image.ObservesWalChild root (rotated).session.directory
        (rotated).writer.wal.active.first (storage position.reached) (visible position.reached) →
      position.WriteStorageEntry seen.view (seen.writeCache position) (storage position.reached) (visible position.reached)) :
    seen.ContinuesWal position root storage visible := by
  intro initial keeps child
  have ready := entryAt initial keeps child
  refine ⟨ready, ?_⟩
  intro through gaps names
  have catalog := returned.walWindow atState rotation storage (fun _ _ => Nat.zero_le _) (fun s _ => gaps s)
    names ready.physical.activeWalPresent
  refine ⟨catalog, ?_⟩
  intro stream source images rebooted namespaceView heldRoot view sample reset within absent
  obtain ⟨valid, history, pending⟩ := position.current.ready.readPrefix.refines
  have opens := @RawWriteRebootEntry.replaysWalBeforeCheckpointAtOpen _ _ _ _ source _ _ _ _ namespaceView heldRoot
    sample valid ready.physical reset (catalog.restrictUpper within).2 (manifest.trans absent)
  have sameHistory : position.current.history = current.current.history := by rw [atState]
  rw [history.trans sameHistory] at opens
  rw [atState] at pending
  change PendingClientReplay current.current.submissions next.reads current.current.history at pending
  rw [rotation.reads] at pending
  intro input returnedAt table
  exact opens.recordsReads pending (input := input) (returnedAt := returnedAt) (table := table)

/-- The exclusive-create route supplies the postcondition at the actual return. -/
theorem NativeOpenedPosition.rotatesCreatedWithWal
    (report : NativeReadyCreatedRotation old) (seen : OpenRotationObservation.Created current report)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :
    ∃ position, seen.Reached report.lookup position ∧ NativeExecutionStep current.current .rotatedWal position.current ∧
      seen.ContinuesWal position report.parent.root storage visible := by
  obtain ⟨next, position, rotation, step, atState, returned⟩ := current.rotatesCreatedOnOpenPhase report seen
  refine ⟨position, returned, step, returned.continuesWal atState rotation.frame ?_ ?_⟩
  · rw [atState]; change next.state.writer.target.pair.manifest = _
    rw [rotation.reached]; rfl
  · exact rotation.writeStorageEntry returned atState

/-- The same continuation also follows the observed reuse of a private empty successor. -/
theorem NativeOpenedPosition.rotatesExistingWithWal
    (report : NativeReadyExistingRotation old) (seen : OpenRotationObservation.Existing current report)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) :
    ∃ position, seen.Reached report.opened.lookup position ∧ NativeExecutionStep current.current .rotatedWal position.current ∧
      seen.ContinuesWal position report.opened.root storage visible := by
  obtain ⟨next, position, rotation, step, atState, returned⟩ := current.rotatesExistingOnOpenPhase report seen
  refine ⟨position, returned, step, returned.continuesWal atState rotation.frame ?_ ?_⟩
  · rw [atState]; change next.state.writer.target.pair.manifest = _
    rw [rotation.reached]; rfl
  · exact rotation.writeStorageEntry returned atState

/-- Follow the actual returned calls on one open handle to a failed
nonempty rotation. Its observed ready phase identifies the prefix that
supplies the physical cache, WAL window and client ledger. Before the
first checkpoint, the selected sample is also sufficient for the ordinary
reader and the writer installed by a later aligned open. The reached
create and pending-cache callbacks determine where those effects apply. -/
theorem NativeReturnedCalls.samplesAfterFailedRotationDirectory
    {heap : Type} {opened : NativeOpenedHandle heap}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    (start : NativeOpenedPosition opened) {calls : List (NativeReturnedCall opened)} {reached : heap}
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) calls reached)
    {installed : Installed} (phase : opened.get opened.phase reached = .ok (.ready installed) reached)
    (view : OpenCloseHeapView heap FileImage) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (initial : writes.StorageAt view storage (fun h => (inodes h).visible) start)
    {horizon : Nat} (nameEffects : writes.WalWindowEffects storage 0 horizon)
    (initialWindow : start.WalWindowAt storage 0 horizon)
    (coversCutoff : installed.walBytes / WAL.frameSize ≤ horizon)
    (rotation : OpenRotationCallbacks heap) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      last.reached = reached ∧
      last.current.ready.state.writer.installed = installed ∧
      last.pins.map NativeOpenedPin.raw =
        calls.foldl (fun pins call => call.pinsAfter pins) (start.pins.map NativeOpenedPin.raw) ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      start.current.LedgerSuffix events last.current ∧
      let state := last.current.ready.state
      let visible := fun h => (inodes h).visible
      let bindings : heap → FilePath → Option Nat := fun h => (storage h).files.names
      ∀ {poisoned afterFileSync : heap}
        (guard : BatchActiveGuard opened.directory installed)
        (_nonempty : installed.activeFirst < installed.walBytes / WAL.frameSize)
        (_poisonedAt : opened.set opened.phase .poisoned reached = .ok () poisoned)
        (filePrefix : rotation.SuccessorFilePrefix opened.directory state.writer.rotationInstalled.activeFirst
          poisoned afterFileSync)
        (barrier : rotation.FailedRootBarrier writes.syncer writes.cache afterFileSync),
        rotation.run opened guard.lookup writes.cache.active reached =
          .error (IO.userError s!"sync failed for '{opened.directory.path}': {barrier.cause}") barrier.failed ∧
        let successor := opened.directory.file (.walSegment state.writer.rotationInstalled.activeFirst)
        ∀ {rebooted : heap} {effective : Bool}
          (absent : filePrefix.observed = none)
          (create : rotation.create successor filePrefix.afterRead = (do
            let handle ← writes.stager.create successor
            writes.stager.remember writes.cache.pending (pushPending successor handle)) filePrefix.afterRead)
          (fileSync : rotation.sync successor filePrefix.beforeSync =
            writes.syncer.group opened.directory.path writes.cache.directory writes.cache.active writes.cache.pending
              #[successor] filePrefix.beforeSync)
          (stored : ∀ {handle openedAt}, writes.stager.create successor filePrefix.afterRead = .ok handle openedAt →
            writes.stager.remember writes.cache.pending (pushPending successor handle) openedAt =
              .ok () filePrefix.beforeSync →
            view.pending filePrefix.beforeSync writes.cache.pending =
              pushPending successor handle (view.pending openedAt writes.cache.pending))
          (loaded : ∀ {entries loaded}, writes.syncer.readPending writes.cache.pending filePrefix.beforeSync =
            .ok entries loaded → entries = view.pending filePrefix.beforeSync writes.cache.pending),
          let file := Classical.choice (filePrefix.reachesExclusiveSync writes.stager writes.syncer writes.cache view
            absent create fileSync stored loaded)
          ∀ (_fileEffects :
            file.SuccessorEffects view storage visible last.reached barrier.issued ∧
            file.PreservesFiles view storage (state.rotationProtectedScope 0 horizon) last.reached barrier.issued)
          (_rootEffects : filePrefix.RootErrorEffects barrier view storage effective last.reached),
          let selected := state.rotationWriterAtSample last.current.ready.readPrefix.refines.1 (bindings rebooted)
          ∀ (_chosen : bindings rebooted ∈ (storage barrier.failed).crashNames),
            selected.history = last.current.history ∧
            PendingClientReplay last.current.submissions last.current.ready.reads selected.history ∧
            (∀ offset, last.current.history.length < offset → offset ≤ horizon →
              bindings rebooted (state.session.directory.file (.walSegment offset)) = none) ∧
            ∀ {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
              (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
              (_beforeCheckpoint : start.current.ready.state.writer.target.pair.manifest = none)
              (_sampled : ∀ path, checkpointSurvivorPath state.session.directory selected selected.target.pair.manifest path →
                ∀ object, bindings rebooted path = some object → visible rebooted object ∈ (storage barrier.failed).files.bytes object)
              {errors : List (FilePath × IO.Error)} {retryAt : heap}
              (attempts : source.FailedCalls rebooted errors retryAt)
              (_retryEffects : attempts.PreserveWalFiles (directory := state.session.directory) horizon bindings visible),
              (∀ offset, selected.history.length < offset → offset ≤ horizon →
                bindings retryAt (state.session.directory.file (.walSegment offset)) = none) ∧
              source.ReadsClientHistoryAtOpen
                (view.withObservedWalFiles state.session.directory selected.wal.active.first bindings visible)
                state.session.directory storage visible retryAt namespaceView root
                last.current.submissions last.current.ready.reads selected.history ∧
              ∀ (_restored : ∀ path, selected.walOpenDurablePath state.session.directory path → path ≠ state.session.directory.path →
                  ∀ object, bindings rebooted path = some object →
                    (storage rebooted).files.bytes object = [visible rebooted object])
                (_rootSettled : ∀ names ∈ (storage rebooted).crashNames,
                  names state.session.directory.path = bindings rebooted state.session.directory.path)
                (_kept : ∀ {prior : List (FilePath × IO.Error)} {before after : heap} {input : FilePath} {cause : IO.Error},
                  source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(input, cause)]) errors →
                  source.openTable input before = .error cause after →
                  (storage before).Frames (selected.walOpenDurablePath state.session.directory) (storage after)),
                source.WritesAfterWalOpen view state.session.directory selected retryAt namespaceView root
                  start.current events inodes runs storage := by
  have notPoisoned : opened.contents reached opened.phase ≠ some .poisoned := by
    intro poisoned
    cases phase.symm.trans (opened.phaseEffects.reads reached opened.phase .poisoned poisoned)
  have covered := executed.readyResponsesOfNotPoisoned view inodes runs storage inode buffered effects
    start rfl rfl initial notPoisoned
  obtain ⟨last, events, atRotation, pins, physical, length, records, ledger, _, ⟨manifest, _⟩, frames⟩ :=
    executed.refinesReadyFramed covered view inodes runs storage inode buffered effects start rfl rfl initial
  obtain ⟨valid, currentHistory, pending⟩ := last.current.ready.readPrefix.refines
  have stored := last.stored.trans (congrArg some valid.phase)
  have reachedReady := opened.phaseEffects.reads last.reached opened.phase _ stored
  have installedAtRotation : installed = last.current.ready.state.writer.installed := by
    have reachedPhase := (EStateM.Result.ok.inj (phase.symm.trans (atRotation ▸ reachedReady))).1
    injection reachedPhase
  subst installed
  refine ⟨last, events, atRotation, rfl, pins, length, records, ledger, ?_⟩
  intro state visible bindings poisoned afterFileSync guard nonempty poisonedAt filePrefix barrier
  have returned := (last.rotationReturnsDirectoryError rotation writes.syncer writes.cache guard nonempty
    (atRotation.symm ▸ poisonedAt) filePrefix barrier.route barrier.loaded barrier.returned).2.2.1
  refine ⟨atRotation ▸ returned, ?_⟩
  intro successor rebooted effective absent create fileSync storedPending loadedPending
    file effectsAtFile rootEffects selected chosen
  obtain ⟨fileEffects, fileFrames⟩ := effectsAtFile
  have cutoff := valid.retained.resumed.through.trans (congrArg List.length currentHistory)
  have within : state.writer.target.range.through ≤ horizon :=
    (valid.retained.rotationAtEnd.trans valid.retained.resumed.through.symm) ▸ coversCutoff
  have window := (frames nameEffects initialWindow).2
  obtain ⟨_, ready, sampledHistory, pair, _, noLater, _, _, sampledFiles⟩ := last.samplesFailedRotationDirectory
      rotation writes.syncer view writes.cache storage visible filePrefix file barrier fileEffects rootEffects
      nonempty physical fileFrames within window chosen
  have sameHistory := sampledHistory.trans currentHistory
  have replay : PendingClientReplay last.current.submissions last.current.ready.reads selected.history :=
    sameHistory.symm ▸ pending
  have absent offset (beyond : last.current.history.length < offset) (upper : offset ≤ horizon) :
      bindings rebooted (state.session.directory.file (.walSegment offset)) = none :=
    noLater offset (cutoff.symm ▸ beyond) upper
  refine ⟨sameHistory, replay, absent, ?_⟩
  intro stream source namespaceView root beforeCheckpoint sampled errors retryAt attempts retryEffects
  have noManifest := manifest.trans beforeCheckpoint
  have missing := (congrArg DirectoryPublication.Bindings.manifest pair).trans noManifest
  have bootFiles := sampledFiles sampled noManifest
  have covers : selected.history.length ≤ horizon := by
    rw [sameHistory, ← cutoff]
    exact within
  obtain ⟨carries, openedRetry, startsWriter⟩ := attempts.reopensSampledWal (view := view)
    (namespaceView := namespaceView) (root := root) inodes runs storage ready missing bootFiles covers retryEffects
  refine ⟨carries (by simpa only [sameHistory] using absent),
    @RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen.recordsReads (opened := openedRetry) (pending := replay), ?_⟩
  intro restored rootSettled kept
  have durable := bootFiles.durabilityAfterRebootRetries ready restored rootSettled attempts kept
  exact @startsWriter _ _ _ sameHistory ledger durable

end Alvoki.Storage.DiskSession
