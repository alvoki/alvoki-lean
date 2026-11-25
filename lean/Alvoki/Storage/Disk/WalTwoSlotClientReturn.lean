import Alvoki.Storage.Disk.PendingClientReplay
import Alvoki.Storage.Disk.WalSegmentCachedRetryReads
import Alvoki.Storage.Disk.WalSegmentSizedCheckpointReports
import Alvoki.Storage.Disk.WalSegmentCachedExtentOpenEffects
import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
import Alvoki.Storage.Disk.WalTwoSlotReopenProjection
import Alvoki.Storage.Disk.BatchInterruptionDispatch
import Alvoki.Storage.Disk.SyncHandleEffects
import Alvoki.Storage.Disk.AppendHandleCustody
import Alvoki.Storage.Disk.DescriptorInventory
import Alvoki.Storage.Disk.CapturedLongKeeperInstallation
import Alvoki.Storage.Disk.CapturedPrunedAlignedInstallation

namespace Alvoki.WAL.TwoSlot

open Alvoki.Storage

private def setPhase {α σ : Type} (phase : DiskSession.Phase α) :
    EStateM ε (DiskSession.Phase α × σ) Unit :=
  fun (_, files) => .ok () (phase, files)

private def commitReports {α σ : Type} (publish : EStateM IO.Error σ Unit) :
    EStateM DiskWriteError (DiskSession.Phase α × σ) Unit :=
  fun (phase, files) =>
    match publish files with
    | .ok _ after => .ok () (phase, after)
    | .error cause after => .error (.commitUnknown cause) (phase, after)

/-- Interpret the returned branch of the actual session publication wrapper
over the exact ordered marker effect reports. A publication error retains
the reached files and leaves no ready table or acknowledged sequence. -/
theorem prepared_write_reports {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α) (files : σ)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit) :
    DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
      match publish append syncWal writeSlot syncSlot install files with
      | .ok _ after => .ok sequence (.ready next, after)
      | .error cause after => .error (.commitUnknown cause) (.poisoned, after) := by
  cases result : publish append syncWal writeSlot syncSlot install files <;>
  simp only [DiskSession.publishPreparedWrite, DiskSession.publishPrepared, setPhase,
    commitReports, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, result]

/-- With no pending handle for the keeper, the two-slot WAL barrier
uses the exact description that wrote and flushed the preceding append. -/
theorem appendThenSync_sameHandle {handle state : Type}
    (cache : SyncHandleRouting.Cache handle) (before : state)
    (directory keeper : System.FilePath) (frame : ByteArray)
    (openAppend openRead : System.FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit)
    (flush fsync : handle → EStateM IO.Error state Unit)
    {file : handle} {opened written appended : state}
    (keeperNotDirectory : keeper ≠ directory)
    (keeperMiss : cache.pending.find? (fun entry => entry.1 == keeper) = none)
    (selected : SyncHandleRouting.selectAppendHandle cache.active openAppend keeper before = .ok file opened)
    (wrote : write file frame opened = .ok () written)
    (flushed : flush file written = .ok () appended) :
    ((SyncHandleRouting.runAppendWithCache keeper frame openAppend write flush >>= fun _ =>
      SyncHandleRouting.sync directory openRead fsync keeper) (cache, before)) =
    SyncHandleRouting.withCache { cache with active := some (keeper, file) } (fsync file appended) := by
  simp [SyncHandleRouting.runAppendWithCache_effect, SyncHandleRouting.sync, SyncHandleRouting.Cache.resolve,
    Bind.bind, EStateM.bind, keeperNotDirectory, keeperMiss, selected, wrote, flushed]

/-- A valid pending handle can take precedence over the append handle.
Both handles still name the same inode under the cache binding invariant. -/
theorem resolveAfterAppend_sameInode {handle state : Type}
    {cache : SyncHandleRouting.Cache handle} {directory keeper : System.FilePath}
    {inode : handle → Nat} {bindings : state → System.FilePath → Option Nat}
    {openRead : System.FilePath → EStateM IO.Error state handle}
    {appended : state} {file : handle}
    (notDirectory : keeper ≠ directory)
    (active : cache.active = some (keeper, file))
    (owned : cache.Agrees directory inode (bindings appended)) :
    ∃ synced resolved,
      cache.resolve directory keeper openRead appended = .ok synced (resolved, appended) ∧
      inode synced = inode file ∧ resolved.Agrees directory inode (bindings appended) := by
  have appendBinding := owned.active active
  cases pending : cache.pending.find? (fun entry => entry.1 == keeper) with
  | none =>
    exact ⟨file, cache, by simp [SyncHandleRouting.Cache.resolve, notDirectory, active, pending], rfl, owned⟩
  | some entry =>
    obtain ⟨path, captured⟩ := entry
    have same : path = keeper := by
      simpa using List.find?_some pending
    subst path
    exact ⟨captured, cache.consume keeper, by simp [SyncHandleRouting.Cache.resolve, notDirectory, pending],
      Option.some.inj ((owned.pending pending).symm.trans appendBinding), owned.consume⟩

/-- The executed append and cache-routed barrier use descriptions for
one inode. The result preserves the exact reached cache and syscall result. -/
theorem appendThenSync_sameInode {handle state : Type}
    (cache : SyncHandleRouting.Cache handle) (before : state)
    (directory keeper : System.FilePath) (frame : ByteArray)
    (openAppend openRead : System.FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit)
    (flush fsync : handle → EStateM IO.Error state Unit)
    (bindings : state → System.FilePath → Option Nat) (inode : handle → Nat)
    {file : handle} {opened written appended : state}
    (notDirectory : keeper ≠ directory)
    (owned : cache.Agrees directory inode (bindings before))
    (fresh : ∀ {captured after}, openAppend keeper before = .ok captured after →
      bindings after keeper = some (inode captured))
    (selected : SyncHandleRouting.selectAppendHandle cache.active openAppend keeper before = .ok file opened)
    (wrote : write file frame opened = .ok () written)
    (flushed : flush file written = .ok () appended)
    (bindingsPreserved : bindings appended = bindings before)
    (selectedPreserved : bindings appended keeper = bindings opened keeper) :
    ∃ synced resolved,
      inode synced = inode file ∧ resolved.Agrees directory inode (bindings appended) ∧
      ((SyncHandleRouting.runAppendWithCache keeper frame openAppend write flush >>= fun _ =>
        SyncHandleRouting.sync directory openRead fsync keeper) (cache, before)) =
        SyncHandleRouting.withCache resolved (fsync synced appended) := by
  obtain ⟨appendResult, activeOwned⟩ := SyncHandleRouting.runAppendWithCache_owned
    frame openAppend write flush bindings inode owned fresh selected wrote flushed
    bindingsPreserved selectedPreserved
  obtain ⟨synced, resolved, lookup, same, resolvedOwned⟩ :=
    resolveAfterAppend_sameInode (openRead := openRead) notDirectory rfl activeOwned
  exact ⟨synced, resolved, same, resolvedOwned, by
    simp only [Bind.bind, EStateM.bind, appendResult, SyncHandleRouting.sync, lookup]⟩

/-- A returned error before marker publication keeps the exact file
state reached by the append or WAL barrier and poisons the writer. -/
theorem prepared_write_walError {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files reached : σ} {cause : IO.Error}
    (failed : append files = .error cause reached ∨
      ∃ appended, append files = .ok () appended ∧ syncWal appended = .error cause reached) :
    DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .error (.commitUnknown cause) (.poisoned, reached) := by
  rw [prepared_write_reports, publish_reports]
  rcases failed with appendError | ⟨appended, wrote, syncError⟩
  · simp only [appendError]
  · simp only [wrote, syncError]

/-- If the slot write or marker barrier fails after the WAL barrier, the
client receives commit-unknown with exactly the reached file state.
The marker barrier runs only after a successful slot write. Installation
is skipped in either case. -/
theorem prepared_write_markerError {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files appended durable reached : σ} {cause : IO.Error}
    (wrote : append files = .ok () appended)
    (walBarrier : syncWal appended = .ok () durable)
    (failed : writeSlot durable = .error cause reached ∨
      ∃ written, writeSlot durable = .ok () written ∧ syncSlot written = .error cause reached) :
    DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .error (.commitUnknown cause) (.poisoned, reached) := by
  rw [prepared_write_reports, publish_reports]
  rcases failed with writeError | ⟨written, slotWritten, syncError⟩
  · simp only [wrote, walBarrier, writeError]
  · simp only [wrote, walBarrier, slotWritten, syncError]

/-- The callback that failed can be recovered from the reported client
error. Installation is a cache update and is assumed to succeed. -/
theorem prepared_write_errorStage {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files reached : σ} {cause : IO.Error}
    (installOk : ∀ state, ∃ installed, install state = .ok () installed)
    (returned : DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .error (.commitUnknown cause) (.poisoned, reached)) :
    (append files = .error cause reached ∨
      ∃ appended, append files = .ok () appended ∧ syncWal appended = .error cause reached) ∨
    ∃ appended durable, append files = .ok () appended ∧ syncWal appended = .ok () durable ∧
      (writeSlot durable = .error cause reached ∨
        ∃ written, writeSlot durable = .ok () written ∧ syncSlot written = .error cause reached) := by
  rw [prepared_write_reports, publish_reports] at returned
  cases wrote : append files with
  | error error state =>
    simp [wrote] at returned
    obtain ⟨rfl, rfl⟩ := returned
    exact .inl (.inl rfl)
  | ok _ appended =>
    cases walBarrier : syncWal appended with
    | error error state =>
      simp [wrote, walBarrier] at returned
      obtain ⟨rfl, rfl⟩ := returned
      exact .inl (.inr ⟨appended, rfl, walBarrier⟩)
    | ok _ durable =>
      cases slotWrite : writeSlot durable with
      | error error state =>
        simp [wrote, walBarrier, slotWrite] at returned
        obtain ⟨rfl, rfl⟩ := returned
        exact .inr ⟨appended, durable, rfl, walBarrier, .inl slotWrite⟩
      | ok _ written =>
        cases markerBarrier : syncSlot written with
        | error error state =>
          simp [wrote, walBarrier, slotWrite, markerBarrier] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact .inr ⟨appended, durable, rfl, walBarrier, .inr ⟨written, slotWrite, markerBarrier⟩⟩
        | ok _ synced =>
          obtain ⟨installed, completed⟩ := installOk synced
          simp [wrote, walBarrier, slotWrite, markerBarrier, completed] at returned

/-- Dispatch recovery of a commit-unknown result to the filesystem
contract of the reached callback, using the exact states from that run. -/
theorem prepared_write_recoverUnknown {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files reached : σ} {cause : IO.Error} {recovers : Prop}
    (installOk : ∀ state, ∃ installed, install state = .ok () installed)
    (returned : DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .error (.commitUnknown cause) (.poisoned, reached))
    (onAppend : append files = .error cause reached → recovers)
    (onWalSync : ∀ appended, append files = .ok () appended →
      syncWal appended = .error cause reached → recovers)
    (onSlotWrite : ∀ appended durable, append files = .ok () appended →
      syncWal appended = .ok () durable → writeSlot durable = .error cause reached → recovers)
    (onMarkerSync : ∀ appended durable written, append files = .ok () appended →
      syncWal appended = .ok () durable → writeSlot durable = .ok () written →
      syncSlot written = .error cause reached → recovers) : recovers := by
  rcases prepared_write_errorStage next sequence prior append syncWal writeSlot syncSlot install
      installOk returned with (failed | ⟨appended, wrote, failed⟩) |
      ⟨appended, durable, wrote, synced, failed | ⟨written, wroteSlot, failed⟩⟩
  · exact onAppend failed
  · exact onWalSync appended wrote failed
  · exact onSlotWrite appended durable wrote synced failed
  · exact onMarkerSync appended durable written wrote synced wroteSlot failed

/-- A client acknowledgement supplies successful reports for all four
file operations in execution order, including the marker barrier. -/
theorem prepared_write_acknowledged {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files after : σ}
    (returned : DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .ok sequence (.ready next, after)) :
    ∃ appended walSynced written slotSynced,
      append files = .ok () appended ∧ syncWal appended = .ok () walSynced ∧
      writeSlot walSynced = .ok () written ∧ syncSlot written = .ok () slotSynced ∧
      install slotSynced = .ok () after := by
  rw [prepared_write_reports] at returned
  have published : publish append syncWal writeSlot syncSlot install files = .ok () after := by
    cases outcome : publish append syncWal writeSlot syncSlot install files with
    | error cause reached => simp [outcome] at returned
    | ok value reached =>
      cases value
      simp [outcome] at returned
      subst reached
      rfl
  rw [publish_reports] at published
  cases appended : append files with
  | error cause reached => simp [appended] at published
  | ok value appendedFiles =>
    cases value
    cases walSynced : syncWal appendedFiles with
    | error cause reached => simp [appended, walSynced] at published
    | ok value walFiles =>
      cases value
      cases written : writeSlot walFiles with
      | error cause reached => simp [appended, walSynced, written] at published
      | ok value writtenFiles =>
        cases value
        cases slotSynced : syncSlot writtenFiles with
        | error cause reached => simp [appended, walSynced, written, slotSynced] at published
        | ok value syncedFiles =>
          cases value
          exact ⟨appendedFiles, walFiles, writtenFiles, syncedFiles, rfl, walSynced, written,
            slotSynced, by simpa only [appended, walSynced, written, slotSynced] using published⟩

/-- A process stop during append leaves the state reported by that append.
No WAL sync or marker mutation is issued by the remaining schedule. -/
theorem publish_appendInterrupted {stop image : Type}
    (append syncWal writeSlot syncSlot install : ExceptT IO.Error (EStateM stop image) Unit)
    {before reached : image} {stopped : stop}
    (cut : append.run before = .error stopped reached) :
    (publish append syncWal writeSlot syncSlot install).run before = .error stopped reached := by
  change append before = .error stopped reached at cut
  simp [publish, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind, cut]

/-- A process stop at the WAL barrier leaves the marker publication
unissued. The caller sees an interrupted operation with no return. -/
theorem publish_walSyncInterrupted {stop image : Type}
    (append syncWal writeSlot syncSlot install : ExceptT IO.Error (EStateM stop image) Unit)
    {before appended reached : image} {stopped : stop}
    (wrote : append.run before = .ok (.ok ()) appended)
    (cut : syncWal.run appended = .error stopped reached) :
    (publish append syncWal writeSlot syncSlot install).run before = .error stopped reached := by
  change append before = .ok (.ok ()) appended at wrote
  change syncWal appended = .error stopped reached at cut
  simp [publish, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, wrote, cut]

/-- A stop reached inside the inactive-slot write keeps its reported
physical state and never issues the marker barrier. -/
theorem publish_slotWriteInterrupted {stop image : Type}
    (append syncWal writeSlot syncSlot install : ExceptT IO.Error (EStateM stop image) Unit)
    {before appended durable reached : image} {stopped : stop}
    (wrote : append.run before = .ok (.ok ()) appended)
    (walBarrier : syncWal.run appended = .ok (.ok ()) durable)
    (cut : writeSlot.run durable = .error stopped reached) :
    (publish append syncWal writeSlot syncSlot install).run before = .error stopped reached := by
  change append before = .ok (.ok ()) appended at wrote
  change syncWal appended = .ok (.ok ()) durable at walBarrier
  change writeSlot durable = .error stopped reached at cut
  simp [publish, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    wrote, walBarrier, cut]

open DiskSession (Installed LockedFileState runBatchWriteWithInterruption runBatchWriteWithInterruption_stopped)

/-- Interpret a prepared batch once its slot preflight has admitted the
publication. Interruption in the positional write reaches the poisoned
writer with the exact reached image and no acknowledgement. -/
theorem runBatch_slotWriteInterrupted {stop image : Type} {directory : DiskDirectory}
    {rows : List (UInt64 × Option UInt64)} {installed : Installed}
    {events : List Write} {table : PackedTable}
    {lookup : System.FilePath → Except IO.Error IO.FS.Metadata}
    (nonempty : rows ≠ []) (prepared : prepareBatch installed.table rows = some (events, table))
    (fits : installed.walBytes + frameSize * rows.length < UInt64.size)
    (guard : checkActiveSegmentWith directory installed lookup = .ok ())
    (append syncWal writeSlot syncSlot install : ExceptT IO.Error (EStateM stop image) Unit)
    {before : LockedFileState image} {appended durable reached : image} {stopped : stop}
    (wrote : append.run before.image = .ok (.ok ()) appended)
    (walBarrier : syncWal.run appended = .ok (.ok ()) durable)
    (cut : writeSlot.run durable = .error stopped reached) :
    runBatchWriteWithInterruption directory rows lookup
      (fun _ _ _ => publish append syncWal writeSlot syncSlot install) (.ready installed, before) =
      .error stopped (.poisoned, { before with image := reached }) :=
  runBatchWriteWithInterruption_stopped nonempty prepared fits guard _
    (publish_slotWriteInterrupted append syncWal writeSlot syncSlot install wrote walBarrier cut)

/-- A process stop at marker sync follows both WAL sync and the slot write,
but it cannot install the cached marker or return an acknowledgement. -/
theorem publish_markerSyncInterrupted {stop image : Type}
    (append syncWal writeSlot syncSlot install : ExceptT IO.Error (EStateM stop image) Unit)
    {before appended durable written reached : image} {stopped : stop}
    (wrote : append.run before = .ok (.ok ()) appended)
    (walBarrier : syncWal.run appended = .ok (.ok ()) durable)
    (slot : writeSlot.run durable = .ok (.ok ()) written)
    (cut : syncSlot.run written = .error stopped reached) :
    (publish append syncWal writeSlot syncSlot install).run before = .error stopped reached := by
  change append before = .ok (.ok ()) appended at wrote
  change syncWal appended = .ok (.ok ()) durable at walBarrier
  change writeSlot durable = .ok (.ok ()) written at slot
  change syncSlot written = .error stopped reached at cut
  simp [publish, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    wrote, walBarrier, slot, cut]

open OrderedTwoSlot

/-- An uncertain slot update selects the exact pre-write history or the
complete batch from the same reported WAL image. Bytes beyond either
accepted frontier do not enter the replay. -/
theorem uncertain_batch_selects_prefix
    {before after : Slots UInt64} {active : Slot} {old next : OrderedTwoSlot.Record UInt64}
    (report : Survivor before active next .slotWriteUncertain after)
    (present : before active = some old)
    (older : ∀ stale, before active.other = some stale → stale.epoch < old.epoch)
    (newer : old.epoch < next.epoch)
    (history batch : List WAL.Write) (physical : ByteArray)
    (oldCount : old.frontier = (WAL.encode history).size.toUInt64)
    (nextCount : next.frontier = (WAL.encode (history ++ batch)).size.toUInt64)
    (oldFits : (WAL.encode history).size < UInt64.size)
    (nextFits : (WAL.encode (history ++ batch)).size < UInt64.size)
    (oldBytes : ∃ tail, physical = WAL.encode history ++ tail)
    (nextBytes : after active.other = some next →
      ∃ tail, physical = WAL.encode (history ++ batch) ++ tail) :
    ∃ chosen events,
      recover (fun frontier => (Boundary.select frontier physical).isOk) after = .ok chosen ∧
      (events = history ∨ events = history ++ batch) ∧
      Boundary.select chosen.frontier physical = .ok (WAL.encode events) := by
  have readOld : Boundary.select old.frontier physical = .ok (WAL.encode history) := by
    obtain ⟨tail, exactBytes⟩ := oldBytes
    rw [oldCount, exactBytes]
    exact Boundary.select_encoded history tail oldFits
  have oldValid : (Boundary.select old.frontier physical).isOk = true := by
    simp [readOld, Except.isOk, Except.toBool]
  cases report with
  | uncertainOld =>
    exact ⟨old, history, recover_targetOld before active _ present oldValid older, .inl rfl, readOld⟩
  | uncertainInvalid =>
    exact ⟨old, history, recover_targetInvalid before active _ present oldValid, .inl rfl, readOld⟩
  | uncertainNew =>
    obtain ⟨tail, exactBytes⟩ := nextBytes (writeTarget_updatesOther ..)
    have readNext : Boundary.select next.frontier physical = .ok (WAL.encode (history ++ batch)) := by
      rw [nextCount, exactBytes]
      exact Boundary.select_encoded (history ++ batch) tail nextFits
    have selection := recover_targetNew before active
      (fun frontier => (Boundary.select frontier physical).isOk) present newer
    exact ⟨next, history ++ batch, by simpa [readNext, Except.isOk, Except.toBool] using selection,
      .inr rfl, readNext⟩

open Boundary (WalInodeImage)
open Storage.SyncHandleRouting (FsyncObservation)
open WalSegmentRepair (KeeperDescriptorIdentity)

private theorem completeFileSync_survivor {image reached : WalInodeImage}
    (state : reached = image.completeFileSync image.active)
    (binding : ∀ inode ∈ image.crashBindings, inode = image.active)
    {bytes : ByteArray} (survived : ∃ inode ∈ reached.crashBindings, bytes ∈ reached.crashBytes inode) :
    bytes = image.visible image.active := by
  obtain ⟨inode, bound, stored⟩ := survived
  have live := binding inode (by
    simpa [state, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync] using bound)
  simpa [state, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, live] using stored

private theorem syncedInode_survivor {image reached : WalInodeImage}
    {descriptor : KeeperDescriptorIdentity}
    (report : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      descriptor image (fun inode files => files.completeFileSync inode) (.ok () reached))
    (current : descriptor.inode = image.active)
    (binding : ∀ inode ∈ image.crashBindings, inode = image.active)
    {bytes : ByteArray} (survived : ∃ inode ∈ reached.crashBindings, bytes ∈ reached.crashBytes inode) :
    bytes = image.visible image.active := by
  have completed := report.effect.completed_of_return ⟨reached, rfl⟩
  have target := report.sameInode.trans current
  rw [target] at completed
  have state : reached = image.completeFileSync image.active := by injection completed
  exact completeFileSync_survivor state binding survived

/-- Any crash survivor of the routed, successful WAL barrier contains
the bytes flushed by the append, even if sync chose a pending handle. -/
theorem routedWalSync_survivor
    {cache resolved : SyncHandleRouting.Cache KeeperDescriptorIdentity}
    {directory keeper : System.FilePath}
    {bindings : System.FilePath → Option Nat}
    {openRead : System.FilePath → EStateM IO.Error WalInodeImage KeeperDescriptorIdentity}
    {appended durable : WalInodeImage} {file synced : KeeperDescriptorIdentity}
    (notDirectory : keeper ≠ directory)
    (active : cache.active = some (keeper, file))
    (owned : cache.Agrees directory KeeperDescriptorIdentity.inode bindings)
    (live : bindings keeper = some appended.active)
    (selected : cache.resolve directory keeper openRead appended = .ok synced (resolved, appended))
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      synced appended (fun inode files => files.completeFileSync inode) (.ok () durable))
    (binding : ∀ inode ∈ appended.crashBindings, inode = appended.active)
    {bytes : ByteArray} (survived : ∃ inode ∈ durable.crashBindings, bytes ∈ durable.crashBytes inode) :
    bytes = appended.visible file.inode := by
  obtain ⟨captured, _, lookup, same, _⟩ :=
    resolveAfterAppend_sameInode (openRead := openRead) (appended := appended)
      (bindings := fun _ => bindings) notDirectory active owned
  have sameHandle := (EStateM.Result.ok.inj (lookup.symm.trans selected)).1
  have appendInode := Option.some.inj ((owned.active active).symm.trans live)
  have syncInode := (congrArg KeeperDescriptorIdentity.inode sameHandle).symm.trans (same.trans appendInode)
  rw [appendInode]
  exact syncedInode_survivor sync syncInode binding survived

/-- A successful append followed by the cache-routed sync preserves
the appended inode's flushed bytes in every reported WAL crash survivor. -/
theorem appendThenSync_survivor
    (cache : SyncHandleRouting.Cache KeeperDescriptorIdentity) (before : WalInodeImage)
    (directory keeper : System.FilePath) (frame : ByteArray)
    (openAppend openRead : System.FilePath → EStateM IO.Error WalInodeImage KeeperDescriptorIdentity)
    (write : KeeperDescriptorIdentity → ByteArray → EStateM IO.Error WalInodeImage Unit)
    (flush fsync : KeeperDescriptorIdentity → EStateM IO.Error WalInodeImage Unit)
    (bindings : WalInodeImage → System.FilePath → Option Nat)
    {file : KeeperDescriptorIdentity} {opened written appended durable : WalInodeImage}
    (notDirectory : keeper ≠ directory)
    (owned : cache.Agrees directory KeeperDescriptorIdentity.inode (bindings before))
    (fresh : ∀ {captured after}, openAppend keeper before = .ok captured after →
      bindings after keeper = some captured.inode)
    (selected : SyncHandleRouting.selectAppendHandle cache.active openAppend keeper before = .ok file opened)
    (wrote : write file frame opened = .ok () written)
    (flushed : flush file written = .ok () appended)
    (bindingsPreserved : bindings appended = bindings before)
    (selectedPreserved : bindings appended keeper = bindings opened keeper)
    (live : bindings appended keeper = some appended.active)
    {returnedCache : SyncHandleRouting.Cache KeeperDescriptorIdentity}
    (returned : (SyncHandleRouting.runAppendWithCache keeper frame openAppend write flush >>= fun _ =>
      SyncHandleRouting.sync directory openRead fsync keeper) (cache, before) =
        .ok () (returnedCache, durable))
    (syncEffect : ∀ synced, fsync synced appended = .ok () durable →
      FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
        synced appended (fun inode files => files.completeFileSync inode) (.ok () durable))
    (binding : ∀ inode ∈ appended.crashBindings, inode = appended.active)
    {bytes : ByteArray} (survived : ∃ inode ∈ durable.crashBindings, bytes ∈ durable.crashBytes inode) :
    bytes = appended.visible file.inode := by
  obtain ⟨appendResult, activeOwned⟩ := SyncHandleRouting.runAppendWithCache_owned frame openAppend write flush
    bindings KeeperDescriptorIdentity.inode owned fresh selected wrote flushed bindingsPreserved selectedPreserved
  obtain ⟨synced, resolved, lookup, _, _⟩ :=
    resolveAfterAppend_sameInode (openRead := openRead) (appended := appended)
      (bindings := bindings) notDirectory rfl activeOwned
  simp only [Bind.bind, EStateM.bind, appendResult, SyncHandleRouting.sync, lookup] at returned
  have syncReturned : fsync synced appended = .ok () durable := by
    cases result : fsync synced appended <;>
      simp_all [SyncHandleRouting.withCache]
  exact routedWalSync_survivor notDirectory rfl activeOwned live lookup (syncEffect synced syncReturned)
    binding survived

/-- Interpret the successful positional write and sync on the single
handle selected by the publication schedule. The sync report is
indexed by that handle and the image reached by the write. -/
theorem writeSlotThenSync_survivor
    (handle : KeeperDescriptorIdentity) (next : Selection)
    (write : KeeperDescriptorIdentity → UInt64 → ByteArray → EStateM IO.Error WalInodeImage Unit)
    (sync : KeeperDescriptorIdentity → EStateM IO.Error WalInodeImage Unit)
    {before written durable : WalInodeImage}
    (wrote : write handle (next.slot * stride).toUInt64 next.encode before = .ok () written)
    (returned : ((write handle (next.slot * stride).toUInt64 next.encode >>= fun _ => sync handle)
      before) = .ok () durable)
    (syncEffect : sync handle written = .ok () durable →
      FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
        handle written (fun inode files => files.completeFileSync inode) (.ok () durable))
    (current : handle.inode = written.active)
    (binding : ∀ inode ∈ written.crashBindings, inode = handle.inode)
    {bytes : ByteArray} (survived : ∃ inode ∈ durable.crashBindings, bytes ∈ durable.crashBytes inode) :
    bytes = written.visible handle.inode := by
  simp only [Bind.bind, EStateM.bind, wrote] at returned
  rw [current]
  exact syncedInode_survivor (syncEffect returned) current
    (fun inode bound => (binding inode bound).trans current) survived

/-- An error after the marker file has reached durable storage does not
undo that effect. Every surviving binding to the marker inode reads the
complete successor, even though the write returned commit-unknown. -/
theorem markerSyncErrorAfter_selectsSuccessor
    {marker reached : WalInodeImage} {handle : KeeperDescriptorIdentity} {cause : IO.Error}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.error cause reached))
    (effective : sync.effective = true)
    (current : handle.inode = marker.active)
    (binding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {before bytes : ByteArray} {previous next : Selection}
    (history batch : List WAL.Write)
    (prior : decode before = .ok previous) (advanced : advance previous (WAL.encode (history ++ batch)).size = .ok next)
    (size : (marker.visible marker.active).size = containerSize)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        (marker.visible marker.active).get! position = before.get! position)
    (written : (marker.visible marker.active).extract (next.slot * stride) (next.slot * stride + 40) =
      next.encode)
    (survived : ∃ inode ∈ reached.crashBindings, bytes ∈ reached.crashBytes inode)
    {wal durable : WalInodeImage} {walHandle : KeeperDescriptorIdentity}
    (walSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      walHandle wal (fun inode files => files.completeFileSync inode) (.ok () durable))
    (walCurrent : walHandle.inode = wal.active)
    (walBinding : ∀ inode ∈ wal.crashBindings, inode = wal.active)
    {walBytes : ByteArray}
    (walSurvived : ∃ inode ∈ durable.crashBindings, walBytes ∈ durable.crashBytes inode)
    (appended : ∃ tail, wal.visible wal.active = WAL.encode (history ++ batch) ++ tail) :
    decode bytes = .ok next ∧
      Boundary.select next.frontier walBytes = .ok (WAL.encode (history ++ batch)) := by
  have effect := sync.effect
  rw [effective, sync.sameInode, current] at effect
  have state : reached = marker.completeFileSync marker.active := by
    cases effect
    rfl
  rw [completeFileSync_survivor state binding survived,
    syncedInode_survivor walSync walCurrent walBinding walSurvived]
  exact syncedBytes_selectBatch history batch prior advanced size unchanged written appended

/-- The no-follow stat and raw open on the held directory identify the
object whose bounded read selects the two-slot frontier. -/
theorem decode_markerFromHeldDirectory
    {reads : WalSegmentRepair.CheckpointRunChunkReads} {directory : DiskDirectory}
    {view : DiskSession.DirectoryReadNamespace} {root : DiskSession.DeviceInode}
    {payload : ByteArray}
    (file : DiskSession.HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload)
    (available : PrefixChunksAvailableUntilEof payload (reads.readChunk file.calls.slot.description)) :
    ∃ bytes, readPrefixUntilEofWith (IO.userError "invalid two-slot WAL marker length")
      (reads.readChunk file.calls.slot.description) acquisitionLimit ByteArray.empty 0 =
        .ok bytes (min acquisitionLimit payload.size) ∧ decode bytes = decode payload := by
  have object := congrArg view.modelObject (file.calls.openLookup.child_eq file.bound)
  have opened := object.symm.trans file.calls.identifiedOpen
  have contents : reads.objectBytes (file.calls.inventory.inode file.calls.slot.description) = some payload := by
    rw [← opened, file.contents]
  exact decode_heldRead _ (file.calls.observes payload contents) available
    (Nat.lt_of_lt_of_le (by decide) USize.le_size)

/-- The marker is opened read-write, then rewound on the same handle.
The bounded reader starts in the heap returned by the rewind, on that
same handle. Cursor reset is an effect of the rewind primitive. -/
theorem readMarkerAfterRewind_reports
    {heap handle : Type}
    (openReadWrite : EStateM IO.Error heap handle)
    (rewind : handle → EStateM IO.Error heap Unit)
    (readChunk : handle → USize → EStateM IO.Error heap ByteArray)
    {entry opened reached : heap} {marker : handle}
    (openedMarker : openReadWrite entry = .ok marker opened)
    (rewound : rewind marker opened = .ok () reached) :
    (do
      let marker ← openReadWrite
      let bytes ← readMarkerBytesWith (rewind marker) (readChunk marker)
      pure (marker, bytes)) entry =
      (do
        let bytes ← readPrefixUntilEofWith (IO.userError "invalid two-slot WAL marker length")
          (readChunk marker) acquisitionLimit ByteArray.empty
        pure (marker, bytes)) reached := by
  simp only [readMarkerBytesWith, Bind.bind, EStateM.bind, openedMarker, rewound]

/-- The shared native marker reader returns a failed rewind at the
reached heap before attempting any chunk read. -/
theorem readMarkerBytesWith_rewindError {heap : Type}
    (rewind : EStateM IO.Error heap Unit)
    (read : USize → EStateM IO.Error heap ByteArray)
    {before after : heap} {cause : IO.Error}
    (failed : rewind before = .error cause after) :
    readMarkerBytesWith rewind read before = .error cause after := by
  simp only [readMarkerBytesWith, Bind.bind, EStateM.bind, failed]

/-- After a reported rewind to zero, the shared native reader decodes
the bytes of the inode identified by the held marker open. -/
theorem readMarkerBytesWith_decodesHeldMarker
    {reads : WalSegmentRepair.CheckpointRunChunkReads} {directory : DiskDirectory}
    {view : DiskSession.DirectoryReadNamespace} {root : DiskSession.DeviceInode}
    {payload : ByteArray}
    (file : DiskSession.HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload)
    (available : PrefixChunksAvailableUntilEof payload (reads.readChunk file.calls.slot.description))
    (rewind : EStateM IO.Error Nat Unit) (cursor : Nat)
    (rewound : rewind cursor = .ok () 0) :
    ∃ bytes, readMarkerBytesWith rewind (reads.readChunk file.calls.slot.description) cursor =
        .ok bytes (min acquisitionLimit payload.size) ∧ decode bytes = decode payload := by
  simpa only [readMarkerBytesWith, Bind.bind, EStateM.bind, rewound] using
    decode_markerFromHeldDirectory file available

/-- The successful reopen barrier persists the same marker that the
bounded read observed. WAL repair may rely on this frontier for every
subsequent surviving marker binding to that inode. A pending directory
barrier can still allow the name to be absent. -/
theorem reopenSync_preservesReadFrontier
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {bytes survived : ByteArray} {selected : Selection}
    {read : USize → EStateM IO.Error Nat ByteArray} {reached : Nat}
    (mismatch : IO.Error)
    (observes : PrefixChunkObserves (marker.visible handle.inode) read)
    (available : PrefixChunksAvailableUntilEof (marker.visible handle.inode) read)
    (fits : acquisitionLimit < USize.size)
    (returned : readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes reached)
    (accepted : decode bytes = .ok selected)
    (survivor : ∃ inode ∈ settled.crashBindings, survived ∈ settled.crashBytes inode) :
    decode survived = .ok selected := by
  rw [syncedInode_survivor sync current sameBinding survivor, ← current]
  exact (decode_of_heldRead mismatch observes available fits returned).symm.trans accepted

/-- Project one directory crash choice from a completed marker sync.
A present name uses the bytes of its surviving inode, while an absent
name preserves the manifest and leaves the marker absent. -/
theorem reopenSync_projectsCrashBinding
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (completed : settled = marker.completeFileSync marker.active)
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} (observed : decode (marker.visible handle.inode) = .ok selected)
    (before : DirectoryPublication.Bindings) {survived : Option ByteArray}
    (presence : survived.isSome = before.walBoundary.isSome)
    (physical : ∀ bytes, survived = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    (match survived with
      | none => Except.ok (ε := String) (⟨before.manifest, none⟩ : DirectoryPublication.Bindings)
      | some bytes => projectBinding before bytes) =
      .ok ⟨before.manifest, before.walBoundary.map fun _ => Boundary.encode selected.frontier⟩ := by
  cases survived with
  | none =>
    cases boundary : before.walBoundary <;> simp_all
  | some bytes =>
    have exactBytes := completeFileSync_survivor completed sameBinding (physical bytes rfl)
    have decoded : decode bytes = .ok selected := by rw [exactBytes, ← current]; exact observed
    change projectBinding before bytes = _
    rw [projectBinding_decodes decoded]
    cases boundary : before.walBoundary <;> simp_all

/-- Map physical outcomes to the complete logical crash list after the
reopen barrier. The list preserves each manifest and marker-presence choice. -/
theorem reopenSync_projectsCrashBindings
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (completed : settled = marker.completeFileSync marker.active)
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} (observed : decode (marker.visible handle.inode) = .ok selected)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    choices.mapM (fun choice =>
      match choice.2 with
      | none => Except.ok (ε := String) (⟨choice.1.manifest, none⟩ : DirectoryPublication.Bindings)
      | some bytes => projectBinding choice.1 bytes) =
    .ok ((settleMarker ⟨⟨none, none⟩, choices.map Prod.fst, fun _ => none⟩ selected).crashImages) := by
  simp only [settleMarker, List.map_map]
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
    have head := reopenSync_projectsCrashBinding completed current sameBinding observed choice.1
      (presence choice (List.mem_cons_self ..)) (physical choice (List.mem_cons_self ..))
    have tail := ih (fun item member => presence item (List.mem_cons_of_mem _ member))
      (fun item member => physical item (List.mem_cons_of_mem _ member))
    simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Function.comp_def]

def projectRepairDirectory (directory : DirectoryPublication.Image) (visible : ByteArray)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray)) :
    Except String DirectoryPublication.Image := do
  let active ← projectBinding directory.active visible
  let crashImages ← choices.mapM fun (choice : DirectoryPublication.Bindings × Option ByteArray) =>
    match choice.2 with
    | none => Except.ok ⟨choice.1.manifest, none⟩
    | some payload => projectBinding choice.1 payload
  pure { directory with active, crashImages }

/-- A successful descriptor barrier yields the exact directory image
that precedes shared keeper repair. Staging is untouched by file sync. -/
theorem completedMarkerSync_projectsRepairDirectory
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (completed : settled = marker.completeFileSync marker.active)
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} (observed : decode (marker.visible handle.inode) = .ok selected)
    (directory : DirectoryPublication.Image)
    (bound : directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    projectRepairDirectory directory (marker.visible handle.inode) choices = .ok (settleMarker directory selected) := by
  have crashes := reopenSync_projectsCrashBindings completed current sameBinding observed choices presence physical
  have active := projectBinding_decodes (visible := directory.active) observed
  have activeMap : directory.active.walBoundary.map (fun _ => Boundary.encode selected.frontier) =
      some (Boundary.encode selected.frontier) := by
    cases boundary : directory.active.walBoundary <;> simp_all
  rw [enumerated] at crashes
  simp only [projectRepairDirectory, Bind.bind, Except.bind, active, crashes, Pure.pure, Except.pure]
  simp [settleMarker, activeMap]

/-- A successful syscall report witnesses the completed effect on the
active marker inode. The projection itself also applies to a sync that
completed before an error or interruption. -/
theorem reopenSync_projectsRepairDirectory
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} (observed : decode (marker.visible handle.inode) = .ok selected)
    (directory : DirectoryPublication.Image)
    (bound : directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    projectRepairDirectory directory (marker.visible handle.inode) choices = .ok (settleMarker directory selected) := by
  have effect := sync.effect.completed_of_return ⟨settled, rfl⟩
  rw [sync.sameInode, current] at effect
  have completed : settled = marker.completeFileSync marker.active := by injection effect
  exact completedMarkerSync_projectsRepairDirectory completed current sameBinding observed
    directory bound choices enumerated presence physical

/-- The repair directory follows from the successful bounded read and sync
of one held marker descriptor. No separate decode of its full bytes is needed. -/
theorem reopenSync_projectsAcquiredMarker
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} {bytes : ByteArray}
    {read : USize → EStateM IO.Error Nat ByteArray} {reached : Nat}
    (mismatch : IO.Error)
    (observes : PrefixChunkObserves (marker.visible handle.inode) read)
    (available : PrefixChunksAvailableUntilEof (marker.visible handle.inode) read)
    (fits : acquisitionLimit < USize.size)
    (returned : readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes reached)
    (accepted : decode bytes = .ok selected)
    (directory : DirectoryPublication.Image)
    (bound : directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    projectRepairDirectory directory (marker.visible handle.inode) choices = .ok (settleMarker directory selected) := by
  have physicalSelection :=
    (decode_of_heldRead mismatch observes available fits returned).symm.trans accepted
  exact reopenSync_projectsRepairDirectory sync current sameBinding physicalSelection
    directory bound choices enumerated presence physical

/-- A successful barrier on each held descriptor fixes the bytes used by
recovery. The marker encoding comes from the reported positional write;
the WAL prefix comes from the reported append on the selected keeper. -/
theorem syncedDescriptors_selectBatch
    {wal marker walSynced markerSynced : WalInodeImage}
    {walHandle markerHandle : KeeperDescriptorIdentity}
    (walSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      walHandle wal (fun inode files => files.completeFileSync inode) (.ok () walSynced))
    (markerSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      markerHandle marker (fun inode files => files.completeFileSync inode) (.ok () markerSynced))
    (walCurrent : walHandle.inode = wal.active) (markerCurrent : markerHandle.inode = marker.active)
    (walSettled : wal.crashBindings = [wal.active]) (markerSettled : marker.crashBindings = [marker.active])
    {walBytes markerBytes before : ByteArray} {current next : Selection}
    (walSurvived : ∃ inode ∈ walSynced.crashBindings, walBytes ∈ walSynced.crashBytes inode)
    (markerSurvived : ∃ inode ∈ markerSynced.crashBindings, markerBytes ∈ markerSynced.crashBytes inode)
    (history batch : List WAL.Write)
    (prior : decode before = .ok current)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (size : (marker.visible marker.active).size = containerSize)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        (marker.visible marker.active).get! position = before.get! position)
    (written : (marker.visible marker.active).extract (next.slot * stride) (next.slot * stride + 40) = next.encode)
    (appended : ∃ tail, wal.visible wal.active = WAL.encode (history ++ batch) ++ tail) :
    decode markerBytes = .ok next ∧
      Boundary.select next.frontier walBytes = .ok (WAL.encode (history ++ batch)) := by
  rw [syncedInode_survivor walSync walCurrent (by simp [walSettled]) walSurvived,
    syncedInode_survivor markerSync markerCurrent (by simp [markerSettled]) markerSurvived]
  exact syncedBytes_selectBatch history batch prior advanced size unchanged written appended

/-- Apply the filesystem contracts at the actual successful callback
states of a client acknowledgement. The crash-byte choices are taken
from the two inodes at the final installed state. -/
theorem acknowledgedWrite_selectBatch {α : Type}
    (nextTable : α) (sequence : UInt64) (phase : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install :
      EStateM IO.Error (WalInodeImage × WalInodeImage) Unit)
    {initial final : WalInodeImage × WalInodeImage}
    (returned : DiskSession.publishPreparedWrite nextTable sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (phase, initial) =
        .ok sequence (.ready nextTable, final))
    {walHandle markerHandle : KeeperDescriptorIdentity}
    (walReport : ∀ {before after}, syncWal before = .ok () after →
      FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
        walHandle before.1 (fun inode files => files.completeFileSync inode) (.ok () after.1))
    (markerReport : ∀ {before after}, syncSlot before = .ok () after →
      FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
        markerHandle before.2 (fun inode files => files.completeFileSync inode) (.ok () after.2))
    (slotKeepsWal : ∀ {before after}, writeSlot before = .ok () after → after.1 = before.1)
    (markerSyncKeepsWal : ∀ {before after}, syncSlot before = .ok () after → after.1 = before.1)
    (installKeepsFiles : ∀ {before after}, install before = .ok () after → after = before)
    (history batch : List WAL.Write) {before markerBytes walBytes : ByteArray} {current next : Selection}
    (prior : decode before = .ok current)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (appendReport : ∀ {after}, append initial = .ok () after →
      walHandle.inode = after.1.active ∧ after.1.crashBindings = [after.1.active] ∧
      ∃ tail, after.1.visible after.1.active = WAL.encode (history ++ batch) ++ tail)
    (slotReport : ∀ {beforeState after}, writeSlot beforeState = .ok () after →
      markerHandle.inode = after.2.active ∧ after.2.crashBindings = [after.2.active] ∧
      (after.2.visible after.2.active).size = containerSize ∧
      (∀ position,
        (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
          (after.2.visible after.2.active).get! position = before.get! position) ∧
      (after.2.visible after.2.active).extract (next.slot * stride) (next.slot * stride + 40) =
        next.encode)
    (walSurvived : ∃ inode ∈ final.1.crashBindings, walBytes ∈ final.1.crashBytes inode)
    (markerSurvived : ∃ inode ∈ final.2.crashBindings, markerBytes ∈ final.2.crashBytes inode) :
    decode markerBytes = .ok next ∧
      Boundary.select next.frontier walBytes = .ok (WAL.encode (history ++ batch)) := by
  obtain ⟨appended, walSynced, written, synced, wrote, walBarrier, slotWrite, slotBarrier, installed⟩ :=
    prepared_write_acknowledged nextTable sequence phase append syncWal writeSlot syncSlot install returned
  have finish := installKeepsFiles installed
  rw [finish, markerSyncKeepsWal slotBarrier, slotKeepsWal slotWrite] at walSurvived
  rw [finish] at markerSurvived
  obtain ⟨walCurrent, walSettled, appendedBytes⟩ := appendReport wrote
  obtain ⟨markerCurrent, markerSettled, size, unchanged, writtenBytes⟩ := slotReport slotWrite
  exact syncedDescriptors_selectBatch (walReport walBarrier) (markerReport slotBarrier)
    walCurrent markerCurrent walSettled markerSettled walSurvived markerSurvived history batch
    prior advanced size unchanged writtenBytes appendedBytes

/-- A successful short positional write advances the cursor by the
reported count. Every byte covered by that syscall is inside the target
record, and the next cursor still satisfies the original length bound.
An interrupted syscall that transfers no bytes leaves the cursor alone. -/
theorem slotWrite_cursor (active : Slot) {cursor remaining transferred : Nat}
    (length : cursor + remaining = 40)
    (reported : transferred ≤ remaining) :
    let start := slotIndex active.other * stride
    (∀ index < transferred, start ≤ start + cursor + index ∧
      start + cursor + index < start + 40) ∧
    (cursor + transferred) + (remaining - transferred) = 40 := by
  dsimp
  constructor
  · intro index inWrite
    constructor <;> omega
  · omega

/-- Each reported transfer advances the positional-write cursor by its
actual length. A zero-byte interruption has no addresses and no effect
on the cursor. The empty trace can end at either a return or a stop. -/
inductive SlotWriteTransfers (start : Nat) : Nat → List Nat → Nat → Prop where
  | done (cursor : Nat) : SlotWriteTransfers start cursor [] cursor
  | transfer {cursor count : Nat} {later : List Nat} {final : Nat}
      (fits : cursor + count ≤ 40)
      (rest : SlotWriteTransfers start (cursor + count) later final) :
      SlotWriteTransfers start cursor ((List.range count).map (fun index => start + cursor + index) ++ later) final

/-- Successfulpositional-write reports determine the reached cursor.
EINTR and terminal failures contribute no successful byte count. -/
theorem SlotWriteTransfers.ofCounts (start cursor : Nat) (counts : List Nat)
    (fits : cursor + counts.sum ≤ 40) :
    ∃ addresses, SlotWriteTransfers start cursor addresses (cursor + counts.sum) := by
  induction counts generalizing cursor with
  | nil =>
    exact ⟨[], by simpa using SlotWriteTransfers.done (start := start) cursor⟩
  | cons count counts ih =>
    simp only [List.sum_cons] at fits ⊢
    obtain ⟨later, transferred⟩ := ih (cursor + count) (by omega)
    exact ⟨_, SlotWriteTransfers.transfer (count := count) (by omega) (by simpa only [Nat.add_assoc] using transferred)⟩

/-- Consecutive transfers cover every address up to the reached cursor,
including when short or zero-byte transfers precede it. -/
theorem SlotWriteTransfers.coversPrefix {start cursor final : Nat} {addresses : List Nat}
    (trace : SlotWriteTransfers start cursor addresses final) (address : Nat) :
    address ∈ addresses ↔ start + cursor ≤ address ∧ address < start + final := by
  have movesForward {initialCursor endCursor : Nat} {written : List Nat}
      (steps : SlotWriteTransfers start initialCursor written endCursor) : initialCursor ≤ endCursor := by
    induction steps with
    | done => omega
    | transfer _ _ follows => omega
  induction trace with
  | done cursor => simp
  | @transfer cursor count later final fits rest ih =>
    have cursorLe := movesForward rest
    simp only [List.mem_append, ih, List.mem_map]
    constructor
    · rintro (⟨index, member, rfl⟩ | after)
      · have within := List.mem_range.mp member
        omega
      · omega
    · intro within
      by_cases first : address < start + (cursor + count)
      · left
        refine ⟨address - (start + cursor), List.mem_range.mpr ?_, ?_⟩ <;> omega
      · exact .inr (by omega)

/-- The whole short-write loop stays within the inactive record, including
any prefix left by a process stop. This bounds syscall transfers. The
separate filesystem contract describes the bytes surviving a power loss. -/
theorem SlotWriteTransfers.inactiveRecord {current next : Selection} {frontier : Nat} {active : Slot}
    (offset : current.slot = slotIndex active) (advanced : advance current frontier = .ok next)
    {addresses : List Nat} {final : Nat}
    (transferred : SlotWriteTransfers (next.slot * stride) 0 addresses final) :
    final ≤ 40 ∧ ∀ address ∈ addresses,
      slotIndex active.other * stride ≤ address ∧ address < slotIndex active.other * stride + 40 := by
  have nextSlot : next.slot = slotIndex active.other := by
    rw [(advance_fields advanced).1, offset]
    cases active <;> rfl
  rw [nextSlot] at transferred
  have bounded {cursor endCursor : Nat} {written : List Nat}
      (trace : SlotWriteTransfers (slotIndex active.other * stride) cursor written endCursor)
      (within : cursor ≤ 40) :
      endCursor ≤ 40 ∧ ∀ address ∈ written,
        slotIndex active.other * stride ≤ address ∧ address < slotIndex active.other * stride + 40 := by
    induction trace with
    | done cursor => exact ⟨within, by simp⟩
    | @transfer cursor count later final fits rest ih =>
      obtain ⟨finalBound, remaining⟩ := ih fits
      refine ⟨finalBound, fun address member => ?_⟩
      rcases List.mem_append.mp member with first | later
      · obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp first
        exact (slotWrite_cursor active (cursor := cursor) (remaining := 40 - cursor)
          (transferred := count) (by omega) (by omega)).1 index (List.mem_range.mp inRange)
      · exact remaining address later
  exact bounded transferred (by decide)

/-- Filesystem contract for one surviving marker container after an
interrupted positional write to its inactive record. -/
def InterruptedSlotBytes (before bytes : ByteArray) (active : Slot) (next : Selection) : Prop :=
  bytes.size = containerSize ∧
    (∀ position,
      (position < slotIndex active.other * stride ∨ slotIndex active.other * stride + 40 ≤ position) →
        bytes.get! position = before.get! position) ∧
    (decodeSlot bytes (slotIndex active.other) = decodeSlot before (slotIndex active.other) ∨
      decodeSlot bytes (slotIndex active.other) = none ∨
      decodeSlot bytes (slotIndex active.other) = some next)

/-- If each changed byte in a surviving container lies in the reported
transfer trace, filesystem isolation reduces to the proven syscall
address bound. The report must include any effect of the in-flight
write, and separately constrain the decoding of the torn record. -/
theorem SlotWriteTransfers.interruptedBytes
    {current next : Selection} {frontier : Nat} {active : Slot}
    (offset : current.slot = slotIndex active) (advanced : advance current frontier = .ok next)
    {addresses : List Nat} {final : Nat}
    (transferred : SlotWriteTransfers (next.slot * stride) 0 addresses final)
    {before bytes : ByteArray} (size : bytes.size = containerSize)
    (attributed : ∀ position, bytes.get! position ≠ before.get! position → position ∈ addresses)
    (decoded : decodeSlot bytes (slotIndex active.other) = decodeSlot before (slotIndex active.other) ∨
      decodeSlot bytes (slotIndex active.other) = none ∨ decodeSlot bytes (slotIndex active.other) = some next) :
    InterruptedSlotBytes before bytes active next := by
  refine ⟨size, ?_, decoded⟩
  intro position outside
  by_cases same : bytes.get! position = before.get! position
  · exact same
  · have inside := (transferred.inactiveRecord offset advanced).2 position (attributed position same)
    omega

/-- After the successful WAL barrier, any marker bytes surviving an
interrupted positional write on the live marker can expose only the
previous history or the whole newly durable batch. The slot isolation
and decode alternatives apply to the surviving bytes of that inode. -/
theorem interruptedDescriptors_selectBatch
    {wal walSynced marker : WalInodeImage}
    {walHandle markerHandle : KeeperDescriptorIdentity}
    (walSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      walHandle wal (fun inode files => files.completeFileSync inode) (.ok () walSynced))
    (walCurrent : walHandle.inode = wal.active) (markerCurrent : markerHandle.inode = marker.active)
    (walSettled : wal.crashBindings = [wal.active]) (markerSettled : marker.crashBindings = [marker.active])
    {walBytes markerBytes before : ByteArray} {active : Slot} {current next : Selection}
    (walSurvived : ∃ inode ∈ walSynced.crashBindings, walBytes ∈ walSynced.crashBytes inode)
    (markerSurvived : ∃ inode ∈ marker.crashBindings, markerBytes ∈ marker.crashBytes inode)
    {history batch : List WAL.Write}
    (prior : decode before = .ok current)
    (activeOffset : current.slot = slotIndex active)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (slotOutcome : ∀ bytes ∈ marker.crashBytes markerHandle.inode,
      InterruptedSlotBytes before bytes active next)
    (oldCount : current.frontier.toNat = (WAL.encode history).size)
    (appended : ∃ tail, wal.visible wal.active = WAL.encode (history ++ batch) ++ tail) :
    ∃ chosen events, decode markerBytes = .ok chosen ∧
      (events = history ∨ events = history ++ batch) ∧
      Boundary.select chosen.frontier walBytes = .ok (WAL.encode events) := by
  obtain ⟨inode, bound, survived⟩ := markerSurvived
  have live : inode = markerHandle.inode := by
    simpa [markerSettled, markerCurrent] using bound
  obtain ⟨size, unchanged, target⟩ := slotOutcome markerBytes (live ▸ survived)
  rw [syncedInode_survivor walSync walCurrent (by simp [walSettled]) walSurvived]
  exact interruptedBytes_selectBatch prior activeOffset advanced size unchanged target oldCount appended

/-- A returned slot-write or marker-sync failure leaves the poisoned session and the
exact crash candidates from the reached files. The previous successful
WAL barrier suffices for either complete marker outcome. -/
theorem markerError_selectBatch {α : Type}
    (nextTable : α) (sequence : UInt64) (phase : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error (WalInodeImage × WalInodeImage) Unit)
    {initial appended durable reached : WalInodeImage × WalInodeImage} {cause : IO.Error}
    (wrote : append initial = .ok () appended)
    (walBarrier : syncWal appended = .ok () durable)
    (failed : writeSlot durable = .error cause reached ∨
      ∃ written, writeSlot durable = .ok () written ∧ syncSlot written = .error cause reached)
    (walUnchanged : reached.1 = durable.1)
    {walHandle markerHandle : KeeperDescriptorIdentity}
    (walSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      walHandle appended.1 (fun inode files => files.completeFileSync inode) (.ok () durable.1))
    (walCurrent : walHandle.inode = appended.1.active)
    (markerCurrent : markerHandle.inode = reached.2.active)
    (walSettled : appended.1.crashBindings = [appended.1.active])
    (markerSettled : reached.2.crashBindings = [reached.2.active])
    {walBytes markerBytes before : ByteArray} {active : Slot} {current next : Selection}
    (walSurvived : ∃ inode ∈ reached.1.crashBindings, walBytes ∈ reached.1.crashBytes inode)
    (markerSurvived : ∃ inode ∈ reached.2.crashBindings, markerBytes ∈ reached.2.crashBytes inode)
    {history batch : List WAL.Write}
    (prior : decode before = .ok current)
    (activeOffset : current.slot = slotIndex active)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (completedCounts : List Nat) (transfersFit : completedCounts.sum ≤ 40)
    (slotOutcome : ∀ bytes ∈ reached.2.crashBytes markerHandle.inode,
      bytes.size = containerSize ∧
      (∀ position, bytes.get! position ≠ before.get! position →
        next.slot * stride ≤ position ∧ position < next.slot * stride + completedCounts.sum) ∧
      (decodeSlot bytes (slotIndex active.other) = decodeSlot before (slotIndex active.other) ∨
        decodeSlot bytes (slotIndex active.other) = none ∨
        decodeSlot bytes (slotIndex active.other) = some next))
    (oldCount : current.frontier.toNat = (WAL.encode history).size)
    (appendedBytes : ∃ tail, appended.1.visible appended.1.active = WAL.encode (history ++ batch) ++ tail) :
    DiskSession.publishPreparedWrite nextTable sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (phase, initial) =
        .error (.commitUnknown cause) (.poisoned, reached) ∧
    ∃ chosen events, decode markerBytes = .ok chosen ∧
      (events = history ∨ events = history ++ batch) ∧
      Boundary.select chosen.frontier walBytes = .ok (WAL.encode events) := by
  refine ⟨prepared_write_markerError nextTable sequence phase append syncWal writeSlot syncSlot install
    wrote walBarrier failed, ?_⟩
  rw [walUnchanged] at walSurvived
  refine interruptedDescriptors_selectBatch walSync walCurrent markerCurrent walSettled markerSettled
    walSurvived markerSurvived prior activeOffset advanced ?_ oldCount appendedBytes
  obtain ⟨_, transfers⟩ := SlotWriteTransfers.ofCounts (next.slot * stride) 0 completedCounts
    (by simpa using transfersFit)
  simp only [Nat.zero_add] at transfers
  intro bytes survives
  obtain ⟨size, changed, decoded⟩ := slotOutcome bytes survives
  apply transfers.interruptedBytes activeOffset advanced size _ decoded
  intro position differs
  exact (transfers.coversPrefix position).mpr (by simpa using changed position differs)

/-- Before the schedule issues a marker write, append and WAL sync
may leave different suffixes on disk, but the previous durable frontier
selects exactly the previously acknowledged history. -/
theorem beforeSlotWrite_selectHistory
    {marker wal : WalInodeImage} {markerHandle walHandle : KeeperDescriptorIdentity}
    (markerCurrent : markerHandle.inode = marker.active) (walCurrent : walHandle.inode = wal.active)
    (markerSettled : marker.crashBindings = [marker.active]) (walSettled : wal.crashBindings = [wal.active])
    {before markerBytes walBytes : ByteArray} {current : Selection} (history : List WAL.Write)
    (prior : decode before = .ok current)
    (oldCount : current.frontier.toNat = (WAL.encode history).size)
    (markerUnchanged : marker.crashBytes markerHandle.inode = [before])
    (walPrefix : ∀ bytes ∈ wal.crashBytes walHandle.inode,
      ∃ tail, bytes = WAL.encode history ++ tail)
    (markerSurvived : ∃ inode ∈ marker.crashBindings, markerBytes ∈ marker.crashBytes inode)
    (walSurvived : ∃ inode ∈ wal.crashBindings, walBytes ∈ wal.crashBytes inode) :
    decode markerBytes = .ok current ∧
      Boundary.select current.frontier walBytes = .ok (WAL.encode history) := by
  obtain ⟨markerInode, markerBound, markerStored⟩ := markerSurvived
  obtain ⟨walInode, walBound, walStored⟩ := walSurvived
  have markerLive : markerInode = markerHandle.inode := by
    simpa [markerSettled, markerCurrent] using markerBound
  have walLive : walInode = walHandle.inode := by
    simpa [walSettled, walCurrent] using walBound
  rw [markerLive, markerUnchanged, List.mem_singleton] at markerStored
  obtain ⟨tail, rfl⟩ := walPrefix walBytes (walLive ▸ walStored)
  refine ⟨markerStored ▸ prior, ?_⟩
  have fits : (WAL.encode history).size < UInt64.size := by
    rw [← oldCount]
    exact current.frontier.toNat_lt
  have count : current.frontier = (WAL.encode history).size.toUInt64 := by
    rw [← oldCount]
    simp
  rw [count]
  exact Boundary.select_encoded history tail fits

/-- A returned append or WAL-sync error preserves the old frontier.
The reached WAL can contain extra durable bytes, but the marker still
selects only the prior history. -/
theorem walError_selectHistory {α : Type}
    (nextTable : α) (sequence : UInt64) (phase : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error (WalInodeImage × WalInodeImage) Unit)
    {initial reached : WalInodeImage × WalInodeImage} {cause : IO.Error}
    (failed : append initial = .error cause reached ∨
      ∃ appended, append initial = .ok () appended ∧ syncWal appended = .error cause reached)
    (markerUnchanged : reached.2 = initial.2)
    {markerHandle walHandle : KeeperDescriptorIdentity}
    (markerCurrent : markerHandle.inode = initial.2.active) (walCurrent : walHandle.inode = reached.1.active)
    (markerSettled : initial.2.crashBindings = [initial.2.active])
    (walSettled : reached.1.crashBindings = [reached.1.active])
    {before markerBytes walBytes : ByteArray} {current : Selection} (history : List WAL.Write)
    (prior : decode before = .ok current)
    (oldCount : current.frontier.toNat = (WAL.encode history).size)
    (markerBytesBefore : initial.2.crashBytes markerHandle.inode = [before])
    (walPrefix : ∀ bytes ∈ reached.1.crashBytes walHandle.inode,
      ∃ tail, bytes = WAL.encode history ++ tail)
    (markerSurvived : ∃ inode ∈ reached.2.crashBindings, markerBytes ∈ reached.2.crashBytes inode)
    (walSurvived : ∃ inode ∈ reached.1.crashBindings, walBytes ∈ reached.1.crashBytes inode) :
    DiskSession.publishPreparedWrite nextTable sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (phase, initial) =
        .error (.commitUnknown cause) (.poisoned, reached) ∧
    decode markerBytes = .ok current ∧
    Boundary.select current.frontier walBytes = .ok (WAL.encode history) := by
  refine ⟨prepared_write_walError nextTable sequence phase append syncWal writeSlot syncSlot install failed, ?_⟩
  rw [markerUnchanged] at markerSurvived
  exact beforeSlotWrite_selectHistory markerCurrent walCurrent markerSettled walSettled
    history prior oldCount markerBytesBefore walPrefix markerSurvived walSurvived

open DiskSession (DatabaseSubmissions DatabaseBatchRetention)

private theorem recoveredFrontier_count {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history : List Write} {base table : PackedTable} {first : Nat}
    (recovery : WalSegmentRecovery image pair range history base first table)
    {frontier : UInt64} (selected : pair.walBoundary = some (Boundary.encode frontier)) :
    frontier.toNat = range.through * frameSize := by
  obtain ⟨marker, length, _, read, decoded, bytes, _⟩ := recovery.marked
  have sameMarker := Option.some.inj (selected.symm.trans read)
  have sameLength : frontier = length :=
    Except.ok.inj ((Boundary.decode_encode frontier).symm.trans (sameMarker ▸ decoded))
  exact sameLength ▸ bytes

private theorem recoveredBatch_history {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {frontier : UInt64} (selected : pair.walBoundary = some (Boundary.encode frontier))
    (whole : frontier.toNat = (WAL.encode history).size ∨
      frontier.toNat = (WAL.encode (history ++ batch)).size) :
    (history ++ batch).take range.through = history ∨
      (history ++ batch).take range.through = history ++ batch := by
  have count : range.through = history.length ∨ range.through = (history ++ batch).length := by
    rw [recoveredFrontier_count recovery selected, WAL.encode_size, WAL.encode_size] at whole
    unfold frameSize at whole
    omega
  rcases count with old | all
  · exact .inl (by rw [old, List.take_append_of_le_length (Nat.le_refl _), List.take_length])
  · exact .inr (all.symm ▸ List.take_length)

/-- The client ledger accounts for a recovered uncertain submission as
one whole batch or no batch. The retained history is exactly the prefix
represented by the recovered table. -/
theorem recoveredBatch_retains {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    {log : List DatabaseSubmissions} (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {frontier : UInt64} (selected : pair.walBoundary = some (Boundary.encode frontier))
    (whole : frontier.toNat = (WAL.encode history).size ∨
      frontier.toNat = (WAL.encode (history ++ batch)).size) :
    DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
    ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model := by
  refine ⟨?_, recovery.refines⟩
  rcases recoveredBatch_history recovery selected whole with old | all
  · rw [old]
    simpa using (DatabaseBatchRetention.append (entry := .uncertainBatch batch)
      (suffix := []) prior (Or.inl rfl))
  · rw [all]
    exact DatabaseBatchRetention.append (entry := .uncertainBatch batch) prior (Or.inr rfl)

/-- Connect the observed commit-unknown return to the recovered client
ledger. The filesystem reports for the reached stage bound the selected
frontier, and the common segmented proof accounts for that exact batch. -/
theorem commitUnknown_retainsBatch {α σ : Type}
    (next : α) (sequence : UInt64) (phase : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files reached : σ} {cause : IO.Error}
    (installOk : ∀ state, ∃ installed, install state = .ok () installed)
    (returned : DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (phase, files) =
        .error (.commitUnknown cause) (.poisoned, reached))
    {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    {log : List DatabaseSubmissions} (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {frontier : UInt64} (bound : pair.walBoundary = some (Boundary.encode frontier))
    (early : (append files = .error cause reached ∨
      ∃ appended, append files = .ok () appended ∧ syncWal appended = .error cause reached) →
        frontier.toNat = (WAL.encode history).size)
    (late : ∀ appended durable, append files = .ok () appended →
      syncWal appended = .ok () durable →
      (writeSlot durable = .error cause reached ∨
        ∃ written, writeSlot durable = .ok () written ∧ syncSlot written = .error cause reached) →
      frontier.toNat = (WAL.encode history).size ∨ frontier.toNat = (WAL.encode (history ++ batch)).size) :
    DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
    ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model := by
  apply recoveredBatch_retains prior recovery bound
  rcases prepared_write_errorStage next sequence phase append syncWal writeSlot syncSlot install
      installOk returned with failed | ⟨appended, durable, wrote, synced, failed⟩
  · exact .inl (early failed)
  · exact late appended durable wrote synced failed

/-- Acknowledged publication has a single retained history, containing the
whole submitted batch after all earlier retained writes. -/
theorem recoveredAcknowledgedBatch_retains {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    {log : List DatabaseSubmissions} (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {frontier : UInt64} (selected : pair.walBoundary = some (Boundary.encode frontier))
    (complete : frontier.toNat = (WAL.encode (history ++ batch)).size) :
    DatabaseBatchRetention (log ++ [.acknowledgedBatch batch]) (history ++ batch) ∧
    ∃ model, table.Refines model ∧ RepresentsWalHistory (history ++ batch) model := by
  have count : range.through = (history ++ batch).length := by
    rw [recoveredFrontier_count recovery selected, WAL.encode_size] at complete
    unfold frameSize at complete
    omega
  refine ⟨DatabaseBatchRetention.append (entry := .acknowledgedBatch batch) prior rfl, ?_⟩
  simpa only [count, List.take_length] using recovery.refines

/-- Carry a successful publication through recovery of its reported
durable frontier into the acknowledged client ledger. -/
theorem acknowledgedReturn_retainsBatch {α σ : Type}
    (nextTable : α) (sequence : UInt64) (phase : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files reached : σ}
    (returned : DiskSession.publishPreparedWrite nextTable sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (phase, files) =
        .ok sequence (.ready nextTable, reached))
    {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    {log : List DatabaseSubmissions} (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {frontier : UInt64} (bound : pair.walBoundary = some (Boundary.encode frontier))
    (durable : ∀ appended walSynced written slotSynced,
      append files = .ok () appended → syncWal appended = .ok () walSynced →
      writeSlot walSynced = .ok () written → syncSlot written = .ok () slotSynced →
      install slotSynced = .ok () reached →
      frontier.toNat = (WAL.encode (history ++ batch)).size) :
    DatabaseBatchRetention (log ++ [.acknowledgedBatch batch]) (history ++ batch) ∧
    ∃ model, table.Refines model ∧ RepresentsWalHistory (history ++ batch) model := by
  obtain ⟨appended, walSynced, written, slotSynced, wrote, walBarrier, slotWrite, markerBarrier, installed⟩ :=
    prepared_write_acknowledged nextTable sequence phase append syncWal writeSlot syncSlot install returned
  exact recoveredAcknowledgedBatch_retains prior recovery bound
    (durable appended walSynced written slotSynced wrote walBarrier slotWrite markerBarrier installed)

/-- A reached slot survivor determines the history retained by the
segmented recovery of that same decoded marker. Only a synced slot can
account for an acknowledged batch. -/
theorem recoveredSlot_retains {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch : List Write} {base table : PackedTable} {first : Nat}
    {log : List DatabaseSubmissions} (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {before after : ByteArray} {active : OrderedTwoSlot.Slot}
    {current : Selection} {next : OrderedTwoSlot.Record UInt64} {phase : OrderedTwoSlot.Phase} {decoded : Selection}
    (report : OrderedTwoSlot.Survivor (decodedSlots before) active next phase (decodedSlots after))
    (currentDecode : decode before = .ok current)
    (activeOffset : current.slot = slotIndex active)
    (newer : current.toRecord.epoch < next.epoch)
    (oldSize : current.frontier.toNat = (WAL.encode history).size)
    (nextSize : next.frontier.toNat = (WAL.encode (history ++ batch)).size)
    (accepted : decode after = .ok decoded)
    (selected : pair.walBoundary = some (Boundary.encode decoded.frontier))
    (acknowledged : Bool) (afterSync : acknowledged = true → phase = .slotSynced) :
    if acknowledged then
      DatabaseBatchRetention (log ++ [.acknowledgedBatch batch]) (history ++ batch) ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory (history ++ batch) model
    else
      DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model := by
  obtain ⟨present, older⟩ := decodedSlots_active currentDecode active activeOffset
  have frontier := decodedMarker_of_survivor report present older newer accepted
  cases acknowledged with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases phase with
    | beforeWalSync | beforeSlotWrite =>
      exact recoveredBatch_retains prior recovery selected (.inl (frontier ▸ oldSize))
    | slotWriteUncertain =>
      change decoded.frontier = current.frontier ∨ decoded.frontier = next.frontier at frontier
      rcases frontier with oldFrontier | nextFrontier
      · exact recoveredBatch_retains prior recovery selected (.inl (oldFrontier ▸ oldSize))
      · exact recoveredBatch_retains prior recovery selected (.inr (nextFrontier ▸ nextSize))
    | slotSynced =>
      exact recoveredBatch_retains prior recovery selected (.inr (frontier ▸ nextSize))
  | true =>
    have synced := afterSync rfl
    subst phase
    exact recoveredAcknowledgedBatch_retains prior recovery selected (frontier ▸ nextSize)

/-- Compose the selected physical WAL prefix with the segmentation proof
for the same marker projection. An observed acknowledgement requires the
full-batch selection, while an uncertain return admits either prefix. -/
theorem selectedBytes_retainBatch
    {image : WalSegmentImage} {directory pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history batch events : List Write}
    {base table : PackedTable} {first : Nat} {log : List DatabaseSubmissions}
    (prior : DatabaseBatchRetention log history)
    (recovery : WalSegmentRecovery image pair range (history ++ batch) base first table)
    {marker bytes wal : ByteArray} {decoded : Selection}
    {read : USize → EStateM IO.Error Nat ByteArray} {reached : Nat}
    (mismatch : IO.Error) (observes : PrefixChunkObserves marker read)
    (available : PrefixChunksAvailableUntilEof marker read)
    (fits : acquisitionLimit < USize.size)
    (returned : readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes reached)
    (accepted : decode bytes = .ok decoded)
    (projected : projectBinding directory marker = .ok pair)
    (selected : Boundary.select decoded.frontier wal = .ok (WAL.encode events))
    (whole : events = history ∨ events = history ++ batch)
    (acknowledged : Bool) (confirmed : acknowledged = true → events = history ++ batch) :
    Boundary.recoverMarked base decoded.frontier wal = .ok (WAL.encode events, table) ∧
    Boundary.recoverRetainedMarked base first decoded.frontier
      (WalSegment.concatenate (image.afterWatermark range.watermark)) =
        .ok (WAL.encode (events.drop first), table) ∧
    (if acknowledged then
      DatabaseBatchRetention (log ++ [.acknowledgedBatch batch]) (history ++ batch) ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory (history ++ batch) model
    else
      DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model) := by
  have projection := projectBinding_of_heldRead (visible := directory)
    mismatch observes available fits returned accepted
  have samePair := Except.ok.inj (projected.symm.trans projection)
  have binding : pair.walBoundary = some (Boundary.encode decoded.frontier) :=
    congrArg DirectoryPublication.Bindings.walBoundary samePair
  have count := (Boundary.select_size selected).symm
  have fits : (WAL.encode events).size < UInt64.size := by
    rw [← count]
    exact decoded.frontier.toNat_lt
  have frontier : decoded.frontier = (WAL.encode events).size.toUInt64 := by
    rw [← count]
    simp
  have canonical : Boundary.select decoded.frontier (WAL.encode (history ++ batch)) =
      .ok (WAL.encode events) := by
    rw [frontier]
    rcases whole with old | new
    · rw [old, WAL.encode_append]
      exact Boundary.select_encoded history (WAL.encode batch) (old ▸ fits)
    · rw [new]
      simpa using Boundary.select_encoded (history ++ batch) ByteArray.empty (new ▸ fits)
  obtain ⟨markerRecord, length, retained, readMarker, parsed, byteCount, retainedBytes, replayRetained, recovered⟩ := recovery.marked
  have sameRecord := Option.some.inj (binding.symm.trans readMarker)
  have sameLength : decoded.frontier = length :=
    Except.ok.inj ((Boundary.decode_encode decoded.frontier).symm.trans (sameRecord ▸ parsed))
  have exactReplay : Boundary.recoverMarked base decoded.frontier wal =
      .ok (WAL.encode events, table) := by
    rw [← sameLength] at recovered
    simp only [Boundary.recoverMarked, Bind.bind, Except.bind, selected, canonical] at recovered ⊢
    cases replay : recoverSelected base (WAL.encode events) <;> simp_all [Pure.pure, Except.pure]
  have exactCount : range.through = events.length := by
    rw [← sameLength, count, WAL.encode_size] at byteCount
    unfold frameSize at byteCount
    omega
  have exactHistory : (history ++ batch).take range.through = events := by
    rw [exactCount]
    rcases whole with old | new
    · rw [old, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    · rw [new, List.take_length]
  rw [← sameLength, retainedBytes, exactHistory] at replayRetained
  refine ⟨exactReplay, replayRetained, ?_⟩
  cases acknowledged with
  | false =>
    apply recoveredBatch_retains prior recovery binding
    rcases whole with old | new
    · exact .inl (old ▸ count)
    · exact .inr (new ▸ count)
  | true =>
    exact recoveredAcknowledgedBatch_retains prior recovery binding (confirmed rfl ▸ count)

open WalSegmentRepair (FileImage Target EffectTrace)

/-- Every admitted repair cut preserves the frontier derived from the
same descriptor barrier and physical directory choices. -/
theorem reopenSync_repairPreservesFrontier
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
    (current : handle.inode = marker.active)
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selected : Selection} (observed : decode (marker.visible handle.inode) = .ok selected)
    {initial after : FileImage} {directory : DirectoryPublication.Image} {target : Target}
    {plan : WalSegmentRepair.Plan}
    (prepared : WalSegmentRepair.Prepared initial target plan)
    (bound : initial.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = initial.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ payload, choice.2 = some payload →
      ∃ inode ∈ settled.crashBindings, payload ∈ settled.crashBytes inode)
    (projected : projectRepairDirectory initial.directory (marker.visible handle.inode) choices = .ok directory)
    (trace : EffectTrace target { initial with directory := directory } after)
    {survivor : DirectoryPublication.Bindings}
    (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have projectedSync := reopenSync_projectsRepairDirectory sync current sameBinding observed
    initial.directory (by simp [bound]) choices enumerated presence physical
  have same := Except.ok.inj (projected.symm.trans projectedSync)
  subst directory
  have authorized := prepared_settleMarker prepared selected bound
  exact repair_preserves_settledMarker initial selected bound trace authorized.pair
    authorized.keeperPrefix authorized.newer chosen

/-- File observations before directory authorization. The marker sync
reports its effect on the held inode. A power loss names the survivors
of that exact reached file image. -/
inductive ReportedMarkerRetries (initial : FileImage) : FileImage → Prop where
  | start : ReportedMarkerRetries initial initial
  | markerSync {before : FileImage} (prior : ReportedMarkerRetries initial before)
      {physical : WalInodeImage} {handle : KeeperDescriptorIdentity} {returned}
      (report : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
        handle physical (fun inode files => files.completeFileSync inode) returned)
      (project : WalInodeImage → FileImage) (source : project physical = before)
      (selection : Selection)
      (observed : before.directory.active.walBoundary = some (Boundary.encode selection.frontier))
      (persisted : project (physical.completeFileSync handle.inode) =
        { before with directory := settleMarker before.directory selection }) :
      ReportedMarkerRetries initial (match returned with
        | .ok _ after | .error _ after => project after)
  | markerInterrupted {before reached : FileImage} (prior : ReportedMarkerRetries initial before)
      (selection : Selection)
      (observed : before.directory.active.walBoundary = some (Boundary.encode selection.frontier))
      (effect : reached = before ∨ reached = { before with directory := settleMarker before.directory selection }) :
      ReportedMarkerRetries initial reached
  | powerLoss {before : FileImage} (prior : ReportedMarkerRetries initial before)
      {pair bytes names}
      (metadata : pair ∈ before.directory.crashImages)
      (payload : bytes ∈ before.keeper.crashImages) (later : names ∈ before.later.crashImages) :
      ReportedMarkerRetries initial (before.crash pair bytes names)

/-- Prepend an observed crash or failed open to a later retry trace. -/
theorem ReportedMarkerRetries.trans {initial middle final : FileImage}
    (earlier : ReportedMarkerRetries initial middle)
    (suffix : ReportedMarkerRetries middle final) : ReportedMarkerRetries initial final := by
  induction suffix with
  | start => exact earlier
  | markerSync _ report project source selection observed persisted ih =>
    exact .markerSync ih report project source selection observed persisted
  | markerInterrupted _ selection observed effect ih =>
    exact .markerInterrupted ih selection observed effect
  | powerLoss _ metadata keeper later ih => exact .powerLoss ih metadata keeper later

theorem ReportedMarkerRetries.refines {initial after : FileImage}
    (reported : ReportedMarkerRetries initial after) : UnsettledRetries initial after := by
  induction reported with
  | start => exact .start
  | markerSync _ report project source selection observed persisted ih =>
    have effect := report.effect
    rw [report.sameInode] at effect
    generalize report.effective = effective at effect
    cases effect with
    | completed => exact cast (congrArg (UnsettledRetries initial) persisted.symm) (ih.settle selection observed)
    | errorBefore => exact cast (congrArg (UnsettledRetries initial) source.symm) ih
    | errorAfter => exact cast (congrArg (UnsettledRetries initial) persisted.symm) (ih.settle selection observed)
  | markerInterrupted _ selection observed effect ih =>
    rcases effect with rfl | rfl
    · exact ih
    · exact ih.settle selection observed
  | powerLoss _ metadata payload later ih => exact ih.crash metadata payload later

/-- Run the marker sync with its physical image and the reached recovery
state together. The continuation uses the recovery state returned by
that very call, on either success or error. -/
def projectMarkerSync {failure state result : Type}
    (sync : KeeperDescriptorIdentity →
      EStateM failure (WalInodeImage × state) result)
    (marker : WalInodeImage) (handle : KeeperDescriptorIdentity) :
    EStateM failure state result :=
  fun reached =>
    match sync handle (marker, reached) with
    | .ok value (_, after) => .ok value after
    | .error cause (_, after) => .error cause after

/-- A machine stop during the reopen barrier never enters WAL repair.
Whether the marker sync took effect or had yet to take effect, the
surviving file choices start another attempt in the same retry lineage. -/
theorem reopenSyncInterrupted_preservesRetry {stop : Type}
    {initial before acquired prepared reached : FileImage}
    (acquire : ExceptT IO.Error (EStateM stop FileImage) (KeeperDescriptorIdentity × Selection))
    (prepare : Selection → ExceptT IO.Error (EStateM stop FileImage)
      (WalSegmentRepair.Plan × WalSegmentRepair.Reopened × Nat))
    (sync : KeeperDescriptorIdentity → EStateM stop (WalInodeImage × FileImage) (Except IO.Error Unit))
    (physical after : WalInodeImage) (handle : KeeperDescriptorIdentity)
    (finish : WalSegmentRepair.Plan → Nat → ExceptT IO.Error (EStateM stop FileImage) Unit)
    {plan : WalSegmentRepair.Plan} {opened : WalSegmentRepair.Reopened} {size : Nat}
    {stopped : stop} {selected : Selection}
    (openedMarker : acquire.run before = .ok (.ok (handle, selected)) acquired)
    (read : (prepare selected).run acquired = .ok (.ok (plan, opened, size)) prepared)
    (cut : sync handle (physical, prepared) = .error stopped (after, reached))
    (prior : ReportedMarkerRetries initial prepared)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (project : WalInodeImage → FileImage)
    (source : project physical = prepared) (reachedImage : project after = reached)
    (current : handle.inode = physical.active)
    (sameBinding : ∀ inode ∈ physical.crashBindings, inode = physical.active)
    (decoded : decode (physical.visible handle.inode) = .ok selected)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = prepared.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (survivors : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ after.crashBindings, bytes ∈ after.crashBytes inode)
    (projection : after = physical.completeFileSync physical.active →
      ∀ directory, projectRepairDirectory prepared.directory (physical.visible handle.inode) choices =
        .ok directory → project after = { prepared with directory })
    (inventory : DiskSession.DescriptorInventory)
    (captured : inventory.inode handle.description = handle.inode)
    (effect : after = physical ∨
      after = physical.completeFileSync (inventory.inode handle.description))
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {names : List Nat}
    (metadata : pair ∈ reached.directory.crashImages)
    (keeper : bytes ∈ reached.keeper.crashImages) (later : names ∈ reached.later.crashImages) :
    (reopenAcquiredWith acquire prepare (fun descriptor => ExceptT.mk (projectMarkerSync sync physical descriptor))
      finish).run before =
      .error stopped reached ∧
      ReportedMarkerRetries initial (reached.crash pair bytes names) := by
  constructor
  · change acquire before = .ok (.ok (handle, selected)) acquired at openedMarker
    change prepare selected acquired = .ok (.ok (plan, opened, size)) prepared at read
    simp [reopenAcquiredWith, reopenWith, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, openedMarker, read, projectMarkerSync, cut]
  · have projectedEffect : reached = prepared ∨
        reached = { prepared with directory := settleMarker prepared.directory selected } := by
      rw [← reachedImage]
      rw [captured, current] at effect
      rcases effect with unchanged | completed
      · exact Or.inl (unchanged.symm ▸ source)
      · have bound : prepared.directory.active.walBoundary.isSome = true := by simp [observed]
        have directory := completedMarkerSync_projectsRepairDirectory completed current sameBinding decoded
          prepared.directory bound choices enumerated presence survivors
        exact Or.inr (projection completed _ directory)
    exact .powerLoss (.markerInterrupted prior selected observed projectedEffect) metadata keeper later

/-- The descriptor's error report determines which retry image is
reachable. A reported error after persistence settles only the marker. -/
theorem reopenSyncError_preservesRetry
    {directory : DiskDirectory} {descriptor nextRef : Nat} (unlock : DiskSession.UnlockReport)
    {initial acquired prepared reached : FileImage} {before : LockedFileState FileImage}
    (prior : ReportedMarkerRetries initial prepared) (selection : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    {acquire : EStateM IO.Error FileImage (KeeperDescriptorIdentity × Selection)}
    {prepare : Selection → EStateM IO.Error FileImage (WalSegmentRepair.Plan × WalSegmentRepair.Reopened × Nat)}
    {syncMarker : KeeperDescriptorIdentity → EStateM IO.Error (WalInodeImage × FileImage) Unit}
    {finish : WalSegmentRepair.Plan → Nat → EStateM IO.Error FileImage Unit}
    {plan : WalSegmentRepair.Plan} {opened : WalSegmentRepair.Reopened} {size : Nat} {cause : IO.Error}
    {physical after : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (openedMarker : acquire before.image = .ok (handle, selection) acquired)
    (read : prepare selection acquired = .ok (plan, opened, size) prepared)
    (barrier : syncMarker handle (physical, prepared) = .error cause (after, reached))
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle physical (fun inode files => files.completeFileSync inode) (.error cause after))
    (project : WalInodeImage → FileImage)
    (priorImage : project physical = prepared)
    (reachedImage : project after = reached)
    (current : handle.inode = physical.active)
    (sameBinding : ∀ inode ∈ physical.crashBindings, inode = physical.active)
    (decoded : decode (physical.visible handle.inode) = .ok selection)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = prepared.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (survivors : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ after.crashBindings, bytes ∈ after.crashBytes inode)
    (projection : after = physical.completeFileSync physical.active →
      ∀ directory, projectRepairDirectory prepared.directory (physical.visible handle.inode) choices =
        .ok directory → project after = { prepared with directory }) :
    (DiskSession.runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
      (do
        let (opened, _, _) ← reopenAcquiredWith acquire prepare
          (projectMarkerSync syncMarker physical) finish
        pure opened) before =
      match unlock with
      | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup applied => .error cleanup
          ⟨reached, before.owners.set (directory.file .lock) (if applied then none else some descriptor)⟩) ∧
    ReportedMarkerRetries initial reached ∧ reached.keeper = prepared.keeper := by
  have aligned : ReportedMarkerRetries initial reached ∧ reached.keeper = prepared.keeper := by
    have effect := sync.effect
    rw [sync.sameInode, current] at effect
    generalize sync.effective = effective at effect
    cases effect with
    | errorBefore =>
      have same : reached = prepared := reachedImage.symm.trans priorImage
      exact ⟨same ▸ prior, congrArg FileImage.keeper same⟩
    | errorAfter =>
      have bound : prepared.directory.active.walBoundary.isSome = true := by simp [observed]
      have settledDirectory := completedMarkerSync_projectsRepairDirectory rfl current sameBinding decoded
        prepared.directory bound choices enumerated presence survivors
      have settled := projection rfl _ settledDirectory
      have syncImage : project (physical.completeFileSync handle.inode) =
          { prepared with directory := settleMarker prepared.directory selection } := by
        simpa only [current] using settled
      have retry : ReportedMarkerRetries initial reached := by
        rw [← reachedImage]
        exact .markerSync prior sync project priorImage selection observed syncImage
      exact ⟨retry, by rw [← reachedImage, settled]⟩
  have projectedFailure : projectMarkerSync syncMarker physical handle prepared = .error cause reached := by
    simp only [projectMarkerSync, barrier]
  have reopened : reopenAcquiredWith acquire prepare
      (projectMarkerSync syncMarker physical) finish before.image = .error cause reached := by
    simp only [reopenAcquiredWith_reports, openedMarker, reopenWith_reports, read, projectedFailure]
  refine ⟨?_, aligned⟩
  rw [DiskSession.runOpenWithInstallation_outcome, DiskSession.runOpenWithImage_acquired]
  simp only [Bind.bind, EStateM.bind, reopened]
  cases unlock <;> rfl

/-- Derive the initial retry alternatives from the physical marker
survivors of the interrupted slot write. An absent binding can arise
before bootstrap has settled the marker name. -/
theorem interruptedMarker_retryChoices
    {image : DirectoryPublication.Image} {checkpoint : Option ByteArray}
    {before : ByteArray} {active : OrderedTwoSlot.Slot} {current : Selection}
    {next : Selection}
    (accepted : decode before = .ok current)
    (offset : current.slot = slotIndex active)
    (newer : current.toRecord.epoch < next.toRecord.epoch)
    (observations : ∀ pair ∈ image.active :: image.crashImages,
      pair = ⟨checkpoint, none⟩ ∨
      ∃ bytes,
        InterruptedSlotBytes before bytes active next ∧
        projectBinding ⟨checkpoint, none⟩ bytes = .ok pair) :
    ∀ pair ∈ image.active :: image.crashImages,
      pair.manifest = checkpoint ∧ (pair.walBoundary = none ∨
        pair.walBoundary = some (Boundary.encode current.frontier) ∨
        pair.walBoundary = some (Boundary.encode next.frontier)) := by
  intro pair member
  rcases observations pair member with rfl | ⟨bytes, report, projected⟩
  · exact ⟨rfl, .inl rfl⟩
  · obtain ⟨_, unchanged, target⟩ := report
    have slotTarget :
        decodedSlots bytes active.other = decodedSlots before active.other ∨
        decodedSlots bytes active.other = none ∨
        decodedSlots bytes active.other = some next.toRecord := by
      rcases target with old | invalid | fresh
      · exact .inl (congrArg (Option.map Selection.toRecord) old)
      · exact .inr (.inl (congrArg (Option.map Selection.toRecord) invalid))
      · exact .inr (.inr (congrArg (Option.map Selection.toRecord) fresh))
    have survivor := uncertainSurvivor_of_bytes active next unchanged slotTarget
    obtain ⟨manifest, boundary⟩ := projectBinding_oldOrNew survivor accepted offset newer projected
    exact ⟨manifest, .inr boundary⟩

/-- The retry trace supplies the actual frontier used by the recovered
table. The retained client history follows from that retry-selected marker. -/
theorem recoveredRetries_retainUncertainBatch
    {initial prepared firstRepair after : FileImage} {target : Target}
    (beforeBarrier : UnsettledRetries initial prepared)
    {checkpoint : Option ByteArray} {before : ByteArray} {active : OrderedTwoSlot.Slot}
    {current : Selection} {next : Selection}
    (accepted : decode before = .ok current)
    (offset : current.slot = slotIndex active)
    {history batch : List Write}
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (observations : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      pair = ⟨checkpoint, none⟩ ∨
      ∃ bytes,
        InterruptedSlotBytes before bytes active next ∧
        projectBinding ⟨checkpoint, none⟩ bytes = .ok pair)
    (selected : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (authorizedRepair : EffectTrace target
      { prepared with directory := settleMarker prepared.directory selected } firstRepair)
    {plan : WalSegmentRepair.Plan} (preparedPlan : WalSegmentRepair.Prepared prepared target plan)
    (retries : SettledRetries target firstRepair after)
    {image : WalSegmentImage} {range : MarkedWalRange}
    {base table : PackedTable} {first : Nat} {log : List DatabaseSubmissions}
    (prior : DatabaseBatchRetention log history)
    (oldSize : current.frontier.toNat = (WAL.encode history).size)
    (recovery : WalSegmentRecovery image after.directory.active range (history ++ batch) base first table) :
    DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
    (∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model) ∧
    ((history ++ batch).take range.through = history ∨
      (history ++ batch).take range.through = history ++ batch) := by
  obtain ⟨_, epoch, newSize, _, _⟩ := advance_fields advanced
  have newer : current.toRecord.epoch < next.toRecord.epoch := by
    change current.epoch.toNat < next.epoch.toNat
    omega
  have authorized := prepared_settleMarker preparedPlan selected observed
  have choices := interruptedMarker_retryChoices accepted offset newer observations
  obtain ⟨_, binding, choice, _⟩ := retries_preservePublishedFrontier beforeBarrier checkpoint
    current.frontier next.frontier
    choices selected observed authorizedRepair authorized.pair authorized.keeperPrefix
    authorized.newer retries (List.mem_cons_self ..)
  have whole : _ ∨ _ := choice.imp
    (fun oldFrontier => oldFrontier ▸ oldSize) (fun newFrontier => newFrontier ▸ newSize)
  obtain ⟨retained, represented⟩ := recoveredBatch_retains prior recovery binding whole
  exact ⟨retained, represented, recoveredBatch_history recovery binding whole⟩

private theorem sealedReads_eq {files : FileImage} {left right : List (Nat × ByteArray)}
    (offsets : left.map Prod.fst = right.map Prod.fst)
    (leftBytes : ∀ file ∈ left, files.kept file.1 = some file.2)
    (rightBytes : ∀ file ∈ right, files.kept file.1 = some file.2) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons entry tail ih =>
    cases right with
    | nil => simp at offsets
    | cons other rest =>
      have head := List.cons.inj offsets
      have sameBytes := Option.some.inj
        ((leftBytes entry (by simp)).symm.trans (head.1.symm ▸ rightBytes other (by simp)))
      have sameEntry := Prod.ext head.1 sameBytes
      rw [sameEntry]
      exact congrArg (List.cons other)
        (ih head.2 (fun file found => leftBytes file (List.mem_cons_of_mem _ found))
          (fun file found => rightBytes file (List.mem_cons_of_mem _ found)))

/-- The open records its reached inventory before the bounded read. The
read advances the reported cursor on that same description. -/
def acquireMarkerWithInventoryUsing {state : Type}
    (readMarker : Nat → (USize → EStateM IO.Error Nat ByteArray) → EStateM IO.Error Nat ByteArray)
    (reached : DiskSession.DescriptorInventory → state → state)
    (reads : WalSegmentRepair.CheckpointRunChunkReads) (path : System.FilePath) :
    EStateM IO.Error state (KeeperDescriptorIdentity × Selection) := do
  let (metadata, _) ← liftExcept (reads.stat path)
  checkPrivateRegularWith path metadata
  fun files =>
    match reads.openRead path with
    | .error cause => .error cause files
    | .ok (inventory, slot, cursor) =>
      let files := reached inventory files
      let handle : KeeperDescriptorIdentity := ⟨slot.description, inventory.inode slot.description⟩
      match readMarker handle.description (reads.readChunk handle.description) cursor with
      | .error cause _ => .error cause files
      | .ok bytes _ =>
        match decode bytes with
        | .error cause => .error (IO.userError cause) files
        | .ok selected => .ok (handle, selected) files

def acquireMarkerWithInventory {state : Type}
    (reached : DiskSession.DescriptorInventory → state → state)
    (reads : WalSegmentRepair.CheckpointRunChunkReads) (path : System.FilePath) :
    EStateM IO.Error state (KeeperDescriptorIdentity × Selection) :=
  acquireMarkerWithInventoryUsing
    (fun _ read => readPrefixUntilEofWith (IO.userError "invalid two-slot WAL marker length")
      read acquisitionLimit ByteArray.empty)
    reached reads path

/-- The projected cursor already includes the successful native rewind.
Running the shared reader with that effect accounted for gives the
same acquisition action, including its bounded reads and error returns. -/
theorem acquireMarkerWithInventory_sharedReader {state : Type}
    (reached : DiskSession.DescriptorInventory → state → state)
    (reads : WalSegmentRepair.CheckpointRunChunkReads) (path : System.FilePath) :
    acquireMarkerWithInventoryUsing (fun _ => readMarkerBytesWith (EStateM.pure ())) reached reads path =
      acquireMarkerWithInventory reached reads path := by
  have same : (fun (_ : Nat) => readMarkerBytesWith (EStateM.pure ())) =
      (fun (_ : Nat) (read : USize → EStateM IO.Error Nat ByteArray) =>
        readPrefixUntilEofWith (IO.userError "invalid two-slot WAL marker length")
          read acquisitionLimit ByteArray.empty) := by
    funext description read cursor
    rfl
  exact congrArg (fun readMarker => acquireMarkerWithInventoryUsing readMarker reached reads path) same

def acquireMarkerFromReports (reads : WalSegmentRepair.CheckpointRunChunkReads) (path : System.FilePath) :
    EStateM IO.Error FileImage (KeeperDescriptorIdentity × Selection) :=
  acquireMarkerWithInventoryUsing (fun _ => readMarkerBytesWith (EStateM.pure ())) (fun _ files => files) reads path

/-- The native acquisition projection retains the opened marker slot
in the state passed to checkpoint preparation. -/
def acquireMarkerInCensus (reads : WalSegmentRepair.CheckpointRunChunkReads) (path : System.FilePath)
    (rewind : Nat → EStateM IO.Error Nat Unit) :
    EStateM IO.Error (DiskSession.CensusDirectoryCache × DiskSession.CensusOpenState)
      (KeeperDescriptorIdentity × Selection) :=
  acquireMarkerWithInventoryUsing (fun description => readMarkerBytesWith (rewind description))
    (fun inventory (cache, _, files) => (cache, inventory, files)) reads path

/-- A successful rewind on the reached marker description and its
bounded reads supply the exact selection and descriptor to recovery. -/
theorem acquireMarkerInCensus_afterRewind
    {reads : WalSegmentRepair.CheckpointRunChunkReads} {directory : DiskDirectory}
    {view : DiskSession.DirectoryReadNamespace} {root : DiskSession.DeviceInode} {payload : ByteArray}
    (file : DiskSession.HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload)
    (privateFile : file.calls.metadata.numLinks = 1)
    (available : PrefixChunksAvailableUntilEof payload (reads.readChunk file.calls.slot.description))
    (rewind : Nat → EStateM IO.Error Nat Unit) (rewound : rewind file.calls.slot.description 0 = .ok () 0)
    {selected : Selection} (decoded : decode payload = .ok selected)
    (before : DiskSession.CensusDirectoryCache × DiskSession.CensusOpenState) :
    acquireMarkerWithInventoryUsing (fun description => readMarkerBytesWith (rewind description))
      (fun inventory (cache, _, files) => (cache, inventory, files)) reads (directory.file .walBoundary) before =
      .ok (⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩, selected)
        (before.1, file.calls.inventory, before.2.2) := by
  obtain ⟨bytes, returned, agrees⟩ := readMarkerBytesWith_decodesHeldMarker file available (rewind file.calls.slot.description) 0 rewound
  cases before
  simp [acquireMarkerWithInventoryUsing, checkPrivateRegularWith, file.calls.stat,
    file.calls.regular, privateFile, file.calls.opened, returned,
    show (IO.FS.FileType.file == .file) = true from rfl,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, liftExcept, agrees.trans decoded]

theorem acquireMarkerInCensus_returns
    {reads : WalSegmentRepair.CheckpointRunChunkReads} {directory : DiskDirectory}
    {view : DiskSession.DirectoryReadNamespace} {root : DiskSession.DeviceInode}
    {payload : ByteArray}
    (file : DiskSession.HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload)
    (privateFile : file.calls.metadata.numLinks = 1)
    (available : PrefixChunksAvailableUntilEof payload (reads.readChunk file.calls.slot.description))
    {selected : Selection} (decoded : decode payload = .ok selected)
    (before : DiskSession.CensusDirectoryCache × DiskSession.CensusOpenState) :
    acquireMarkerInCensus reads (directory.file .walBoundary) (fun _ => EStateM.pure ()) before =
      .ok (⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩, selected)
        (before.1, file.calls.inventory, before.2.2) := by
  exact acquireMarkerInCensus_afterRewind file privateFile available (fun _ => EStateM.pure ()) rfl decoded before


section CapturedPreparation

open DiskSession WalSegmentRepair

variable {input : System.FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- The checkpoint callbacks start at the census returned by opening
the marker, using the same held lock and cached directory. -/
theorem acquiresAndReadsCheckpoint
    (report : CapturedMarkedReadReports admission layout published false)
    {payload : ByteArray}
    (file : HeldMetadataFile report.reads (directory.file .walBoundary) "WAL.commit"
      admission.view admission.root payload)
    (privateFile : file.calls.metadata.numLinks = 1)
    (available : PrefixChunksAvailableUntilEof payload (report.reads.readChunk file.calls.slot.description))
    {selection : Selection} (decoded : decode payload = .ok selection)
    {release : System.FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report release file.calls.inventory manifestDrops)
    (runs : CapturedRunReadCensus report (file.calls.inventory.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) :
    ((do
      let marker ← acquireMarkerInCensus report.reads (directory.file .walBoundary) (fun _ => EStateM.pure ())
      let checkpoint ← report.readCheckpointFromCensus release runs.released
      pure (marker, checkpoint)) :
      EStateM IO.Error (CensusDirectoryCache × CensusOpenState)
        ((KeeperDescriptorIdentity × Selection) × Option (PackedTable × UInt64)))
      (admission.cache, admission.reached, admission.held) =
      .ok ((⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩, selection), checkpoint)
        (admission.cache,
          (file.calls.inventory.afterDrops manifestDrops).afterDrops
            (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest)), admission.held) := by
  have acquired := acquireMarkerInCensus_returns file privateFile available decoded
    (admission.cache, admission.reached, admission.held)
  simp only [Bind.bind, EStateM.bind, acquired, runs.reads manifest selected, Pure.pure, EStateM.pure]

/-- The prepared table and plan use the exact checkpoint and WAL
callbacks. The reached state carries both the keeper and marker slots. -/
theorem preparesFromHeldMarker
    {markerReads : CheckpointRunChunkReads} {payload : ByteArray}
    (file : HeldMetadataFile markerReads (directory.file .walBoundary) "WAL.commit" admission.view admission.root payload)
    (privateFile : file.calls.metadata.numLinks = 1)
    (available : PrefixChunksAvailableUntilEof payload (markerReads.readChunk file.calls.slot.description))
    (rewind : Nat → EStateM IO.Error Nat Unit) (rewound : rewind file.calls.slot.description 0 = .ok () 0)
    (report : CapturedMarkedReadReports admission layout published false file.calls.inventory)
    {metadataRelease : System.FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease file.calls.inventory manifestDrops)
    (runs : CapturedRunReadCensus report (file.calls.inventory.afterDrops manifestDrops))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))
    (selection : Selection) (decoded : decode payload = .ok selection)
    (count : selection.frontier.toNat = layout.range.through * WAL.frameSize)
    (ordered : WAL.OrdinalsFrom 1 history) {table : PackedTable}
    (replay : recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table)
    (captured : CapturedKeeperOpenReports report) {released : System.FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)}
    {retains : DescriptorSlot → Prop}
    (seals : CapturedSealReadChainWith report released retains required report.listing.afterClose captured.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ captured.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ retry.image.later.visible, layout.range.through < start)
    (keepsMarker : retains file.calls.slot)
    (listingDrops : ∀ event ∈ report.listing.beforeOpen ++ report.listing.duringScan,
      event.removes file.calls.slot.reference = false)
    (keeperDrops : ∀ event ∈ captured.duringRead, event.removes file.calls.slot.reference = false) :
    let handle := (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
    let cache := admission.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
      handle layout.keeper.bytes.size report.wal.keeper.calls.metadata.byteSize.toNat
    acquireMarkerInCensus markerReads (directory.file .walBoundary) rewind
      (admission.cache, admission.reached, admission.held) =
      .ok (⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩, selection)
        (admission.cache, file.calls.inventory, admission.held) ∧
    prepareBoundedMarkedFromReaders directory (report.readCheckpointFromCensus metadataRelease runs.released)
        (fun _ => pure (some (Boundary.encode selection.frontier)))
        (fun watermark length => readSelectedWithCachedExtents directory watermark length report.scanWal
          report.inspectWal (readTemporarySeal report.reads released) captured.readKeeperAt)
        (admission.cache, file.calls.inventory, admission.held) =
      .ok (layout.boundedPlan, ⟨table, (checkpoint.getD (.empty, 0)).2, selection.frontier, layout.keeper.first⟩,
          report.wal.keeper.calls.metadata.byteSize.toNat) (cache, captured.afterRead, admission.held) ∧
    file.calls.slot ∈ captured.afterRead.slots ∧
    captured.afterRead.inode file.calls.slot.description =
      file.calls.inventory.inode file.calls.slot.description := by
  intro handle cache
  have watermark := Option.some.inj (selected.watermark.symm.trans
    (DirectoryPublication.Bindings.walRange_accounting layout.decoded).1)
  obtain ⟨walRead, live⟩ := report.walFromScan count captured seals offsets retained following later
    keepsMarker file.calls.live listingDrops keeperDrops
  let files := (layout.sealed ++ [layout.keeper]).map (fun segment => (segment.first, segment.bytes))
  have replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 selection.frontier files =
      .ok (WAL.encode (history.drop layout.first), table) := by
    simpa only [files, List.map_append, List.map_cons, List.map_nil, ByteArray.append_empty] using
      layout.chain.replaysMarked ByteArray.empty (layout.through ▸ count)
        (watermark.symm ▸ layout.covers) ordered replay
  have last : files.getLast? = some (layout.keeper.first, layout.keeper.bytes) := by simp [files]
  have prepared := prepareSelected_stateful directory (Boundary.encode selection.frontier) selection.frontier
    (Boundary.decode_encode _) (report.readCheckpointFromCensus metadataRelease runs.released)
    (fun watermark length => readSelectedWithCachedExtents directory watermark length report.scanWal
      report.inspectWal (readTemporarySeal report.reads released) captured.readKeeperAt)
    (report.checkpointAtScan manifest runs selected chronology)
    (by simpa only [watermark] using walRead) replayed last
  have through : selection.frontier.toNat / WAL.frameSize = layout.range.through := by
    rw [count, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  rw [through] at prepared
  exact ⟨acquireMarkerInCensus_afterRewind file privateFile available rewind rewound decoded _, prepared, live,
    congrFun (captured.afterRead_inode.trans report.objectMap.symm) file.calls.slot.description⟩

/-- Construct the marker barrier from the prepared keeper census and
derive the exact directory image that enters repair. -/
theorem stabilizesAfterKeeperRead
    {readStart : DescriptorInventory}
    (report : CapturedMarkedReadReports admission layout published false readStart)
    (captured : CapturedKeeperOpenReports report)
    {marker settled : WalInodeImage} {slot : DescriptorSlot}
    (live : slot ∈ captured.afterRead.slots)
    (current : captured.afterRead.inode slot.description = marker.active)
    (effect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync marker.active) true (.ok () settled))
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selection : Selection} (decoded : decode (marker.visible marker.active) = .ok selection)
    (bound : retry.image.directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode) :
    projectRepairDirectory retry.image.directory (marker.visible marker.active) choices =
      .ok (settleMarker retry.image.directory selection) := by
  let handle : KeeperDescriptorIdentity := ⟨slot.description, marker.active⟩
  have inode : captured.afterRead.inode handle.description = handle.inode :=
    current
  have liveReference : slot.reference ∈ (captured.afterRead.afterDrops []).references handle.description := by
    rw [DescriptorInventory.references_afterDrops]
    exact List.mem_filter.mpr ⟨(captured.afterRead.mem_references).mpr ⟨slot, live, rfl, rfl⟩, rfl⟩
  have observed := FsyncObservation.ofInventory captured.afterRead []
    KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode handle
    slot.reference liveReference inode marker (fun object (files : WalInodeImage) => files.completeFileSync object)
    (by rw [inode]; exact effect)
  exact reopenSync_projectsRepairDirectory observed rfl sameBinding decoded
    retry.image.directory bound choices enumerated presence physical

/-- Project the successful marker barrier into the repair state. File
sync changes the selected marker projection, retaining the cache,
descriptor census, and lock owner used by the next callback. -/
def stabilizeCapturedMarker (visible : ByteArray)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray)) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit :=
  fun (cache, census, files) =>
    match projectRepairDirectory files.image.directory visible choices with
    | .error cause => .error (IO.userError cause) (cache, census, files)
    | .ok settled => .ok () (cache, census, { files with image := { files.image with directory := settled } })

/-- The reported successful marker sync authorizes the bounded repair
on the exact reached keeper state. A successful finish returns the
same plan's opened table and the repair's reached state. -/
theorem reopensAfterCapturedPreparation
    {readStart : DescriptorInventory}
    (report : CapturedMarkedReadReports admission layout published false readStart)
    (captured : CapturedKeeperOpenReports report)
    {marker settled : WalInodeImage} {slot : DescriptorSlot}
    (live : slot ∈ captured.afterRead.slots)
    (current : captured.afterRead.inode slot.description = marker.active)
    (effect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync marker.active) true (.ok () settled))
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selection : Selection} (decoded : decode (marker.visible marker.active) = .ok selection)
    (bound : retry.image.directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode)
    {before after : CensusDirectoryCache × CensusOpenState}
    {cache : CensusDirectoryCache} {opened : Reopened} {size : Nat}
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (prepared : prepare before = .ok (layout.boundedPlan, opened, size) (cache, captured.afterRead, admission.held))
    (finish : Plan → Nat → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (finished : finish layout.boundedPlan size
      (cache, captured.afterRead,
        { admission.held with image := { retry.image with directory := settleMarker retry.image.directory selection } }) =
      .ok () after) :
    reopenWith prepare (stabilizeCapturedMarker (marker.visible marker.active) choices) finish before =
      .ok opened after := by
  have projected := stabilizesAfterKeeperRead report captured live current effect sameBinding decoded
    bound choices enumerated presence physical
  have barrier : stabilizeCapturedMarker (marker.visible marker.active) choices
      (cache, captured.afterRead, admission.held) =
      .ok () (cache, captured.afterRead,
        { admission.held with image := { retry.image with directory := settleMarker retry.image.directory selection } }) := by
    change (match projectRepairDirectory retry.image.directory (marker.visible marker.active) choices with
      | .error cause => _
      | .ok settled => _) = _
    rw [projected]
    rfl
  simp only [reopenWith_reports, prepared, barrier, finished]

/-- The aligned case runs marker fsync, directory fsync and the cached
keeper fsync in order, using the exact state returned by each call. -/
theorem reopensAlignedAfterCapturedPreparation
    {readStart : DescriptorInventory}
    (report : CapturedMarkedReadReports admission layout published false readStart)
    (captured : CapturedKeeperOpenReports report)
    {marker settled : WalInodeImage} {slot : DescriptorSlot}
    (live : slot ∈ captured.afterRead.slots)
    (current : captured.afterRead.inode slot.description = marker.active)
    (effect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync marker.active) true (.ok () settled))
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selection : Selection} (decoded : decode (marker.visible marker.active) = .ok selection)
    (bound : retry.image.directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode)
    (aligned : layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat)
    (noLater : retry.image.later.visible = [])
    {before : CensusDirectoryCache × CensusOpenState} {opened : Reopened}
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (prepared : prepare before =
      .ok (layout.boundedPlan, opened, report.wal.keeper.calls.metadata.byteSize.toNat)
        (admission.cache.remember (directory.file (.walSegment layout.keeper.first))
          (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0), captured.afterRead, admission.held))
    (openRead : System.FilePath → EStateM IO.Error CensusOpenState (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error CensusOpenState Unit)
    (removeFile : System.FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Except IO.Error Unit))
    (write : System.FilePath → ByteArray → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (renameFile : System.FilePath → System.FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    {after : CensusOpenState}
    (directorySync :
      let before := { admission.held with image :=
        { retry.image with directory := settleMarker retry.image.directory selection } }
      fsync (admission.reached, admission.cached, 0) (captured.afterRead, before) =
        match (captured.directoryBarrier .completed).run before with
        | .ok value reached => .ok value (captured.afterRead, reached)
        | .error cause reached => .error cause (captured.afterRead, reached))
    (keeperSync :
      let before := { admission.held with image :=
        { retry.image with directory := settleMarker retry.image.directory selection } }
      fsync (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
        (captured.afterRead, { before with image := before.image.syncDirectory }) = .ok () after) :
    reopenWith prepare (stabilizeCapturedMarker (marker.visible marker.active) choices)
        (fun plan extent => finishBoundedMarkedOpen directory plan extent removeFile write
          (Storage.SyncPathGroup.run (Storage.SyncHandleRouting.sync directory.path openRead fsync)) renameFile) before =
      .ok opened (admission.cache, after) := by
  apply reopensAfterCapturedPreparation report captured live current effect sameBinding decoded
    bound choices enumerated presence physical prepare prepared
  have returned := captured.finishAlignedFromCache aligned noLater openRead fsync
    removeFile write renameFile (captured.directoryBarrier_completed _ fsync directorySync)
  simpa only [keeperSync] using returned

/-- Install the marked worker's recovered table in the admitted session.
The acquired marker and selection feed recovery before the cache is dropped
from the returned state. -/
theorem installsAfterAcquiredRecovery
    (calls : CapturedAlignedCallbacks admission)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (acquire : DiskDirectory → EStateM IO.Error (CensusDirectoryCache × CensusOpenState)
      (KeeperDescriptorIdentity × Selection))
    (prepare : DiskDirectory → Selection → EStateM IO.Error (CensusDirectoryCache × CensusOpenState)
      (Plan × Reopened × Nat))
    (stabilize : KeeperDescriptorIdentity → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (finish : DiskDirectory → Plan → Nat → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    {handle : KeeperDescriptorIdentity} {selection : Selection}
    {acquired : CensusDirectoryCache × CensusOpenState}
    (acquisition : acquire directory (admission.cache, admission.reached, admission.held) =
      .ok (handle, selection) acquired)
    {opened : Reopened} {after : CensusOpenState}
    (recovery : reopenWith (prepare directory selection) (stabilize handle) (finish directory) acquired =
      .ok opened (admission.cache, after)) :
    calls.runWithMarked (fun resolved cache before =>
      match reopenAcquiredWith (acquire resolved) (prepare resolved) stabilize (finish resolved) (cache, before) with
      | .ok (opened, _, _) (_, reached) => .ok opened reached
      | .error cause (_, reached) => .error cause reached) =
      .ok ⟨directory, admission.owner.description, .ready opened.installed, calls.nextRef, calls.nextRef + 1⟩ after := by
  apply calls.runWithMarked_ready _ marker
  simp only [reopenAcquiredWith_reports, acquisition, recovery]

/-- Reports for the three successful repairs reached after reading the
selected keeper. The indices pair the actual callback with its reached
state so the client proof cannot mix reports from different branches. -/
inductive CapturedFinalRepair (calls : CapturedAlignedCallbacks admission)
    {readStart : DescriptorInventory}
    {report : CapturedMarkedReadReports admission layout published false readStart}
    {loaded : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest loaded)
    (files : LockedFileState FileImage) :
    CapturedKeeperOpenReports report →
    (DiskDirectory → Plan → Nat → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit) →
    CensusOpenState → Prop where
  | aligned (keeper : CapturedKeeperOpenReports report)
      (aligned : layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat)
      (noLater : retry.image.later.visible = []) (later : files.image.later.visible = [])
      (exactRead : files.image.keeper.active = some layout.keeper.bytes)
      (openRead : System.FilePath → EStateM IO.Error CensusOpenState (DescriptorInventory × DescriptorSlot × Nat))
      (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error CensusOpenState Unit)
      (removeFile : System.FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Except IO.Error Unit))
      (write : System.FilePath → ByteArray → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
      (renameFile : System.FilePath → System.FilePath → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
      (directorySync : fsync (admission.reached, admission.cached, 0) (keeper.afterRead, files) =
        match (keeper.directoryBarrier .completed).run files with
        | .ok value reached => .ok value (keeper.afterRead, reached)
        | .error cause reached => .error cause (keeper.afterRead, reached))
      {after : DescriptorInventory}
      (keeperSync : fsync (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
        (keeper.afterRead, { files with image := files.image.syncDirectory }) =
        .ok () (after, { files with image := files.image.syncDirectory.syncKeeper })) :
      CapturedFinalRepair calls selected files keeper
        (fun resolved plan size => finishBoundedMarkedOpen resolved plan size removeFile write
          (Storage.SyncPathGroup.run (Storage.SyncHandleRouting.sync resolved.path openRead fsync)) renameFile)
        (after, { files with image := files.image.syncDirectory.syncKeeper })
  | replacement {vacant : TryLockObserves retry.owners directory (.ok true)}
      (repair : CapturedLongKeeperFinish calls report vacant selected)
      (same : files.image.syncDirectory = retry.image.syncDirectory)
      (first : repair.authorization.fsync (admission.reached, admission.cached, 0) files =
        .ok () { admission.held with image := retry.image.syncDirectory }) :
      CapturedFinalRepair calls selected files repair.reader repair.repairAfterRead (repair.census, repair.settled)
  | prune {vacant : TryLockObserves retry.owners directory (.ok true)}
      (repair : CapturedPrunedAlignedFinish calls report vacant selected)
      (same : files.image.syncDirectory = retry.image.syncDirectory)
      (first : repair.authorization.fsync (admission.reached, admission.cached, 0) files =
        .ok () { admission.held with image := retry.image.syncDirectory })
      (later : ∀ name ∈ retry.image.later.visible, layout.range.through < name) :
      CapturedFinalRepair calls selected files repair.reader repair.repairActions (repair.census, repair.settled)

theorem CapturedFinalRepair.returns
    {calls : CapturedAlignedCallbacks admission} {readStart : DescriptorInventory}
    {report : CapturedMarkedReadReports admission layout published false readStart}
    {loaded : Option (PackedTable × UInt64)}
    {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest loaded}
    {files : LockedFileState FileImage} {keeper finish after}
    (repair : CapturedFinalRepair calls (report := report) selected files keeper finish after) :
    finish directory layout.boundedPlan report.wal.keeper.calls.metadata.byteSize.toNat
      (admission.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
        (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
        layout.keeper.bytes.size report.wal.keeper.calls.metadata.byteSize.toNat, keeper.afterRead, files) =
      .ok () (admission.cache, after) ∧ EffectTrace layout.target files.image after.2.image := by
  cases repair with
  | aligned keeper aligned noLater later exactRead openRead fsync removeFile write renameFile directorySync keeperSync =>
    simpa only [Storage.SyncHandleRouting.Cache.captureKeeper, aligned, beq_self_eq_true, ↓reduceIte] using
      keeper.finishAligned_effects aligned noLater openRead fsync removeFile write renameFile files
        later exactRead directorySync keeperSync
  | replacement repair same first =>
    have extent : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
      report.wal.keeper.observesFile.extent
    have unequal : layout.keeper.bytes.size ≠ layout.plan.keeperBytes.size :=
      Nat.ne_of_lt (extent ▸ repair.longer)
    simpa only [Storage.SyncHandleRouting.Cache.captureKeeper, extent, ite_eq_right unequal,
      ↓reduceIte] using repair.repairAfterRead_returns_from files same first
  | prune repair same first later =>
    have extent : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
      report.wal.keeper.observesFile.extent
    have aligned := repair.repair.aligned
    rw [repair.sameKeeper] at aligned
    change layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat at aligned
    simpa only [Storage.SyncHandleRouting.Cache.captureKeeper, extent, aligned.trans extent, beq_self_eq_true, ↓reduceIte]
      using repair.repairActions_returns_from files same first later

private theorem selectedCheckpoint_represents
    {published : CheckpointPublication.Image} {binding : Option ByteArray}
    {loaded : Option (PackedTable × UInt64)} {history : List WAL.Write}
    (selected : SelectedIntegrityCheckpoint published.durable binding loaded)
    (accepted : published.AcceptsVersioned history.length.toUInt64
      (Boundary.CheckpointRepresentsPrefix history) binding) :
    ∃ model, (loaded.getD (.empty, 0)).1.Refines model ∧ (loaded.getD (.empty, 0)).1.RowBounds ∧
      (loaded.getD (.empty, 0)).1.committed.toNat ≤ history.length ∧
      RepresentsWalHistory (history.take (loaded.getD (.empty, 0)).1.committed.toNat) model := by
  cases selected with
  | absent => exact ⟨.empty, PackedTable.empty_refines, PackedTable.empty_rowBounds, Nat.zero_le _, RepresentsWalHistory.empty⟩
  | @present bytes manifest files table decoded stored loaded =>
    obtain ⟨acceptedFiles, durable, spec, _, covered⟩ :=
      published.acceptsVersioned_runs accepted (Manifest.VersionedCheckpoint.decode_integrity decoded)
    have sameFiles : acceptedFiles = files := Option.some.inj (durable.symm.trans stored)
    subst acceptedFiles
    obtain ⟨checkpoint, model, written, refined, historyPrefix⟩ := spec
    obtain ⟨base, interpreted, same⟩ := written.loads
    have structural := (loadIntegrityRunSet_iff.mp loaded).2
    have sameBase := Except.ok.inj (interpreted.symm.trans structural)
    subst base
    have fresh := loadRunSet_clearsPins structural
    obtain ⟨rebound, baseRefines, sameTable, sameClock, sameFloor⟩ :=
      same.refines_rebindPins refined (by simp [fresh])
    have bounds := same.rowBounds written.rowBounds
    have ceiling : table.committed.toNat ≤ history.length := by
      rw [same.committed, ← written.watermark]
      exact Nat.le_trans (UInt64.le_iff_toNat_le.mp covered) (Nat.mod_le ..)
    refine ⟨rebound, baseRefines, bounds, ceiling, ?_⟩
    change RepresentsWalHistory (history.take table.committed.toNat) rebound
    rw [same.committed]
    exact historyPrefix.preserve sameClock (UInt64.le_of_eq sameFloor.symm)
      (baseRefines.rowsBounded bounds) (fun _ _ _ => by rw [sameTable])

/-- Once the marker is authorized, reuse the shared reopen trace for
failed opens, interrupted repairs, descriptor drops and power losses. -/
theorem settledRetriesOfBoundedReopen
    {directory : DiskDirectory} {target : Target} {initial after : LockedFileState FileImage}
    (trace : BoundedReopenTrace directory (fun candidate => candidate = target) initial after) :
    SettledRetries target initial.image after.image := by
  have beforeBarrier {current : FileImage} (prior : BeforeReopenBarrier initial.image current) :
      SettledRetries target initial.image current := by
    cases prior with
    | live => exact .start
    | crash _ _ _ metadata bytes names => exact .crash .start metadata bytes names
  cases trace.lineage (fun a b _ => a.trans b.symm) with
  | before prior => exact beforeBarrier prior
  | repairing prior canonical _ effects =>
    exact .repair (beforeBarrier prior) (canonical ▸ effects)

/-- A cut in the append, WAL sync, inactive slot write or marker sync.
The reached state supplies both the logical file image and physical
marker image used by the retry proof. -/
structure InterruptedBatchMarkerPublication (directory : DiskDirectory) (prior : SegmentedWriterState)
    (batch : List WAL.Write) (next : Selection) (reached : FileImage × WalInodeImage) where
  Stop : Type
  rows : List (UInt64 × Option UInt64)
  table : PackedTable
  initialMarker : WalInodeImage
  markerDescription : Nat
  lookup : System.FilePath → Except IO.Error IO.FS.Metadata
  nonempty : rows ≠ []
  prepared : prepareBatch prior.installed.table rows = some (batch, table)
  fits : prior.installed.walBytes + frameSize * rows.length < UInt64.size
  guard : checkActiveSegmentWith directory prior.installed lookup = .ok ()
  append : System.FilePath → ByteArray → ExceptT IO.Error (EStateM Stop (FileImage × WalInodeImage)) Unit
  syncWal : System.FilePath → ExceptT IO.Error (EStateM Stop (FileImage × WalInodeImage)) Unit
  writeSlot : KeeperDescriptorIdentity → UInt64 → ByteArray → ExceptT IO.Error (EStateM Stop (FileImage × WalInodeImage)) Unit
  syncSlot : KeeperDescriptorIdentity → ExceptT IO.Error (EStateM Stop (FileImage × WalInodeImage)) Unit
  install : KeeperDescriptorIdentity → Selection → ExceptT IO.Error (EStateM Stop (FileImage × WalInodeImage)) Unit
  stopped : Stop
  cut :
    let active := directory.file (.walSegment prior.installed.activeFirst)
    let marker : KeeperDescriptorIdentity := ⟨markerDescription, initialMarker.active⟩
    ((append active (WAL.encode batch)).run (prior.files, initialMarker) = .error stopped reached ∧
      reached.2 = initialMarker) ∨
    ∃ appended, (append active (WAL.encode batch)).run (prior.files, initialMarker) = .ok (.ok ()) appended ∧
      (((syncWal active).run appended = .error stopped reached ∧ reached.2 = initialMarker) ∨
        ∃ durable, (syncWal active).run appended = .ok (.ok ()) durable ∧
          ((writeSlot marker (next.slot * stride).toUInt64 next.encode).run durable = .error stopped reached ∨
            ∃ written, (writeSlot marker (next.slot * stride).toUInt64 next.encode).run durable = .ok (.ok ()) written ∧ (syncSlot marker).run written = .error stopped reached))

def InterruptedBatchMarkerPublication.markerHandle
    {directory : DiskDirectory} {prior : SegmentedWriterState} {batch : List WAL.Write}
    {next : Selection} {reached : FileImage × WalInodeImage}
    (report : InterruptedBatchMarkerPublication directory prior batch next reached) : KeeperDescriptorIdentity :=
  ⟨report.markerDescription, report.initialMarker.active⟩

theorem InterruptedBatchMarkerPublication.stops
    {directory : DiskDirectory} {prior : SegmentedWriterState} {batch : List WAL.Write}
    {next : Selection} {reached : FileImage × WalInodeImage}
    (report : InterruptedBatchMarkerPublication directory prior batch next reached) :
    runBatchWriteWithInterruption directory report.rows report.lookup
      (fun _ _ _ => publish
        (report.append (directory.file (.walSegment prior.installed.activeFirst)) (WAL.encode batch))
        (report.syncWal (directory.file (.walSegment prior.installed.activeFirst)))
        (report.writeSlot report.markerHandle (next.slot * stride).toUInt64 next.encode)
        (report.syncSlot report.markerHandle) (report.install report.markerHandle next))
      (.ready prior.installed, ⟨(prior.files, report.initialMarker), prior.owners⟩) =
      .error report.stopped (.poisoned, ⟨reached, prior.owners⟩) := by
  let active := (directory.file (.walSegment prior.installed.activeFirst))
  let append := report.append active (WAL.encode batch)
  let syncWal := report.syncWal active
  let writeSlot := report.writeSlot report.markerHandle (next.slot * stride).toUInt64 next.encode
  let syncSlot := report.syncSlot report.markerHandle
  let install := report.install report.markerHandle next
  apply runBatchWriteWithInterruption_stopped report.nonempty report.prepared report.fits report.guard
  rcases report.cut with ⟨appendCut, _⟩ | ⟨_, wrote, ⟨walCut, _⟩ | ⟨_, walBarrier, slotCut | ⟨_, slot, syncCut⟩⟩⟩
  · exact publish_appendInterrupted append syncWal writeSlot syncSlot install appendCut
  · exact publish_walSyncInterrupted append syncWal writeSlot syncSlot install wrote walCut
  · exact publish_slotWriteInterrupted append syncWal writeSlot syncSlot install
      wrote walBarrier slotCut
  · exact publish_markerSyncInterrupted append syncWal writeSlot syncSlot install
      wrote walBarrier slot syncCut

/-- If the writer stops before the slot write, the report preserves the
previous physical marker. The later cases require the completed WAL sync. -/
theorem InterruptedBatchMarkerPublication.markerUnchangedOrWalSynced
    {directory : DiskDirectory} {prior : SegmentedWriterState} {batch : List WAL.Write}
    {next : Selection} {reached : FileImage × WalInodeImage}
    (report : InterruptedBatchMarkerPublication directory prior batch next reached) :
    reached.2 = report.initialMarker ∨
      ∃ appended durable,
        let active := directory.file (.walSegment prior.installed.activeFirst)
        (report.append active (WAL.encode batch)).run (prior.files, report.initialMarker) = .ok (.ok ()) appended ∧
          (report.syncWal active).run appended = .ok (.ok ()) durable := by
  rcases report.cut with ⟨_, unchanged⟩ | ⟨appended, wrote, ⟨_, unchanged⟩ | ⟨durable, synced, _⟩⟩
  · exact .inl unchanged
  · exact .inl unchanged
  · exact .inr ⟨appended, durable, wrote, synced⟩

def projectMarkerBytes (checkpoint : Option ByteArray) :
    Option ByteArray → Except String DirectoryPublication.Bindings
  | none => .ok ⟨checkpoint, none⟩
  | some bytes => projectBinding ⟨checkpoint, none⟩ bytes

private theorem projectedMarker_member {checkpoint : Option ByteArray}
    {source : List (Option ByteArray)} {bindings : List DirectoryPublication.Bindings}
    (projected : source.mapM (projectMarkerBytes checkpoint) = .ok bindings)
    {pair : DirectoryPublication.Bindings} (member : pair ∈ bindings) :
    ∃ raw ∈ source, projectMarkerBytes checkpoint raw = .ok pair := by
  induction source generalizing bindings with
  | nil =>
    have empty := Except.ok.inj projected
    subst bindings
    simp at member
  | cons raw rest ih =>
    cases head : projectMarkerBytes checkpoint raw with
    | error => simp [List.mapM_cons, head, Bind.bind, Except.bind] at projected
    | ok value =>
      cases tail : rest.mapM (projectMarkerBytes checkpoint) with
      | error => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at projected
      | ok values =>
        have equal : value :: values = bindings := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using projected
        subst bindings
        rcases List.mem_cons.mp member with same | later
        · exact ⟨raw, List.mem_cons_self .., same.symm ▸ head⟩
        · obtain ⟨bytes, present, projected⟩ := ih tail later
          exact ⟨bytes, List.mem_cons_of_mem _ present, projected⟩

/-- After the WAL barrier, marker-only operations preserve the keeper
image left by that barrier, even if the marker callback is interrupted. -/
theorem InterruptedBatchMarkerPublication.keeperUnchangedOrWalSynced
    {directory : DiskDirectory} {prior : SegmentedWriterState} {batch : List WAL.Write}
    {next : Selection} {reached : FileImage × WalInodeImage}
    (report : InterruptedBatchMarkerPublication directory prior batch next reached)
    (writeKeepsKeeper : ∀ before (result : EStateM.Result report.Stop
        (FileImage × WalInodeImage) (Except IO.Error Unit)),
      (report.writeSlot report.markerHandle (next.slot * stride).toUInt64 next.encode).run before = result →
      (match result with | .ok _ after | .error _ after => after.1.keeper) = before.1.keeper)
    (syncKeepsKeeper : ∀ before,
      (report.syncSlot report.markerHandle).run before = .error report.stopped reached →
      reached.1.keeper = before.1.keeper) :
    reached.2 = report.initialMarker ∨
      ∃ appended durable,
        let active := directory.file (.walSegment prior.installed.activeFirst)
        (report.append active (WAL.encode batch)).run (prior.files, report.initialMarker) = .ok (.ok ()) appended ∧
          (report.syncWal active).run appended = .ok (.ok ()) durable ∧
          reached.1.keeper = durable.1.keeper := by
  rcases report.cut with ⟨_, unchanged⟩ | ⟨appended, wrote, ⟨_, unchanged⟩ | ⟨durable, synced, cut⟩⟩
  · exact .inl unchanged
  · exact .inl unchanged
  · refine .inr ⟨appended, durable, wrote, synced, ?_⟩
    rcases cut with writeCut | ⟨written, writeReturned, syncCut⟩
    · exact writeKeepsKeeper durable _ writeCut
    · exact (syncKeepsKeeper written syncCut).trans (writeKeepsKeeper durable _ writeReturned)

/-- If the marker changed, the first reboot sees exactly the keeper
bytes from the append, under the successful WAL barrier's persistence contract. -/
theorem InterruptedBatchMarkerPublication.survivingKeeperOfMarkerChange
    {directory : DiskDirectory} {prior : SegmentedWriterState} {batch : List WAL.Write}
    {next : Selection} {reached : FileImage × WalInodeImage}
    (report : InterruptedBatchMarkerPublication directory prior batch next reached)
    (writeKeepsKeeper : ∀ before (result : EStateM.Result report.Stop
        (FileImage × WalInodeImage) (Except IO.Error Unit)),
      (report.writeSlot report.markerHandle (next.slot * stride).toUInt64 next.encode).run before = result →
      (match result with | .ok _ after | .error _ after => after.1.keeper) = before.1.keeper)
    (syncKeepsKeeper : ∀ before,
      (report.syncSlot report.markerHandle).run before = .error report.stopped reached →
      reached.1.keeper = before.1.keeper)
    (walPersists : ∀ {appended durable},
      (report.syncWal (directory.file (.walSegment prior.installed.activeFirst))).run appended =
        .ok (.ok ()) durable → durable.1.keeper = appended.1.syncKeeper.keeper)
    (changed : reached.2 ≠ report.initialMarker)
    {bytes : Option ByteArray} (survives : bytes ∈ reached.1.keeper.crashImages) :
    ∃ appended durable,
      let active := directory.file (.walSegment prior.installed.activeFirst)
      (report.append active (WAL.encode batch)).run (prior.files, report.initialMarker) = .ok (.ok ()) appended ∧
        (report.syncWal active).run appended = .ok (.ok ()) durable ∧
        bytes = appended.1.keeper.active := by
  rcases report.keeperUnchangedOrWalSynced writeKeepsKeeper syncKeepsKeeper with unchanged |
    ⟨appended, durable, wrote, synced, keeper⟩
  · exact False.elim (changed unchanged)
  · have membership : bytes ∈ durable.1.keeper.crashImages := keeper ▸ survives
    rw [walPersists synced] at membership
    exact ⟨appended, durable, wrote, synced, by simpa [FileImage.syncKeeper] using membership⟩

/-- The guarded marked opener returns a session whose reads use the
same replay as the already selected client history. -/
theorem installsAfterAcquiredRecovery_replays
    (calls : CapturedAlignedCallbacks admission)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    {markerReads : CheckpointRunChunkReads} {payload : ByteArray}
    (file : HeldMetadataFile markerReads (directory.file .walBoundary) "WAL.commit"
      admission.view admission.root payload)
    (privateFile : file.calls.metadata.numLinks = 1)
    (available : PrefixChunksAvailableUntilEof payload (markerReads.readChunk file.calls.slot.description))
    (rewind : Nat → EStateM IO.Error Nat Unit) (rewound : rewind file.calls.slot.description 0 = .ok () 0)
    {selection : Selection} (decoded : decode payload = .ok selection)
    (syncMarker : KeeperDescriptorIdentity →
      EStateM IO.Error (WalInodeImage × (CensusDirectoryCache × CensusOpenState)) Unit)
    (finish : DiskDirectory → Plan → Nat → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    {after : CensusOpenState}
    (report : CapturedMarkedReadReports admission layout published false file.calls.inventory)
    (keeper : CapturedKeeperOpenReports report)
    {metadataRelease : System.FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease file.calls.inventory manifestDrops)
    (runs : CapturedRunReadCensus report (file.calls.inventory.afterDrops manifestDrops))
    {loaded : Option (PackedTable × UInt64)}
    (checkpointSelected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest loaded)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))
    (orderedLayout : WAL.OrdinalsFrom 1 history) {table : PackedTable}
    (replay : recoverSelected (loaded.getD (.empty, 0)).1 (WAL.encode history) = .ok table)
    {released : System.FilePath → List LockReferenceDrop}
    {required : List (Nat × IO.FS.Metadata)}
    {retains : DescriptorSlot → Prop}
    (seals : CapturedSealReadChainWith report released retains required report.listing.afterClose keeper.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ keeper.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ retry.image.later.visible, layout.range.through < start)
    (keepsMarker : retains file.calls.slot)
    (listingDrops : ∀ event ∈ report.listing.beforeOpen ++ report.listing.duringScan,
      event.removes file.calls.slot.reference = false)
    (keeperDrops : ∀ event ∈ keeper.duringRead, event.removes file.calls.slot.reference = false)
    {markerImage settledMarker : WalInodeImage}
    (markerInode : file.calls.inventory.inode file.calls.slot.description = markerImage.active)
    (markerBytes : payload = markerImage.visible markerImage.active)
    (markerSync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      (⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩ : KeeperDescriptorIdentity)
      markerImage (fun inode files => files.completeFileSync inode) (.ok () settledMarker))
    (sameBinding : ∀ inode ∈ markerImage.crashBindings, inode = markerImage.active)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settledMarker.crashBindings, bytes ∈ settledMarker.crashBytes inode)
    {reachedDirectory : DirectoryPublication.Image}
    (reachedDirectoryReport :
      projectRepairDirectory retry.image.directory (markerImage.visible markerImage.active) choices =
        .ok reachedDirectory)
    (syncReturned :
      let reached := (admission.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
        (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
        layout.keeper.bytes.size report.wal.keeper.calls.metadata.byteSize.toNat, keeper.afterRead, admission.held)
      syncMarker ⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩
        (markerImage, reached) =
        .ok () (settledMarker, reached.1, reached.2.1,
          { reached.2.2 with image := { reached.2.2.image with directory := reachedDirectory } }))
    (repair : CapturedFinalRepair calls checkpointSelected
      { admission.held with image := { retry.image with directory := settleMarker retry.image.directory selection } }
      keeper finish after)
    {bootstrapFirst writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory bootstrapFirst initial)
    (trace : SegmentedClientReadTrace directory bootstrapFirst start.writer allowCollection log reads writer prior)
    {batch : List WAL.Write}
    (acceptedCheckpoint : published.AcceptsVersioned prior.history.length.toUInt64
      (Boundary.CheckpointRepresentsPrefix prior.history) retry.image.directory.active.manifest)
    {interrupted firstPrepared : FileImage} {firstRepair : LockedFileState FileImage}
    (reportedBeforeBarrier : ReportedMarkerRetries interrupted firstPrepared ∨
      ∃ (crashPair : DirectoryPublication.Bindings) (crashKeeper : Option ByteArray) (crashLater : List Nat),
        crashPair ∈ interrupted.directory.crashImages ∧ crashKeeper ∈ interrupted.keeper.crashImages ∧
        crashLater ∈ interrupted.later.crashImages ∧
        ReportedMarkerRetries (interrupted.crash crashPair crashKeeper crashLater) firstPrepared)
    {checkpoint : Option ByteArray} {active : OrderedTwoSlot.Slot}
    {current next : Selection}
    (offset : current.slot = slotIndex active)
    (advanced : advance current (WAL.encode (prior.history ++ batch)).size = .ok next)
    {interruptedMarker : WalInodeImage}
    (writeCut : InterruptedBatchMarkerPublication directory prior batch next (interrupted, interruptedMarker))
    (writeKeepsKeeper : ∀ before (result : EStateM.Result writeCut.Stop
        (FileImage × WalInodeImage) (Except IO.Error Unit)),
      (writeCut.writeSlot writeCut.markerHandle (next.slot * stride).toUInt64 next.encode).run before = result →
      (match result with | .ok _ after | .error _ after => after.1.keeper) = before.1.keeper)
    (syncKeepsKeeper : ∀ before,
      (writeCut.syncSlot writeCut.markerHandle).run before = .error writeCut.stopped (interrupted, interruptedMarker) →
      interrupted.keeper = before.1.keeper)
    (walPersists : ∀ {appended durable},
      (writeCut.syncWal (directory.file (.walSegment prior.installed.activeFirst))).run appended =
        .ok (.ok ()) durable → durable.1.keeper = appended.1.syncKeeper.keeper)
    (accepted : decode (writeCut.initialMarker.visible writeCut.initialMarker.active) = .ok current)
    (completedCounts : List Nat) (inFlightCount : Nat)
    (transfersFit : completedCounts.sum + inFlightCount ≤ 40)
    (slotOutcome : ∀ bytes ∈ interruptedMarker.visible interruptedMarker.active ::
      interruptedMarker.crashBytes interruptedMarker.active,
      bytes.size = containerSize ∧
      (∀ position, bytes.get! position ≠ (writeCut.initialMarker.visible writeCut.initialMarker.active).get! position →
        next.slot * stride ≤ position ∧ position < next.slot * stride + (completedCounts.sum + inFlightCount)) ∧
      (decodeSlot bytes (slotIndex active.other) =
          decodeSlot (writeCut.initialMarker.visible writeCut.initialMarker.active) (slotIndex active.other) ∨
        decodeSlot bytes (slotIndex active.other) = none ∨ decodeSlot bytes (slotIndex active.other) = some next))
    {liveMarker : Option ByteArray} {crashMarkers : List (Option ByteArray)}
    (liveBytes : ∀ bytes, liveMarker = some bytes → bytes = interruptedMarker.visible interruptedMarker.active)
    (crashBytes : ∀ bytes, some bytes ∈ crashMarkers → bytes ∈ interruptedMarker.crashBytes interruptedMarker.active)
    (projectedLive : projectMarkerBytes checkpoint liveMarker = .ok interrupted.directory.active)
    (projectedCrash : crashMarkers.mapM (projectMarkerBytes checkpoint) = .ok interrupted.directory.crashImages)
    (observedFirst : firstPrepared.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    (firstBarrier : DelayedDirectorySync directory)
    (firstEffective : firstBarrier.outcome.effective = true)
    {firstOwner : LockOwners}
    (firstReached : firstBarrier.after
      ⟨{ firstPrepared with directory := settleMarker firstPrepared.directory selection }, firstOwner⟩ = firstRepair)
    {firstPlan : Plan} (preparedPlan : WalSegmentRepair.Prepared firstPrepared layout.target firstPlan)
    (reportedRetries : ReportedReopenPrefix directory layout.target.first firstRepair retry)
    (oldSize : current.frontier.toNat = (WAL.encode prior.history).size)
    (sameHistory : history = (prior.history ++ batch).take layout.range.through) :
    let opened : Reopened := ⟨table, (loaded.getD (.empty, 0)).2, selection.frontier, layout.keeper.first⟩
    let prepare := fun (resolved : DiskDirectory) (chosen : Selection) =>
      prepareBoundedMarkedFromReaders resolved (report.readCheckpointFromCensus metadataRelease runs.released)
        (fun _ => pure (some (Boundary.encode chosen.frontier)))
        (fun watermark length => readSelectedWithCachedExtents resolved watermark length report.scanWal
          report.inspectWal (readTemporarySeal report.reads released) keeper.readKeeperAt)
    let stabilize := fun handle => projectMarkerSync syncMarker markerImage handle
    ∃ session,
      calls.runWithMarked (fun resolved cache before =>
        match reopenAcquiredWith (acquireMarkerInCensus markerReads (resolved.file .walBoundary) rewind)
            (prepare resolved) stabilize (finish resolved) (cache, before) with
        | .ok (opened, _, _) (_, reached) => .ok opened reached
        | .error cause (_, reached) => .error cause reached) =
        .ok session after ∧
      InstalledClientReplay (log ++ [.uncertainBatch batch]) reads ((prior.history ++ batch).take layout.range.through)
        opened.installed session ∧ after.2.image.directory.active = layout.target.pair ∧
      after.2.image.kept = interrupted.kept ∧
      (interruptedMarker ≠ writeCut.initialMarker →
        ∀ bytes ∈ interrupted.keeper.crashImages,
          ∃ appended,
            (writeCut.append (directory.file (.walSegment prior.installed.activeFirst)) (WAL.encode batch)).run
              (prior.files, writeCut.initialMarker) = .ok (.ok ()) appended ∧ bytes = appended.1.keeper.active) ∧
      runBatchWriteWithInterruption directory writeCut.rows writeCut.lookup
        (fun _ _ _ => publish
          (writeCut.append (directory.file (.walSegment prior.installed.activeFirst)) (WAL.encode batch))
          (writeCut.syncWal (directory.file (.walSegment prior.installed.activeFirst)))
          (writeCut.writeSlot writeCut.markerHandle (next.slot * stride).toUInt64 next.encode)
          (writeCut.syncSlot writeCut.markerHandle) (writeCut.install writeCut.markerHandle next))
        (.ready prior.installed, ⟨(prior.files, writeCut.initialMarker), prior.owners⟩) =
        .error writeCut.stopped (.poisoned, ⟨(interrupted, interruptedMarker), prior.owners⟩) := by
  intro opened prepare stabilize
  obtain ⟨transferredAddresses, transfers⟩ := SlotWriteTransfers.ofCounts (next.slot * stride) 0
    (completedCounts ++ [inFlightCount]) (by simpa using transfersFit)
  simp only [Nat.zero_add, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at transfers
  have beforeBarrier : UnsettledRetries interrupted firstPrepared := by
    rcases reportedBeforeBarrier with direct | ⟨_, _, _, metadata, keeperBytes, laterNames, retries⟩
    · exact direct.refines
    · exact ((ReportedMarkerRetries.start.powerLoss metadata keeperBytes laterNames).trans retries).refines
  have finished := repair.returns
  have authorizedRepair : EffectTrace layout.target
      { firstPrepared with directory := settleMarker firstPrepared.directory selection } firstRepair.image := by
    rw [← firstReached, firstBarrier.after_effective firstEffective]
    exact .authorized
  have authorized := prepared_settleMarker preparedPlan selection observedFirst
  have validFirst := authorizedRepair.valid authorized.pair authorized.keeperPrefix authorized.newer
  have boundedRetries : BoundedReopenTrace directory (fun candidate => candidate = layout.target)
      firstRepair retry := by
    apply reportedRetries.refines
    intro current traced
    have valid := ((settledRetriesOfBoundedReopen traced).preserves validFirst).1
    obtain ⟨tail, read⟩ := valid.keeper.activeValid
    exact ⟨layout.target, ⟨layout.target.range.through, layout.target.first, current.image.later.visible,
      layout.target.trimmed ++ tail⟩, rfl, rfl,
      ⟨valid.selected, valid.keeper, valid.later, rfl, rfl, rfl, read⟩⟩
  have ⟨validRetry, keptRetry⟩ := (settledRetriesOfBoundedReopen boundedRetries).preserves validFirst
  have observed : retry.image.directory.active.walBoundary = some (Boundary.encode selection.frontier) := by
    rw [validRetry.selected, ← authorized.pair]
    simp [settleMarker, observedFirst]
  have effects := finished.2.ofSameAuthorizedImage (syncDirectory_afterSelectedMarker _ _ observed).symm
  have validAfter := effects.valid validRetry.selected validRetry.keeper validRetry.later
  obtain ⟨_, _, markerPayload, frontier, present, markerDecoded, count⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have samePayload := Option.some.inj (observed.symm.trans present)
  have sameFrontier : selection.frontier = frontier :=
    Except.ok.inj ((Boundary.decode_encode selection.frontier).symm.trans (samePayload ▸ markerDecoded))
  obtain ⟨acquisition, prepared, markerLive, sameInode⟩ := preparesFromHeldMarker file privateFile available rewind rewound report
    manifest runs checkpointSelected chronology selection decoded (sameFrontier.symm ▸ count) orderedLayout replay keeper
    seals offsets retained following later keepsMarker listingDrops keeperDrops
  obtain ⟨_, epoch, newSize, _, _⟩ := advance_fields advanced
  have newer : current.toRecord.epoch < next.toRecord.epoch := by
    change current.epoch.toNat < next.epoch.toNat
    omega
  have observations : ∀ pair ∈ interrupted.directory.active :: interrupted.directory.crashImages,
      pair = ⟨checkpoint, none⟩ ∨
        ∃ bytes, InterruptedSlotBytes (writeCut.initialMarker.visible writeCut.initialMarker.active) bytes active next ∧
          projectBinding ⟨checkpoint, none⟩ bytes = .ok pair := by
    intro pair member
    have candidate : ∃ raw, projectMarkerBytes checkpoint raw = .ok pair ∧
        ∀ bytes, raw = some bytes →
          bytes ∈ interruptedMarker.visible interruptedMarker.active :: interruptedMarker.crashBytes interruptedMarker.active := by
      rcases List.mem_cons.mp member with live | crash
      · subst pair
        exact ⟨liveMarker, projectedLive, fun bytes raw => (liveBytes bytes raw).symm ▸ List.mem_cons_self ..⟩
      · obtain ⟨raw, present, projection⟩ := projectedMarker_member projectedCrash crash
        exact ⟨raw, projection, fun bytes eq => List.mem_cons_of_mem _ (crashBytes bytes (eq ▸ present))⟩
    obtain ⟨raw, projection, source⟩ := candidate
    cases raw with
    | none => exact .inl (Except.ok.inj projection).symm
    | some bytes =>
      obtain ⟨size, attributed, decoded⟩ := slotOutcome bytes (source bytes rfl)
      have reported : ∀ position, bytes.get! position ≠
          (writeCut.initialMarker.visible writeCut.initialMarker.active).get! position →
          position ∈ transferredAddresses := by
        intro position changed
        apply (transfers.coversPrefix position).mpr
        simpa only [Nat.add_zero] using attributed position changed
      exact .inr ⟨bytes, transfers.interruptedBytes offset advanced size reported decoded, projection⟩
  have choicesBefore := interruptedMarker_retryChoices accepted offset newer observations
  have choice := (beforeBarrier.selectsOldOrNew checkpoint current.frontier next.frontier choicesBefore observedFirst).2
  have bytes := choice.imp (fun old => old ▸ oldSize) (fun all => all ▸ newSize)
  have chosenCount := sameFrontier.symm ▸ count
  have lengthChoice : layout.range.through = prior.history.length ∨
      layout.range.through = (prior.history ++ batch).length := by
    rw [chosenCount, WAL.encode_size, WAL.encode_size] at bytes
    unfold frameSize at bytes
    omega
  have whole : (prior.history ++ batch).take layout.range.through = prior.history ∨
      (prior.history ++ batch).take layout.range.through = prior.history ++ batch := by
    rcases lengthChoice with old | all
    · exact .inl (by rw [old, List.take_append_of_le_length (Nat.le_refl _), List.take_length])
    · exact .inr (all.symm ▸ List.take_length)
  have pending := trace.replaysUncertainSubmission start whole (sameHistory ▸ orderedLayout)
  let covered := history.take layout.range.watermark
  let suffix := history.drop layout.range.watermark
  have split : covered ++ suffix = history := List.take_append_drop ..
  have baseClock := Option.some.inj (checkpointSelected.watermark.symm.trans
    (DirectoryPublication.Bindings.walRange_accounting layout.decoded).1)
  obtain ⟨_, baseRefines, baseBounds, coveredBeforeBatch, baseHistory⟩ :=
    selectedCheckpoint_represents checkpointSelected acceptedCheckpoint
  rw [baseClock] at coveredBeforeBatch baseHistory
  have sameCovered : covered = prior.history.take layout.range.watermark := by
    rcases whole with old | all
    · exact congrArg (List.take layout.range.watermark) (sameHistory.trans old)
    · exact (congrArg (List.take layout.range.watermark) (sameHistory.trans all)).trans
        (List.take_append_of_le_length coveredBeforeBatch)
  rw [← sameCovered] at baseHistory
  have coveredLength : covered.length = (loaded.getD (.empty, 0)).1.committed.toNat := by
    have watermark := (DirectoryPublication.Bindings.walRange_accounting layout.decoded).2.1
    simp [covered, baseClock, ← layout.through, Nat.min_eq_left watermark]
  have played := (recoverSelected_encoded (loaded.getD (.empty, 0)).1 covered suffix
    (split.symm ▸ orderedLayout) coveredLength).symm.trans (by simpa only [split] using replay)
  obtain ⟨model, playedModel, refined⟩ := replay_refines baseRefines played
  have represented := sameHistory ▸ (split ▸ baseHistory.append playedModel)
  have effect : Storage.SyncHandleRouting.FsyncResult markerImage
      (markerImage.completeFileSync markerImage.active) true (.ok () settledMarker) := by
    have observed := markerSync.effect
    have target : markerSync.effectInode = markerImage.active := markerSync.sameInode.trans markerInode
    rw [target] at observed
    generalize markerSync.effective = effective at observed
    cases observed
    exact .completed
  have projected := stabilizesAfterKeeperRead report keeper markerLive (sameInode.trans markerInode)
    effect sameBinding (markerBytes ▸ decoded) (by rw [observed]; rfl) choices enumerated presence physical
  have recovery : reopenWith (prepare directory selection)
      (stabilize ⟨file.calls.slot.description, file.calls.inventory.inode file.calls.slot.description⟩)
      (finish directory) (admission.cache, file.calls.inventory, admission.held) =
        .ok opened (admission.cache, after) := by
    have sameDirectory := Except.ok.inj (reachedDirectoryReport.symm.trans projected)
    simp only [reopenWith_reports, prepare, opened, prepared, stabilize, projectMarkerSync, syncReturned, sameDirectory]
    erw [finished.1]
  have returned := installsAfterAcquiredRecovery calls marker
    (fun resolved => acquireMarkerInCensus markerReads (resolved.file .walBoundary) rewind)
    prepare stabilize finish acquisition recovery
  refine ⟨_, returned, pending.install rfl represented refined (recoverSelected_rowBounds baseBounds replay),
    validAfter.selected,
    effects.keepsSealed.trans (keptRetry.trans (authorizedRepair.keepsSealed.trans beforeBarrier.keepsSealed)),
    ?_, writeCut.stops⟩
  intro changed bytes survived
  obtain ⟨appended, _, wrote, _, exactBytes⟩ :=
    writeCut.survivingKeeperOfMarkerChange (fun before result eq => by
      cases result <;> exact writeKeepsKeeper before _ eq)
      syncKeepsKeeper walPersists changed survived
  exact ⟨appended, wrote, exactBytes⟩

/-- After marker stabilization, a longer keeper uses the shared native
replacement schedule once its first directory sync authorizes repair. -/
theorem reopensLongAfterCapturedPreparation
    {readStart : DescriptorInventory}
    (report : CapturedMarkedReadReports admission layout published false readStart)
    (calls : CapturedAlignedCallbacks admission)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (finish : CapturedLongKeeperFinish calls report vacant selected)
    {marker settled : WalInodeImage} {slot : DescriptorSlot}
    (live : slot ∈ finish.reader.afterRead.slots)
    (current : finish.reader.afterRead.inode slot.description = marker.active)
    (effect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync marker.active) true (.ok () settled))
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selection : Selection} (decoded : decode (marker.visible marker.active) = .ok selection)
    (bound : retry.image.directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode)
    {before : CensusDirectoryCache × CensusOpenState} {opened : Reopened}
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (prepared : prepare before =
      .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size)
        (admission.cache, finish.reader.afterRead, admission.held))
    (frontier : retry.image.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    (directorySync :
      let before := { admission.held with image :=
        { retry.image with directory := settleMarker retry.image.directory selection } }
      finish.authorization.fsync (admission.reached, admission.cached, 0) before =
        (finish.reader.directoryBarrierAfterDrops [report.wal.keeper.calls.slot.closeEvent]
          (finish.readAndClose.2.symm ▸ finish.authorization.directoryRetained) .completed).run before) :
    reopenWith prepare (stabilizeCapturedMarker (marker.visible marker.active) choices)
      (finish.repairAfterRead directory) before =
        .ok opened (admission.cache, finish.census, finish.settled) ∧
    EffectTrace layout.target { retry.image with directory := settleMarker retry.image.directory selection }
      finish.settled.image := by
  have authorized : finish.authorization.fsync (admission.reached, admission.cached, 0)
      { admission.held with image := { retry.image with directory := settleMarker retry.image.directory selection } } =
      .ok () { admission.held with image := retry.image.syncDirectory } := by
    simpa only [CapturedKeeperOpenReports.directoryBarrierAfterDrops, DescriptorInventory.delayedDirectorySync,
      DelayedDirectorySync.run, syncDirectory_afterSelectedMarker _ _ frontier] using directorySync
  obtain ⟨returned, effects⟩ := finish.repairAfterRead_returns_from _
    (syncDirectory_afterSelectedMarker _ _ frontier) authorized
  exact ⟨reopensAfterCapturedPreparation report finish.reader live current effect sameBinding decoded
    bound choices enumerated presence physical prepare prepared _ returned, effects⟩

/-- An aligned keeper with later segments uses the same ordered suffix
repair after the marker barrier reaches the common authorized image. -/
theorem reopensPrunedAfterCapturedPreparation
    {readStart : DescriptorInventory}
    (report : CapturedMarkedReadReports admission layout published false readStart)
    (calls : CapturedAlignedCallbacks admission)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (finish : CapturedPrunedAlignedFinish calls report vacant selected)
    {marker settled : WalInodeImage} {slot : DescriptorSlot}
    (live : slot ∈ finish.reader.afterRead.slots)
    (current : finish.reader.afterRead.inode slot.description = marker.active)
    (effect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync marker.active) true (.ok () settled))
    (sameBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    {selection : Selection} (decoded : decode (marker.visible marker.active) = .ok selection)
    (bound : retry.image.directory.active.walBoundary.isSome = true)
    (choices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : choices.map Prod.fst = retry.image.directory.crashImages)
    (presence : ∀ choice ∈ choices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physical : ∀ choice ∈ choices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settled.crashBindings, bytes ∈ settled.crashBytes inode)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first)
    {before : CensusDirectoryCache × CensusOpenState} {opened : Reopened}
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (prepared : prepare before =
      .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size)
        (admission.cache.remember (directory.file (.walSegment layout.keeper.first))
          (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0), finish.reader.afterRead, admission.held))
    (frontier : retry.image.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    (directorySync :
      let before := { admission.held with image :=
        { retry.image with directory := settleMarker retry.image.directory selection } }
      finish.authorization.fsync (admission.reached, admission.cached, 0) before =
        (finish.reader.directoryBarrier .completed).run before) :
    reopenWith prepare (stabilizeCapturedMarker (marker.visible marker.active) choices)
      (finish.repairActions directory) before =
        .ok opened (admission.cache, finish.census, finish.settled) ∧
    EffectTrace layout.target { retry.image with directory := settleMarker retry.image.directory selection }
      finish.settled.image := by
  have authorized : finish.authorization.fsync (admission.reached, admission.cached, 0)
      { admission.held with image := { retry.image with directory := settleMarker retry.image.directory selection } } =
      .ok () { admission.held with image := retry.image.syncDirectory } := by
    simpa only [CapturedKeeperOpenReports.directoryBarrier, CapturedKeeperOpenReports.directoryBarrierAfterDrops,
      DescriptorInventory.delayedDirectorySync,
      DelayedDirectorySync.run, syncDirectory_afterSelectedMarker _ _ frontier] using directorySync
  obtain ⟨returned, effects⟩ := finish.repairActions_returns_from _
    (syncDirectory_afterSelectedMarker _ _ frontier) authorized later
  exact ⟨reopensAfterCapturedPreparation report finish.reader live current effect sameBinding decoded
    bound choices enumerated presence physical prepare prepared _ returned, effects⟩

end CapturedPreparation

/-- The same retry-selected recovery explains the retained submissions and
fresh snapshot reads on the session installed by the shared open schedule. -/
theorem recoveredRetries_installedReads
    {initial prepared : FileImage} {target : Target}
    (beforeBarrier : UnsettledRetries initial prepared)
    {checkpoint : Option ByteArray} {before : ByteArray} {active : OrderedTwoSlot.Slot}
    {current : Selection} {next : Selection}
    (accepted : decode before = .ok current)
    (offset : current.slot = slotIndex active)
    {history batch : List Write}
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (observations : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      pair = ⟨checkpoint, none⟩ ∨
      ∃ bytes,
        InterruptedSlotBytes before bytes active next ∧
        projectBinding ⟨checkpoint, none⟩ bytes = .ok pair)
    (selected : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    {plan : WalSegmentRepair.Plan} (preparedPlan : WalSegmentRepair.Prepared prepared target plan)
    {image : WalSegmentImage}
    {table : PackedTable} {log : List DatabaseSubmissions}
    {directory : DiskDirectory} {descriptor nextRef : Nat} {unlock : DiskSession.UnlockReport}
    {openedFrom : LockedFileState FileImage}
    (readManifest : EStateM IO.Error FileImage (Option ByteArray))
    (readRunPrefix : System.FilePath → Nat → EStateM IO.Error FileImage ByteArray)
    (list : System.FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : System.FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readSeal : System.FilePath → Nat → EStateM IO.Error FileImage ByteArray)
    (readKeeper : System.FilePath → Nat → Nat → EStateM IO.Error FileImage ByteArray)
    (removeFile : System.FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : System.FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array System.FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : System.FilePath → System.FilePath → EStateM IO.Error FileImage Unit)
    (prior : DatabaseBatchRetention log history)
    (oldSize : current.frontier.toNat = (WAL.encode history).size)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : DiskSession.TryLockObserves openedFrom.owners directory (.ok true))
    {checkpointResult : Option (PackedTable × UInt64)}
    {durableRuns : CheckpointPublication.RunFiles} {checkpointReports : OpenPathReadReports}
    (checkpointSelected : SelectedIntegrityCheckpoint durableRuns target.pair.manifest checkpointResult)
    (sizes : WalSegmentRepair.SizedCheckpointRunReports directory checkpointReports
      target.pair.manifest durableRuns)
    (atRun : Nat → FileImage)
    (manifestSeen : readManifest openedFrom.image = .ok target.pair.manifest (atRun 0))
    (runReads : ∀ bytes manifest, target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest →
      ∀ index < manifest.header.runCount.toNat, ∀ payload,
        durableRuns manifest.header.generation index = some payload →
        readRunPrefix (directory.file (.run manifest.header.generation index)) payload.size (atRun index) =
          .ok payload (atRun (index + 1)))
    (layout : DiskSession.CanonicalKeeperLayout prepared ((history ++ batch).take target.range.through))
    (layoutTarget : layout.target = target)
    (catalog : WalSegmentRepair.CachedRetryReadInventory directory layout)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (extentReports : lstat = fun path => liftExcept (.ok (catalog.inventory.reports.lstat path) : Except IO.Error _))
    {listedState scannedState : FileImage}
    (listed : list directory.path (atRun (WalSegmentRepair.selectedRunCount target.pair.manifest)) = .ok catalog.entries listedState)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith directory lstat (catalog.entries.toList.map (·.fileName)) listedState =
      .ok extents scannedState)
    (selectedExtents : WalSegmentRepair.selectWalExtentsThrough extents (checkpointResult.getD (.empty, 0)).1.committed.toNat
      (selected.frontier.toNat / frameSize) = some (required, newer))
    {keeperMetadata : IO.FS.Metadata} {atKeeper : FileImage}
    (sealReads : WalSegmentRepair.CachedWalKeeperReached directory readSeal target.first
      keeperMetadata required scannedState atKeeper)
    (reportedSeal : ∀ entry ∈ required.dropLast, ∀ {before after bytes},
      readSeal (directory.file (.walSegment entry.1)) entry.2.byteSize.toNat before = .ok bytes after →
      prepared.kept entry.1 = some bytes)
    (keeperRead : readKeeper (directory.file (.walSegment target.first)) target.trimmed.size
      keeperMetadata.byteSize.toNat atKeeper = .ok target.trimmed prepared)
    {marker settledMarker : WalInodeImage}
    {markerReads : WalSegmentRepair.CheckpointRunChunkReads}
    {markerView : DiskSession.DirectoryReadNamespace} {markerRoot : DiskSession.DeviceInode}
    (markerFile : DiskSession.HeldMetadataFile markerReads (directory.file .walBoundary)
      "WAL.commit" markerView markerRoot (marker.visible marker.active))
    (markerPrivate : markerFile.calls.metadata.numLinks = 1)
    (atMarkerSync : DiskSession.DescriptorInventory)
    (markerSyncDrops : List DiskSession.LockReferenceDrop)
    (markerRetained : markerFile.calls.slot ∈ (atMarkerSync.afterDrops markerSyncDrops).slots)
    (sameObjects : atMarkerSync.inode = markerFile.calls.inventory.inode)
    (markerHandle : KeeperDescriptorIdentity)
    (markerIdentity : markerHandle = ⟨markerFile.calls.slot.description,
      markerFile.calls.inventory.inode markerFile.calls.slot.description⟩)
    (markerEffect : Storage.SyncHandleRouting.FsyncResult marker
      (marker.completeFileSync (atMarkerSync.inode markerHandle.description)) true (.ok () settledMarker))
    (markerCurrent : markerHandle.inode = marker.active)
    (markerBinding : ∀ inode ∈ marker.crashBindings, inode = marker.active)
    (markerAvailable : PrefixChunksAvailableUntilEof (marker.visible markerHandle.inode)
      (markerReads.readChunk markerFile.calls.slot.description))
    (markerAccepted : decode (marker.visible markerHandle.inode) = .ok selected)
    {stabilize : KeeperDescriptorIdentity → EStateM IO.Error FileImage Unit}
    (markerChoices : List (DirectoryPublication.Bindings × Option ByteArray))
    (enumerated : markerChoices.map Prod.fst = prepared.directory.crashImages)
    (presence : ∀ choice ∈ markerChoices, choice.2.isSome = choice.1.walBoundary.isSome)
    (physicalChoices : ∀ choice ∈ markerChoices, ∀ bytes, choice.2 = some bytes →
      ∃ inode ∈ settledMarker.crashBindings, bytes ∈ settledMarker.crashBytes inode)
    (stabilizeReport : stabilize markerHandle prepared =
      match projectRepairDirectory prepared.directory (marker.visible markerHandle.inode) markerChoices with
      | .ok directory => .ok () { prepared with directory }
      | .error cause => .error (IO.userError cause) prepared)
    (keeperExtent : keeperMetadata.byteSize.toNat = plan.keeperBytes.size)
    (settles : sync #[directory.path] { prepared with directory := settleMarker prepared.directory selected } =
      .ok () ({ prepared with directory := settleMarker prepared.directory selected } : FileImage).syncDirectory)
    (healthy : ∀ action state next,
      WalSegmentRepair.ReachesAction target
        ({ prepared with directory := settleMarker prepared.directory selected } : FileImage).syncDirectory
        plan.finishActions action state →
      state.effect target action = some next →
      WalSegmentRepair.performPaths directory plan removeFile throw write sync renameFile action state =
        .ok () next)
    (selectedRecovery : WalSegmentRecovery image target.pair target.range (history ++ batch)
      (checkpointResult.getD (.empty, 0)).1 layout.first table)
    (layoutBytes : ∀ segment ∈ layout.sealed, prepared.kept segment.first = some segment.bytes)
    {snapshot : UInt64} (retained : table.pins.floor ≤ snapshot)
    (within : snapshot.toNat ≤ target.range.through) :
    (∃ bytes, readPrefixUntilEofWith (IO.userError "invalid two-slot WAL marker length")
      (markerReads.readChunk markerFile.calls.slot.description) acquisitionLimit ByteArray.empty 0 =
        .ok bytes (min acquisitionLimit (marker.visible markerHandle.inode).size) ∧
      decode bytes = .ok selected) ∧
    DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take target.range.through) ∧
    ∃ after : FileImage,
    (∀ bytes, some bytes ∈ after.keeper.active :: after.keeper.crashImages →
      recoverMarkedWalSegments (checkpointResult.getD (.empty, 0)).1 selected.frontier
        (layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(target.first, bytes)]) =
        .ok (WAL.encode (((history ++ batch).take target.range.through).drop layout.first), table) ∧
      ∀ segment ∈ layout.sealed, after.kept segment.first = some segment.bytes) ∧
    ∃ retry : DiskSession.CanonicalKeeperLayout after ((history ++ batch).take target.range.through),
      retry.target = target ∧ retry.first = layout.first ∧
      retry.sealed = layout.sealed ∧ retry.keeper = layout.keeper ∧
      WalSegmentRepair.Prepared after target retry.plan ∧
    ∃ session final reference state pin pinned,
      DiskSession.runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (do
          let (opened, _, _) ← reopenAcquiredWith (acquireMarkerFromReports markerReads (directory.file .walBoundary))
            (fun selection => WalSegmentRepair.prepareBoundedMarkedFromReaders directory
              (readIntegrityCheckpointSized directory readManifest
                (fun path => liftExcept (WalSegmentRepair.checkpointRunSizeReport checkpointReports path)) readRunPrefix)
              (fun _ => pure (some (Boundary.encode selection.frontier)))
              (fun start length => WalSegmentRepair.readSelectedWithCachedExtents directory start length
                list lstat readSeal readKeeper))
            stabilize
            (fun bounded size =>
              WalSegmentRepair.finishBoundedMarkedOpen directory bounded size removeFile write sync renameFile)
          pure opened) openedFrom = .ok session final ∧
      (∃ opened,
        reopenAcquiredWith (acquireMarkerFromReports markerReads (directory.file .walBoundary))
          (fun selection => WalSegmentRepair.prepareBoundedMarkedFromReaders directory
            (readIntegrityCheckpointSized directory readManifest
              (fun path => liftExcept (WalSegmentRepair.checkpointRunSizeReport checkpointReports path)) readRunPrefix)
            (fun _ => pure (some (Boundary.encode selection.frontier)))
            (fun start length => WalSegmentRepair.readSelectedWithCachedExtents directory start length
              list lstat readSeal readKeeper))
          stabilize
          (fun bounded size =>
            WalSegmentRepair.finishBoundedMarkedOpen directory bounded size removeFile write sync renameFile)
          openedFrom.image = .ok (opened, markerHandle, selected) after ∧
        session.phase = .ready opened.installed) ∧
      final.image = after ∧ final.image.Ready target ∧
      EffectTrace target { prepared with directory := settleMarker prepared.directory selected } final.image ∧
      final.owners.Owns directory descriptor ∧
      session.sessionRef ∉ liveRefs ∧
      SnapshotWalReplay .empty ((history ++ batch).take target.range.through) reference ∧
      session.phase = .ready state ∧
      state.table.acquireAt snapshot = some (pin, pinned) ∧
      (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
      ∀ start stop, pinned.range pin.handle start stop =
        some (reference.table.range start stop snapshot) := by
  let base := (checkpointResult.getD (.empty, 0)).1
  let readWal := fun start length =>
    WalSegmentRepair.readSelectedWithCachedExtents directory start length list lstat readSeal readKeeper
  have logicalMarker : target.pair.walBoundary = some (Boundary.encode selected.frontier) :=
    congrArg DirectoryPublication.Bindings.walBoundary preparedPlan.pair.symm |>.trans observed
  have markerDescription : markerFile.calls.slot.description = markerHandle.description :=
    (congrArg KeeperDescriptorIdentity.description markerIdentity).symm
  have reachedInode : markerFile.calls.inventory.inode markerHandle.description = markerHandle.inode := by
    rw [markerIdentity]
  have markerLive : markerFile.calls.slot.reference ∈
      (atMarkerSync.afterDrops markerSyncDrops).references markerHandle.description :=
    ((atMarkerSync.afterDrops markerSyncDrops).mem_references).mpr
      ⟨markerFile.calls.slot, markerRetained, rfl, markerDescription⟩
  let markerSync := FsyncObservation.ofInventory atMarkerSync markerSyncDrops
    KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode markerHandle
    markerFile.calls.slot.reference markerLive (sameObjects.symm ▸ reachedInode) marker
    (fun inode (files : WalInodeImage) => files.completeFileSync inode) markerEffect
  obtain ⟨manifestWatermark, checkpointCovered, logicalMarkerBytes, length, binding, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have sameMarker := Option.some.inj (binding.symm.trans logicalMarker)
  have sameLength := Except.ok.inj ((sameMarker ▸ decoded).symm.trans (Boundary.decode_encode _))
  have aligned : selected.frontier.toNat % frameSize = 0 := by
    rw [← sameLength, absolute, Nat.mul_mod_left]
  have through : selected.frontier.toNat / frameSize = target.range.through := by
    rw [← sameLength, absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have sameWatermark : base.committed.toNat = target.range.watermark := by
    have selectedWatermark := checkpointSelected.watermark
    exact Option.some.inj (selectedWatermark.symm.trans manifestWatermark)
  have watermark : base.committed.toNat ≤ selected.frontier.toNat / frameSize := by
    rw [sameWatermark, through]
    exact checkpointCovered
  have layoutThrough : layout.range.through = target.range.through :=
    congrArg (fun t : Target => t.range.through) layoutTarget
  have absoluteLayout : selected.frontier.toNat = layout.range.through * frameSize := by
    rw [← sameLength, absolute, layoutThrough]
  obtain ⟨catalogExtents, catalogRequired, catalogScan, catalogSelection, catalogOrder, _⟩ :=
    catalog.scanSelected following (fun start member =>
      layoutThrough.symm ▸ preparedPlan.newer _ (List.mem_cons_self ..) start member) absoluteLayout
  have exactScan := scanned
  rw [extentReports, WalSegmentRepair.readWalSegmentExtentsWith_liftReports, catalogScan] at exactScan
  change EStateM.Result.ok catalogExtents listedState = _ at exactScan
  have extentsAgree := (EStateM.Result.ok.inj exactScan).1
  have catalogWatermark : layout.range.watermark = base.committed.toNat :=
    (congrArg (fun t : Target => t.range.watermark) layoutTarget).trans sameWatermark.symm
  rw [extentsAgree, catalogWatermark] at catalogSelection
  have selectionAgrees := Prod.mk.inj (Option.some.inj (selectedExtents.symm.trans catalogSelection))
  have laterNames : newer = prepared.later.visible := selectionAgrees.2
  have layoutOffsets : layout.sealed.map WalSegment.first = required.dropLast.map Prod.fst := by
    rw [selectionAgrees.1, List.map_dropLast, catalogOrder, List.map_append, List.map_cons, List.map_nil,
      List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
  have keeperSize : target.trimmed.size =
      (selected.frontier.toNat / frameSize - target.first) * frameSize := by
    rw [through]
    exact target.trimmedSize
  obtain ⟨tail, fullKeeper⟩ := preparedPlan.keeperPrefix.activeValid
  have full : plan.keeperBytes = target.trimmed ++ tail :=
    Option.some.inj (preparedPlan.keeperRead.symm.trans fullKeeper)
  have keeperCovers : target.trimmed.size ≤ keeperMetadata.byteSize.toNat := by
    rw [keeperExtent, full, ByteArray.size_append]
    exact Nat.le_add_right ..
  obtain ⟨earlier, earlierOffsets, earlierBytes, payloadRead⟩ :=
    sealReads.read_success (selected.frontier.toNat / frameSize) readKeeper
      (selected := fun offset bytes => prepared.kept offset = some bytes)
      (fun entry member {_before _after _bytes} seen => reportedSeal entry member seen) keeperSize keeperCovers keeperRead
  let sealed := layout.sealed.map (fun segment => (segment.first, segment.bytes))
  have sealedOffsets : sealed.map Prod.fst = required.dropLast.map Prod.fst := by
    simpa only [sealed, List.map_map, Function.comp_def] using layoutOffsets
  have sealedRead : ∀ file ∈ sealed, prepared.kept file.1 = some file.2 := by
    intro file member
    obtain ⟨segment, found, rfl⟩ := List.mem_map.mp member
    exact layoutBytes segment found
  have sameSeals := sealedReads_eq (earlierOffsets.trans sealedOffsets.symm) earlierBytes sealedRead
  rw [sameSeals] at payloadRead
  have walRead := WalSegmentRepair.readSelectedWithCachedExtents_stateful directory
    base.committed.toNat selected.frontier list lstat readSeal readKeeper
    ⟨aligned, watermark⟩ listed scanned selectedExtents payloadRead
  let payload := WAL.encode (((history ++ batch).take target.range.through).drop layout.first)
  have authorized := prepared_settleMarker preparedPlan selected observed
  obtain ⟨after, repaired, ready, authorizedRepair⟩ :=
    WalSegmentRepair.finishMarkedOpen_completes authorized directory removeFile write sync renameFile settles healthy
  have recovery : WalSegmentRecovery image after.directory.active target.range (history ++ batch)
      base layout.first table := ready.selected.symm ▸ selectedRecovery
  have retries : SettledRetries target after after := .start
  have ledger := recoveredRetries_retainUncertainBatch beforeBarrier accepted offset advanced
    observations selected observed authorizedRepair preparedPlan retries prior oldSize recovery
  obtain ⟨_, _, reference, replayed, _⟩ := ledger.2.1
  obtain ⟨pin, pinned, acquired, points, ranges⟩ := recovery.acquireReads replayed retained within
  have liveMarker := (retries.preservesSelectedMarker prepared selected observed authorizedRepair
    authorized.pair authorized.keeperPrefix authorized.newer (List.mem_cons_self ..)).1
  obtain ⟨actualMarker, actualLength, recoveredBytes, marked, decodedLength, _, samePayload, physicalReplay, _⟩ :=
    recovery.marked
  have sameMarker := Option.some.inj (marked.symm.trans liveMarker)
  have sameLength := Except.ok.inj ((sameMarker ▸ decodedLength).symm.trans (Boundary.decode_encode _))
  let segments := layout.sealed ++ [layout.keeper]
  have selectedChain : WalSegment.Chain ((history ++ batch).take target.range.through) layout.first segments :=
    layout.chain
  have keeperOffset : layout.keeper.first = target.first := congrArg Target.first layoutTarget
  have keeperBytes : layout.keeper.bytes = target.trimmed := congrArg Target.trimmed layoutTarget
  have selectedThrough : selected.frontier.toNat / frameSize = ((history ++ batch).take target.range.through).length := by
    exact through.trans ((congrArg (fun t : Target => t.range.through) layoutTarget).symm.trans layout.through)
  have checked : checkSelectedWalSegmentSpans (selected.frontier.toNat / frameSize)
      (sealed ++ [(target.first, plan.keeperBytes)]) = true := by
    rw [selectedThrough, full, ← keeperOffset, ← keeperBytes]
    exact layout.chain.checkSelectedSpans tail
  have boundedChecked := checkSelectedWalSegmentSpans_replaceKeeperBytes (after := target.trimmed)
    sealed (Nat.le_of_eq keeperSize.symm) checked
  have selectedSegments : segments.map (fun segment => (segment.first, segment.bytes)) =
      sealed ++ [(target.first, target.trimmed)] := by
    simp [segments, sealed, keeperOffset, keeperBytes]
  have selectedStart : ((sealed ++ [(target.first, target.trimmed)]).head?.map Prod.fst) = some layout.first := by
    rw [← selectedSegments]
    generalize segmentList : segments = parts at selectedChain ⊢
    generalize layout.first = first at selectedChain ⊢
    have nonempty : parts ≠ [] := by rw [← segmentList]; simp [segments]
    cases selectedChain with
    | endOfHistory => exact (nonempty rfl).elim
    | cons => rfl
  have concatenated : walSegmentPayloadBytes (sealed ++ [(target.first, target.trimmed)]) = payload := by
    have concatenate (parts : List WalSegment) :
        walSegmentPayloadBytes (parts.map (fun segment => (segment.first, segment.bytes))) =
          WalSegment.concatenate parts := by
      induction parts with
      | nil => rfl
      | cons segment rest ih =>
        change segment.bytes ++ walSegmentPayloadBytes
          (rest.map (fun part => (part.first, part.bytes))) = segment.bytes ++ WalSegment.concatenate rest
        rw [ih]
    rw [← selectedSegments, concatenate]
    exact selectedChain.concatenate_eq
  let laterBytes := WAL.encode (((history ++ batch).drop layout.first).drop (target.range.through - layout.first))
  have exactBytes : WalSegment.concatenate (image.afterWatermark target.range.watermark) =
      walSegmentPayloadBytes (sealed ++ [(target.first, target.trimmed)]) ++ laterBytes := by
    rw [recovery.historyRetained, concatenated]
    dsimp only [payload, laterBytes]
    rw [List.drop_take, ← WAL.encode_append, List.take_append_drop]
  have boundedReplay : recoverMarkedWalSegments base selected.frontier
      (sealed ++ [(target.first, target.trimmed)]) = .ok (payload, table) := by
    obtain ⟨entry, rest, files⟩ := List.exists_cons_of_ne_nil
      (show sealed ++ [(target.first, target.trimmed)] ≠ [] by simp)
    obtain ⟨startOffset, bytes⟩ := entry
    have start : startOffset = layout.first := by simpa [files] using selectedStart
    subst startOffset
    rw [files] at boundedChecked exactBytes ⊢
    rw [recoverMarkedWalSegments_eq_retained _ _ layout.first bytes rest laterBytes aligned boundedChecked,
      ← exactBytes, ← sameLength, physicalReplay, samePayload]
  have selectedReplay : recoverMarkedWalSegments base selected.frontier
      (sealed ++ [(target.first, plan.keeperBytes)]) = .ok (payload, table) := by
    rw [full] at checked ⊢
    exact (recoverMarkedWalSegments_removeKeeperTail base selected.frontier sealed target.first
      target.trimmed tail aligned (Nat.le_of_eq keeperSize.symm) checked).trans boundedReplay
  let readCheckpoint := readIntegrityCheckpointSized directory readManifest
    (fun path => liftExcept (WalSegmentRepair.checkpointRunSizeReport checkpointReports path)) readRunPrefix
  have checkpointRead := sizes.readExactWithState checkpointSelected readManifest readRunPrefix
    openedFrom.image atRun manifestSeen runReads
  have read := prepareSelected_stateful directory (Boundary.encode selected.frontier)
    selected.frontier (Boundary.decode_encode _) readCheckpoint readWal checkpointRead
    walRead boundedReplay
    (keeper := target.first) (bytes := target.trimmed) (by simp)
  let opened : WalSegmentRepair.Reopened :=
    ⟨table, (checkpointResult.getD (.empty, 0)).2, selected.frontier, target.first⟩
  have markerBound : prepared.directory.active.walBoundary.isSome = true := by simp [observed]
  have projected := reopenSync_projectsRepairDirectory markerSync markerCurrent markerBinding
    markerAccepted prepared.directory markerBound markerChoices enumerated presence physicalChoices
  have barrier : stabilize markerHandle prepared = .ok ()
      { prepared with directory := settleMarker prepared.directory selected } := by
    rw [stabilizeReport, projected]
  have keeperPrefixBytes : plan.keeperBytes.extract 0 plan.keeperSize = target.trimmed := by
    have size : plan.keeperSize = target.trimmed.size := by
      rw [WalSegmentRepair.Plan.keeperSize, preparedPlan.through, preparedPlan.start, target.trimmedSize]
    rw [full, size, ByteArray.extract_append_eq_left rfl]
  have boundedPlan : (⟨selected.frontier.toNat / frameSize, target.first, newer, target.trimmed⟩ :
      WalSegmentRepair.Plan) = { plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize } := by
    rw [through, ← preparedPlan.through, ← preparedPlan.start, laterNames, ← preparedPlan.names, keeperPrefixBytes]
  have boundedRepair : WalSegmentRepair.finishBoundedMarkedOpen directory
      ⟨selected.frontier.toNat / frameSize, target.first, newer, target.trimmed⟩
      keeperMetadata.byteSize.toNat removeFile write sync renameFile
      { prepared with directory := settleMarker prepared.directory selected } = .ok () after := by
    rw [boundedPlan, keeperExtent, WalSegmentRepair.finishBoundedMarkedOpen_eq_full
      directory plan preparedPlan.valid removeFile write sync renameFile]
    exact repaired
  have available : PrefixChunksAvailableUntilEof (marker.visible marker.active)
      (markerReads.readChunk markerFile.calls.slot.description) := by
    simpa only [markerCurrent] using markerAvailable
  obtain ⟨markerBytes, markerRead, markerDecode⟩ := decode_markerFromHeldDirectory markerFile available
  have decodedMarker : decode markerBytes = .ok selected :=
    markerDecode.trans (by simpa only [markerCurrent] using markerAccepted)
  have markerAcquired : acquireMarkerFromReports markerReads (directory.file .walBoundary) openedFrom.image =
      .ok (markerHandle, selected) openedFrom.image := by
    have held : (⟨markerFile.calls.slot.description,
        markerFile.calls.inventory.inode markerFile.calls.slot.description⟩ : KeeperDescriptorIdentity) =
        markerHandle := by
      cases markerHandle
      simp only [KeeperDescriptorIdentity.mk.injEq]
      exact ⟨markerDescription, markerDescription ▸ reachedInode⟩
    rw [acquireMarkerFromReports, acquireMarkerWithInventory_sharedReader]
    simp [acquireMarkerWithInventory, acquireMarkerWithInventoryUsing, checkPrivateRegularWith, markerFile.calls.stat,
      markerFile.calls.regular, markerPrivate, markerFile.calls.opened, markerRead,
      show (IO.FS.FileType.file == .file) = true from rfl,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, liftExcept,
      decodedMarker, held]
  have recovery : reopenWith
      (WalSegmentRepair.prepareBoundedMarkedFromReaders directory readCheckpoint
        (fun _ => pure (some (Boundary.encode selected.frontier))) readWal)
      (stabilize markerHandle)
      (fun bounded size =>
        WalSegmentRepair.finishBoundedMarkedOpen directory bounded size removeFile write sync renameFile)
      openedFrom.image = .ok opened after := by
    simp only [reopenWith_reports, read, barrier, boundedRepair]
    rfl
  obtain ⟨fullReopen, session, final, returned, installed, reached, owner, freshSession⟩ :=
    reopenAcquiredWith_installsReady (unlock := unlock)
      (prepare := fun selection => WalSegmentRepair.prepareBoundedMarkedFromReaders directory readCheckpoint
        (fun _ => pure (some (Boundary.encode selection.frontier))) readWal)
      (stabilize := stabilize)
      liveRefs fresh acquisition markerAcquired recovery
  have physical bytes survives := retries.replayUnchanged authorizedRepair authorized base sealed
    sealedRead logicalMarker (Boundary.decode_encode selected.frontier) checked (bytes := bytes) survives
  have layoutPlan : layout.plan = plan := by
    have throughEq : layout.range.through = plan.through :=
      (congrArg (fun t : Target => t.range.through) layoutTarget).trans preparedPlan.through.symm
    have bytesEq : layout.keeper.bytes ++ layout.tail = plan.keeperBytes :=
      Option.some.inj (layout.visible.symm.trans preparedPlan.keeperRead)
    have startEq := keeperOffset.trans preparedPlan.start.symm
    have namesEq := preparedPlan.names.symm
    change (⟨layout.range.through, layout.keeper.first, prepared.later.visible,
      layout.keeper.bytes ++ layout.tail⟩ : WalSegmentRepair.Plan) = plan
    rw [throughEq, startEq, namesEq, bytesEq]
  have layoutPrepared : WalSegmentRepair.Prepared prepared layout.target layout.plan := by
    rw [layoutTarget, layoutPlan]
    exact preparedPlan
  obtain ⟨retry, retryTarget, retryStart, retrySeals, retryKeeper, _, retryPrepared⟩ :=
    canonicalLayout_afterMarkerRetries layout selected observed layoutPrepared
      (layoutTarget.symm ▸ authorizedRepair) (layoutTarget.symm ▸ retries)
  have retryPlan : WalSegmentRepair.Prepared after target retry.plan := by
    simpa only [layoutTarget] using retryPrepared
  refine ⟨⟨markerBytes, (by simpa only [markerCurrent] using markerRead), decodedMarker⟩, ledger.1, after, ?_, retry, retryTarget.trans layoutTarget, retryStart,
    retrySeals, retryKeeper, retryPlan, session, final, reference,
    opened.installed, pin, pinned, returned, ⟨opened, fullReopen, installed⟩, reached, reached.symm ▸ ready,
    reached.symm ▸ authorizedRepair, owner, freshSession, replayed, installed, acquired, points, ranges⟩
  intro bytes survives
  obtain ⟨equalReplay, sealedBytes⟩ := physical bytes survives
  exact ⟨equalReplay.trans selectedReplay, fun segment found =>
    sealedBytes (segment.first, segment.bytes) (List.mem_map.mpr ⟨segment, found, rfl⟩)⟩

end Alvoki.WAL.TwoSlot
