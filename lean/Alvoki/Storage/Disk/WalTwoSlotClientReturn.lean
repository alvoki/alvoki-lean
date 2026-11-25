import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
import Alvoki.Storage.Disk.WalTwoSlotReopenProjection
import Alvoki.Storage.Disk.BatchInterruptionDispatch
import Alvoki.Storage.Disk.SyncHandleEffects

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

/-- If the positional marker write fails after the WAL barrier, the
client receives commit-unknown with exactly the reached file state.
Neither the marker barrier nor installation runs. -/
theorem prepared_write_slotError {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit)
    {files appended durable reached : σ} {cause : IO.Error}
    (wrote : append files = .ok () appended)
    (walBarrier : syncWal appended = .ok () durable)
    (failed : writeSlot durable = .error cause reached) :
    DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
        .error (.commitUnknown cause) (.poisoned, reached) := by
  rw [prepared_write_reports, publish_reports]
  simp only [wrote, walBarrier, failed]

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
  obtain ⟨inode, bound, stored⟩ := survived
  have live : inode = image.active := by
    exact binding inode (by simpa [state, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync] using bound)
  simpa [state, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, live] using stored

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
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
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
    have exactBytes := syncedInode_survivor sync current sameBinding (physical bytes rfl)
    have decoded : decode bytes = .ok selected := by rw [exactBytes, ← current]; exact observed
    change projectBinding before bytes = _
    rw [projectBinding_decodes decoded]
    cases boundary : before.walBoundary <;> simp_all

/-- Map physical outcomes to the complete logical crash list after the
reopen barrier. The list preserves each manifest and marker-presence choice. -/
theorem reopenSync_projectsCrashBindings
    {marker settled : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle marker (fun inode files => files.completeFileSync inode) (.ok () settled))
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
    have head := reopenSync_projectsCrashBinding sync current sameBinding observed choice.1
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
  have crashes := reopenSync_projectsCrashBindings sync current sameBinding observed choices presence physical
  have active := projectBinding_decodes (visible := directory.active) observed
  have activeMap : directory.active.walBoundary.map (fun _ => Boundary.encode selected.frontier) =
      some (Boundary.encode selected.frontier) := by
    cases boundary : directory.active.walBoundary <;> simp_all
  rw [enumerated] at crashes
  simp only [projectRepairDirectory, Bind.bind, Except.bind, active, crashes, Pure.pure, Except.pure]
  simp [settleMarker, activeMap]

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
  have count : range.through = history.length ∨ range.through = (history ++ batch).length := by
    rw [recoveredFrontier_count recovery selected, WAL.encode_size, WAL.encode_size] at whole
    unfold frameSize at whole
    omega
  refine ⟨?_, recovery.refines⟩
  rcases count with old | new
  · rw [old, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    simpa using (DatabaseBatchRetention.append (entry := .uncertainBatch batch)
      (suffix := []) prior (Or.inl rfl))
  · rw [new, List.take_length]
    exact DatabaseBatchRetention.append (entry := .uncertainBatch batch) prior (Or.inr rfl)

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

/-- A machine stop during the reopen barrier never enters WAL repair.
Whether the marker sync took effect or had yet to take effect, the
surviving file choices start another attempt in the same retry lineage. -/
theorem reopenSyncInterrupted_preservesRetry {stop : Type}
    {initial before prepared reached : FileImage}
    (prepare : ExceptT IO.Error (EStateM stop FileImage)
      (WalSegmentRepair.Plan × WalSegmentRepair.Reopened × Nat))
    (stabilize : ExceptT IO.Error (EStateM stop FileImage) Unit)
    (finish : WalSegmentRepair.Plan → Nat → ExceptT IO.Error (EStateM stop FileImage) Unit)
    {plan : WalSegmentRepair.Plan} {opened : WalSegmentRepair.Reopened} {size : Nat}
    {stopped : stop} (read : prepare.run before = .ok (.ok (plan, opened, size)) prepared)
    (cut : stabilize.run prepared = .error stopped reached)
    (prior : UnsettledRetries initial prepared) (selected : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (effect : reached = prepared ∨
      reached = { prepared with directory := settleMarker prepared.directory selected })
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {names : List Nat}
    (metadata : pair ∈ reached.directory.crashImages)
    (keeper : bytes ∈ reached.keeper.crashImages) (later : names ∈ reached.later.crashImages) :
    (reopenWith prepare stabilize finish).run before = .error stopped reached ∧
      UnsettledRetries initial (reached.crash pair bytes names) := by
  constructor
  · change prepare before = .ok (.ok (plan, opened, size)) prepared at read
    change stabilize prepared = .error stopped reached at cut
    simp [reopenWith, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, read, cut]
  · apply UnsettledRetries.crash _ metadata keeper later
    rcases effect with rfl | rfl
    · exact prior
    · exact .settle prior selected observed

/-- The descriptor's error report determines which retry image is
reachable. A reported error after persistence settles only the marker. -/
theorem reopenSyncError_preservesRetry
    {directory : DiskDirectory} {descriptor nextRef : Nat} (unlock : DiskSession.UnlockReport)
    {initial prepared reached : FileImage} {before : LockedFileState FileImage}
    (prior : UnsettledRetries initial prepared) (selection : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    {prepare : EStateM IO.Error FileImage (WalSegmentRepair.Plan × WalSegmentRepair.Reopened × Nat)}
    {stabilize : EStateM IO.Error FileImage Unit}
    {finish : WalSegmentRepair.Plan → Nat → EStateM IO.Error FileImage Unit}
    {plan : WalSegmentRepair.Plan} {opened : WalSegmentRepair.Reopened} {size : Nat} {cause : IO.Error}
    (read : prepare before.image = .ok (plan, opened, size) prepared)
    (barrier : stabilize prepared = .error cause reached)
    {physical after : WalInodeImage} {handle : KeeperDescriptorIdentity}
    (sync : FsyncObservation KeeperDescriptorIdentity.description KeeperDescriptorIdentity.inode
      handle physical (fun inode files => files.completeFileSync inode) (.error cause after))
    (project : WalInodeImage → FileImage)
    (priorImage : project physical = prepared)
    (reachedImage : project after = reached)
    (syncImage : project (physical.completeFileSync handle.inode) =
      { prepared with directory := settleMarker prepared.directory selection }) :
    ∃ error final,
      DiskSession.runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (reopenWith prepare stabilize finish) before = .error error final ∧
      UnsettledRetries initial final.image ∧ final.image.keeper = prepared.keeper := by
  apply reopenWith_markerSyncError_retries unlock prior selection observed read barrier
  have effect := sync.effect
  rw [sync.sameInode] at effect
  generalize sync.effective = effective at effect
  cases effect with
  | errorBefore => exact .inl (reachedImage.symm.trans priorImage)
  | errorAfter => exact .inr (reachedImage.symm.trans syncImage)

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
    ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model := by
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
  rcases choice with oldFrontier | newFrontier
  · exact recoveredBatch_retains prior recovery binding (.inl (oldFrontier ▸ oldSize))
  · exact recoveredBatch_retains prior recovery binding (.inr (newFrontier ▸ newSize))

end Alvoki.WAL.TwoSlot
