import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
import Alvoki.Storage.Disk.WalTwoSlotReopenProjection
import Alvoki.Storage.Disk.BatchInterruptionDispatch

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

open WalSegmentRepair (FileImage Target EffectTrace)

/-- The retry trace supplies the actual frontier used by the recovered
table. The retained client history follows from that retry-selected marker. -/
theorem recoveredRetries_retainUncertainBatch
    {initial prepared firstRepair after : FileImage} {target : Target}
    (beforeBarrier : UnsettledRetries initial prepared)
    (checkpoint : Option ByteArray) (old new : UInt64)
    (choices : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      pair.manifest = checkpoint ∧ (pair.walBoundary = none ∨
        pair.walBoundary = some (Boundary.encode old) ∨ pair.walBoundary = some (Boundary.encode new)))
    (selected : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (authorizedRepair : EffectTrace target
      { prepared with directory := settleMarker prepared.directory selected } firstRepair)
    (targetPair : (settleMarker prepared.directory selected).active = target.pair)
    (keeper : prepared.keeper.Valid target.Accepts)
    (later : prepared.later.Beyond target.range.through)
    (retries : SettledRetries target firstRepair after)
    {image : WalSegmentImage} {range : MarkedWalRange} {history batch : List Write}
    {base table : PackedTable} {first : Nat} {log : List DatabaseSubmissions}
    (prior : DatabaseBatchRetention log history)
    (oldSize : old.toNat = (WAL.encode history).size)
    (newSize : new.toNat = (WAL.encode (history ++ batch)).size)
    (recovery : WalSegmentRecovery image after.directory.active range (history ++ batch) base first table) :
    DatabaseBatchRetention (log ++ [.uncertainBatch batch]) ((history ++ batch).take range.through) ∧
    ∃ model, table.Refines model ∧ RepresentsWalHistory ((history ++ batch).take range.through) model := by
  obtain ⟨_, binding, choice, _⟩ := retries_preservePublishedFrontier beforeBarrier checkpoint old new
    choices selected observed authorizedRepair targetPair keeper later retries (List.mem_cons_self ..)
  rcases choice with oldFrontier | newFrontier
  · exact recoveredBatch_retains prior recovery binding (.inl (oldFrontier ▸ oldSize))
  · exact recoveredBatch_retains prior recovery binding (.inr (newFrontier ▸ newSize))

end Alvoki.WAL.TwoSlot
