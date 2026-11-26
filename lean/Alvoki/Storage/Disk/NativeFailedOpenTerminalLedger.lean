import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeSourceLedger

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The last instruction of a nonempty failed-open prefix returned its
diagnostic at the prefix's final heap. The preceding failures determine
the heap where this call started. -/
theorem RawMarkedOpenInterpreter.FailedCalls.lastError
    {heap stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {first reached : heap} {returns : List (FilePath × IO.Error)}
    (calls : source.FailedCalls first returns reached) (nonempty : returns ≠ []) :
    ∃ earlier input diagnostic issued,
      returns = earlier ++ [(input, diagnostic)] ∧
      source.FailedCalls first earlier issued ∧ source.openTable input issued = .error diagnostic reached := by
  cases calls with
  | empty => exact (nonempty rfl).elim
  | next prior input returned => exact ⟨_, input, _, _, rfl, prior, returned⟩

/-- A failed open can be the last instruction of a source prefix. The
same fail-only fold that prepares a later open selects the history at
the terminal heap. The write contributes one uncertain submission to
the preceding client ledger. The errors contribute no writes or reads. -/
theorem NativeExecutionPosition.refinesFailedOpenTerminalLedger
    {heap stream : Type} {source : RawMarkedOpenInterpreter heap stream}
    {origin current : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events current)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch current.ready.state.writer.installed.table rows = some (batch, table))
    (fits : current.ready.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget current.ready.state.writer.history batch
      current.ready.state.writer.wal.active.first target)
    {view : OpenCloseHeapView heap FileImage} {first reached : heap}
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {firstOffset : Nat} (covers : ∀ offset ∈ current.ready.state.writer.wal.segments.map WalSegment.first,
      firstOffset ≤ offset)
    (initial : RawOpenRetryTrace.SelectedEntry view current.ready.state target
      (fun atHeap => (storage atHeap).files.names) visible first)
    (entry : RawOpenRetryTrace.RecoveryObservations view current.ready.state target storage visible firstOffset
      (current.history ++ batch).length first)
    {returns : List (FilePath × IO.Error)} (attempts : source.FailedCalls first returns reached)
    (nonempty : returns ≠ [])
    (effects : RawOpenRetryTrace.SelectedEffects view source first target
      (fun atHeap => ⟨(storage atHeap).files.names, fun inode => [visible atHeap inode]⟩)
      current.ready.state.selectedRetryPath
      (RawOpenRetryTrace.RecoveryObservations view current.ready.state target storage visible firstOffset
        (current.history ++ batch).length) attempts) :
    (∀ event ∈ events, event.uncertainBatchWhole) ∧
    ∃ earlier input diagnostic issued,
      returns = earlier ++ [(input, diagnostic)] ∧ source.FailedCalls first earlier issued ∧
      source.openTable input issued = .error diagnostic reached ∧
      ∃ plan : current.ready.SelectedWritePlan batch target (view.files reached).image,
        plan.layout.VisibleWal current.ready.state.session.directory (storage reached).files.names (visible reached) ∧
        RawOpenRetryTrace.SelectedEntry view current.ready.state target
          (fun atHeap => (storage atHeap).files.names) visible reached ∧
        current.ready.state.SelectedRetryDurability target (storage reached) ∧
        RawOpenRetryTrace.LaterWalAt view current.ready.state.session.directory target
          (fun atHeap => (storage atHeap).files.names) reached ∧
        let priorHistory := origin.history ++ events.flatMap NativeExecutionEvent.writes
        let submissions := (origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch]
        let reads := origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads
        (plan.history = priorHistory ∨ plan.history = priorHistory ++ batch) ∧
        PendingClientReplay submissions reads plan.history ∧
        ∀ read ∈ reads, read.BoundedBy plan.history.length := by
  obtain ⟨earlier, input, diagnostic, issued, reported, previous, returned⟩ := attempts.lastError nonempty
  obtain ⟨plan, physical, selected, _, _, reachedDurable, suffix⟩ :=
    current.ready.preparesDurableVisibleWriteRetry prepared fits admitted storage visible covers initial entry effects
  refine ⟨prior.whole, earlier, input, diagnostic, issued, reported, previous, returned, plan,
    physical, selected, reachedDurable, suffix, ?_, ?_, ?_⟩
  · simpa only [← prior.history] using plan.allowed
  · simpa only [← prior.submissions, ← prior.reads] using plan.pending
  · simpa only [← prior.reads] using plan.bounded

end Alvoki.Storage.DiskSession
