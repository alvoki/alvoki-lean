import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativeSelectedWriteReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The reopened ready position yields the existing replay event directly
from the selected old-or-whole history and the carried snapshot ledger. -/
theorem NativeReadPosition.SelectedWritePlan.ledgerAfterReopen
    {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image)
    (next : NativeReadPosition plan.history (log ++ [.uncertainBatch batch])) (kept : next.reads = current.reads)
    (request : WriteRequest) (input : FilePath) (cause : IO.Error) :
    ∃ retained, (⟨history, log, current⟩ : NativeExecutionPosition).LedgerSuffix
      [.uncertainWriteCrashRecovered request input cause batch retained]
      ⟨plan.history, log ++ [.uncertainBatch batch], next⟩ := by
  obtain ⟨retained, allowed, selected⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = batch) ∧ plan.history = history ++ retained := by
    rcases plan.allowed with previous | whole
    · exact ⟨[], .inl rfl, by simpa using previous⟩
    · exact ⟨batch, .inr rfl, whole⟩
  refine ⟨retained, ?_, rfl, ?_, ?_⟩
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using selected
  · simpa [NativeExecutionEvent.reads] using kept
  · intro event member
    obtain rfl := List.mem_singleton.mp member
    exact allowed

/-- A return from the source opener that keeps the old history, with the
uncertain submission and the existing snapshot observations in its ledger. -/
def NativeReadPosition.ReopenedOldLedger
    {heap : Type} {prior : List WAL.Write} {log : List DatabaseSubmissions}
    (current : NativeReadPosition prior log) (batch : List WAL.Write)
    (request : WriteRequest) (input : FilePath) (cause : IO.Error)
    (returned : EStateM.Result IO.Error heap DiskTable) : Prop :=
    ∃ (next : NativeReadPosition prior (log ++ [.uncertainBatch batch]))
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      returned = .ok handle.table start.reached ∧
      start.current = ⟨prior, log ++ [.uncertainBatch batch], next⟩ ∧
      (⟨prior, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        [.uncertainWriteCrashRecovered request input cause batch []] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session

/-- At the old marker the selected history has the original length,
even if additional WAL bytes survived. The very table returned by the
source open carries that history and records the uncertain submission. -/
theorem NativeReadPosition.SelectedWriteRecovery.replaysOldTarget
    {heap stream : Type} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
    {returns : List (FilePath × IO.Error)}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {prior : List WAL.Write} {log : List DatabaseSubmissions} {batch : List WAL.Write}
    {current : NativeReadPosition prior log} {first reached : heap}
    {source : RawMarkedOpenInterpreter heap stream}
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    {vacant : TryLockObserves (view.files reached).owners current.state.session.directory (.ok true)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (recovered : current.SelectedWriteRecovery (returns := returns) (input := input) (view := view)
      (batch := batch) (target := current.state.writer.target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names visible first vacant get set ptrEq)
    (request : WriteRequest) (cause : IO.Error) :
    current.ReopenedOldLedger batch request input cause (source.openTable input reached) := by
  obtain ⟨_, _, plan, opening, raw, _, _, _, _, _, _, _, returned⟩ := recovered
  obtain ⟨_, next, _, handle, start, _, _, success, atStart, reads, _⟩ := returned
  obtain ⟨valid, original, _⟩ := current.readPrefix.refines
  have oldLength := valid.retained.resumed.through.trans (congrArg List.length original)
  have sameLength : plan.history.length = prior.length :=
    plan.layout.through.symm.trans ((congrArg (fun target : Target => target.range.through) plan.targetEq).trans oldLength)
  have old : plan.history = prior := by
    rcases plan.allowed with kept | whole
    · exact kept
    · have empty : batch = [] := by
        have count := (congrArg List.length whole).symm.trans sameLength
        simp only [List.length_append] at count
        exact List.length_eq_zero_iff.mp (by omega)
      simpa only [empty, List.append_nil] using whole
  let installed : NativeReadPosition prior (log ++ [.uncertainBatch batch]) := old ▸ next
  have castPosition {before after : List WAL.Write} (eq : before = after)
      (ready : NativeReadPosition before (log ++ [.uncertainBatch batch])) :
      (⟨before, log ++ [.uncertainBatch batch], ready⟩ : NativeExecutionPosition) =
        ⟨after, log ++ [.uncertainBatch batch], eq ▸ ready⟩ := by
    cases eq
    rfl
  have castReads {before after : List WAL.Write} (eq : before = after)
      (ready : NativeReadPosition before (log ++ [.uncertainBatch batch])) :
      (eq ▸ ready : NativeReadPosition after (log ++ [.uncertainBatch batch])).reads = ready.reads := by
    cases eq
    rfl
  have position := atStart.trans (castPosition old next)
  have kept := (castReads old next).trans reads
  refine ⟨installed, handle, start, success, position, ?_, start.current.ready.readPrefix.guardedReplay⟩
  rw [position]
  refine ⟨by simp [NativeExecutionEvent.writes], rfl, ?_, ?_⟩
  · simpa [NativeExecutionEvent.reads] using kept
  · intro event member
    obtain rfl := List.mem_singleton.mp member
    exact .inl rfl

end Alvoki.Storage.DiskSession
