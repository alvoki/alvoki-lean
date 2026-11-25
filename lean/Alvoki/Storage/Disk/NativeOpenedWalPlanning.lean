import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeWalPlanningQuery

namespace Alvoki.Storage.DiskSession

/-- Interpret the phase read on the actual opened reference before running
the observationally read-only planner with the reached file reports. -/
def WalCollectionReads.runOnOpenPhase {heap : Type}
    (calls : WalCollectionReads) (opened : NativeOpenedHandle heap) :
    EStateM IO.Error heap (List Nat) := do
  let state ← (← opened.get opened.phase).installed
  match calls.plan opened.directory state with
  | .ok offsets => pure offsets
  | .error cause => throw cause

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A successful plan or a reported extent error reads the same phase cell
and leaves the same heap, table, pins and client history available. The
file reports determine the ordered plan and account for temporary closes. -/
theorem NativeOpenedPosition.plansWalCollection
    (start : NativeOpenedPosition opened)
    (observed : NativeWalPlanningObservation start.current.ready.state) :
    opened.table.UsesOpenWalPlanningSchedule start.current.ready.state.session.directory opened.phase ∧
    observed.calls.runOnOpenPhase opened start.reached = (match observed.extents.result with
      | .ok offsets => .ok offsets start.reached
      | .error cause => .error cause start.reached) ∧
    NativeExecutionStep start.current (.walCollectionPlan observed.extents.result) start.current ∧
    observed.read.manifest.Released ∧ observed.read.marker.Released ∧ observed.read.listing.Custody ∧
    observed.read.listing.afterClose = start.current.ready.state.census ∧
    (∀ offsets, observed.extents.result = .ok offsets →
      offsets = start.current.ready.state.writer.wal.collectionOffsets ∧ offsets.Pairwise (· < ·) ∧
        ∀ first, first ∈ offsets ↔ ∃ segment ∈ start.current.ready.state.writer.wal.sealed,
          start.current.ready.state.writer.wal.Eligible segment ∧ segment.first = first) := by
  obtain ⟨returned, manifest, marker, listing, census, valid, _⟩ :=
    start.current.ready.plansWalCollection observed
  refine ⟨start.uses.planWalCollection, ?_, .planWalCollection start.current observed returned,
    manifest, marker, listing, census, fun _ success => observed.extents.eligibleInOrder valid success⟩
  have loaded := opened.phaseEffects.reads start.reached opened.phase _ start.stored
  have plan := observed.extents.plans valid
  rw [start.directory] at plan
  simp only [WalCollectionReads.runOnOpenPhase, Bind.bind, EStateM.bind, loaded, valid.phase,
    Phase.installed, Pure.pure, EStateM.pure, plan]
  cases observed.extents.result <;> rfl

end Alvoki.Storage.DiskSession
