import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotPin SnapshotTable Table)

/-- Interpret the native phase read and pointer comparison with their
reported results. A successful lookup or range returns the same session. -/
def SegmentedSession.runSnapshotRead (sameSession : Bool) (read : PackedTable → Option α) :
    EStateM IO.Error SegmentedSession (Option α) := fun session =>
  readSnapshotWith (m := EStateM IO.Error SegmentedSession) session.phase.installed (pure sameSession) read session

/-- A local read at an active intermediate pin agrees with the same
snapshot in the final abstract replay. The suffix starts at the exact
ready writer that served the read under the observed lock description.
Its later writes cannot affect that earlier sequence. -/
theorem SegmentedBatchDatabaseTrace.guardedReadsBeforeSuffix
    {session : SegmentedSession} {before : SegmentedWriterState}
    (suffix : SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection log descriptor last)
    (ready : before.RetainedReady session.directory session.descriptor)
    (phase : session.phase = .ready before.installed)
    {reference : SnapshotTable UInt64} (replayed : SnapshotWalReplay .empty last.history reference)
    {pin : SnapshotPin} (active : pin ∈ before.installed.table.pins.active)
    {issuer : Nat} (localToken : issuer = session.sessionRef) {sameSession : Bool}
    (compared : sameSession = decide (issuer = session.sessionRef)) :
    (∀ key, session.runSnapshotRead sameSession (fun table => table.lookup pin.handle key) =
      .ok (some (reference.table.lookup key pin.sequence)) session) ∧
    ∀ lo hi, session.runSnapshotRead sameSession (fun table => table.range pin.handle lo hi) =
      .ok (some (reference.table.range lo hi pin.sequence)) session := by
  obtain ⟨_, retained, history, _⟩ := suffix.preservesRetained ready
  rw [history] at replayed
  obtain ⟨earlier, prefixReplay, continued⟩ := replayed.split
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  obtain ⟨lookup, range⟩ := represented.packedPinnedReads refined prefixReplay active
  have clock : model.committed = earlier.committed := by
    apply UInt64.toNat_inj.mp
    rw [represented.committed_count, prefixReplay.committed_count]
    exact (Nat.zero_add _).symm
  have supported : pin.sequence ≤ earlier.committed :=
    clock ▸ model.pins_committed pin (refined.pins ▸ active)
  have stable := continued.visibleEntry_before_suffix supported
  have matched : sameSession = true := compared.trans (decide_eq_true localToken)
  rw [matched]
  constructor
  · intro key
    rw [SegmentedSession.runSnapshotRead, phase]
    change EStateM.Result.ok (before.installed.table.lookup pin.handle key) session = _
    rw [lookup, Table.lookup_eq_visibleEntry, Table.lookup_eq_visibleEntry, stable key]
  · intro lo hi
    rw [SegmentedSession.runSnapshotRead, phase]
    change EStateM.Result.ok (before.installed.table.range pin.handle lo hi) session = _
    rw [range, Table.range_of_visibleEntry_eq lo hi _ stable]

/-- One final replay explains every local pin read at the reached earlier
writer, including sequences that are outside the final writer's floor. -/
theorem SegmentedBatchDatabaseTrace.intermediateSnapshotRefinement
    {session : SegmentedSession} {initial before : SegmentedWriterState}
    (prior : SegmentedBatchDatabaseTrace session.directory initialDescriptor initial allowCollection priorLog
      session.descriptor before)
    (initialReady : initial.RetainedReady session.directory initialDescriptor)
    (suffix : SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection log descriptor last)
    (phase : session.phase = .ready before.installed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ before.installed.table.pins.active, ∀ issuer, issuer = session.sessionRef →
        ∀ sameSession : Bool, sameSession = decide (issuer = session.sessionRef) →
          (∀ key, session.runSnapshotRead sameSession (fun table => table.lookup pin.handle key) =
            .ok (some (reference.table.lookup key pin.sequence)) session) ∧
          ∀ lo hi, session.runSnapshotRead sameSession (fun table => table.range pin.handle lo hi) =
            .ok (some (reference.table.range lo hi pin.sequence)) session := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨reference, replay⟩ := SnapshotWalReplay.fromEmpty last.history
    (suffix.preservesRetained ready).1.resumed.ordered
  refine ⟨reference, replay, ?_⟩
  intro _ active _ localToken _ compared
  exact suffix.guardedReadsBeforeSuffix ready phase replay active localToken compared

end Alvoki.Storage.DiskSession
