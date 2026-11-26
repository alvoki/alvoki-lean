import Alvoki.Storage.Disk.NativeMarkedFirstBarrierRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {directory : DiskDirectory} {history : List WAL.Write}
  {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
  {lock root : Nat} {first after : CensusOpenState} {events : List NativeMarkedBarrierEvent} {available : Bool}

/-- The selected and append-ready WAL evidence belongs to the original
attempted image. A failed directory barrier can narrow crash choices
while this evidence picks the same visible checkpoint and keeper. -/
structure NativeMarkedBarrierSeed (first : CensusOpenState) (history : List WAL.Write)
    (published : CheckpointPublication.Image) (checkpoint : Option (PackedTable × UInt64)) where
  layout : CanonicalKeeperLayout first.2.image history
  prepared : Prepared first.2.image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint published.durable first.2.image.directory.active.manifest checkpoint
  accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
    first.2.image.directory.active.manifest
  following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1, layout.range.watermark < start
  ordered : WAL.OrdinalsFrom 1 history
  wal : WalSegmentImage
  readLayout : wal.ReadLayout history
  valid : wal.Valid history
  spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize
  active : wal.directory.active = layout.target.pair
  keeper : layout.target.first = wal.active.first
  kept : first.2.image.kept = (wal.checkpointReopenFiles wal.directory none).kept

namespace NativeMarkedBarrierRetries

variable (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after available)
  (seed : NativeMarkedBarrierSeed first history published checkpoint)

/-- Re-index the original layout with the actually reached file image.
The same marker and keeper bytes still witness the unchanged selection. -/
def layout : CanonicalKeeperLayout after.2.image history where
  range := seed.layout.range
  decoded := (congrArg DirectoryPublication.Bindings.walRange trace.preserves.2.1).trans seed.layout.decoded
  through := seed.layout.through
  first := seed.layout.first
  sealed := seed.layout.sealed
  keeper := seed.layout.keeper
  chain := seed.layout.chain
  covers := seed.layout.covers
  tail := seed.layout.tail
  visible := (congrArg Publication.Image.active trace.preserves.2.2.2.1).trans seed.layout.visible

theorem target : (trace.layout seed).target = seed.layout.target := by
  have pair := trace.preserves.2.1
  cases original : seed.layout.target with
  | mk bindings range decoded first covered trimmed size =>
    have firstPair : first = seed.layout.keeper.first := (congrArg Target.first original).symm
    have sameRange : range = seed.layout.range := (congrArg Target.range original).symm
    have sameTrimmed : trimmed = seed.layout.keeper.bytes := (congrArg Target.trimmed original).symm
    have sameBindings : bindings = after.2.image.directory.active :=
      (congrArg Target.pair original).symm.trans pair.symm
    subst first range trimmed bindings
    rfl

include trace in
theorem laterBeyond : after.2.image.later.Beyond seed.layout.range.through := by
  have exactImage := trace.preserves.1
  rw [exactImage]
  split
  · intro names listed
    have visible : names = first.2.image.later.visible := by
      simpa [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled] using listed
    subst names
    exact seed.prepared.newer _ List.mem_cons_self
  · exact seed.prepared.newer

/-- An after-effect error settles only the directory and suffix name
choices. Keeper validity, the old prefix and the pruning guard can all
be transported from the original selected image. -/
theorem prepared : Prepared after.2.image (trace.layout seed).target (trace.layout seed).plan := by
  refine ⟨rfl, ?_, trace.laterBeyond seed, rfl, rfl, rfl, (trace.layout seed).visible⟩
  rw [trace.target seed, trace.preserves.2.2.2.1]
  exact seed.prepared.keeperPrefix

include trace seed in
theorem accepted :
    published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      after.2.image.directory.active.manifest := by
  rw [trace.preserves.2.1]
  exact seed.accepted

variable {input : FilePath}
  (ready : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after true)
  (opened : MarkedReadyOpenObservations input directory after.1 after.2
    (ready.layout seed) published ready.vacant (ready.retainsSelected seed.selected))

/-- The healthy callbacks come from the reached vacant census. Their
chronological marked opener determines the exact returned table and
retains the prior read replay. The work sums over the failed sequence and
this successful attempt, with the original selected bytes as budget. -/
theorem reopensWithWork
    (objects : opened.admission.view.modelObject opened.reads.lock = lock ∧
      opened.admission.view.modelObject opened.admission.root = root)
    (pending : PendingClientReplay log reads history) (bounded : ∀ read ∈ reads, read.BoundedBy history.length) :
    ∃ (state : NativeReadyState) (repairRequests : Nat),
      NativeReadyReadPrefix (opened.finish.run opened.chronology) state history log reads state ∧
      opened.finish.run opened.chronology = .ok state.session (state.census, state.files) ∧
      state.session.directory = directory ∧ state.owner = opened.admission.owner ∧
      state.directorySlot = opened.admission.cached ∧ state.cache = opened.admission.cache ∧
      state.census = opened.finish.census ∧
      opened.admission.reached.inode state.owner.description = lock ∧
      opened.admission.reached.inode state.directorySlot.description = root ∧
      state.files.image.directory.active = first.2.image.directory.active ∧
      state.files.image.kept = first.2.image.kept ∧
      state.writer.published.durable = published.durable ∧ state.writer.checkpoint = checkpoint ∧
      state.writer.target = seed.layout.target ∧
      state.session.phaseRef ∉ opened.callbacks.liveRefs ∧ state.session.sessionRef ∉ opened.callbacks.liveRefs ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok state.writer.installed.table ∧
      InstalledClientReplay log reads history state.writer.installed state.session ∧
      countBoundedRepairCallbacks directory (ready.layout seed).boundedPlan opened.reads.wal.keeper.calls.metadata.byteSize.toNat =
        .ok repairRequests ∧
      (events.map (·.chunkRequests)).sum + opened.metadataReadRequests + opened.payloadReadRequests ≤
        (events.length + 1) * NativeMarkedBarrierAttempt.chunkBudget first.2.image history checkpoint ∧
      (events.map (·.directoryRequests)).sum +
        (opened.directoryWork.opendirCalls + opened.directoryWork.readdirCalls + opened.directoryWork.closedirCalls) =
        (events.map (·.listedNames)).sum + opened.reads.listing.scan.names.length + 3 * (events.length + 1) ∧
      (events.map (·.repairRequests)).sum + repairRequests ≤ events.length + first.2.image.later.visible.length + 6 := by
  have prepared := ready.prepared seed
  have accepted := ready.accepted seed
  have following := seed.following
  have kept := ready.preserves.2.2.1.trans seed.kept
  obtain ⟨state, started, cache, census, owner, directorySlot, active, durable, checkpointEq, path, target, seals, _, _, phaseFresh, sessionFresh⟩ :=
    opened.finish.startsNativeReadPrefix opened.chronology opened.markerFound prepared following accepted seed.ordered
      seed.readLayout seed.valid seed.spans (seed.active.trans (congrArg Target.pair (ready.target seed)).symm)
      seed.keeper kept pending bounded
  obtain ⟨session, final, requests, returned, _, installed, chunks, listed, counted, repairs⟩ :=
    opened.installsWithWork prepared following accepted seed.ordered
  obtain ⟨table, chosen, _, installedSession, installedFiles, result, _, _, phase, _, _, _, _, _, _, _, _, _,
    _, checkpointSelected, replay, _, _, _, _, _, _, _⟩ := installed
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj result
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (started.frames.1.symm.trans returned)
  have loaded := Phase.ready.inj (started.refines.1.phase.symm.trans (sameSession.symm ▸ phase))
  have exactTable : state.writer.installed.table = table.table := congrArg Installed.table loaded
  have exactCheckpoint := checkpointSelected.uniqueResult (ready.retainsSelected seed.selected)
  have directoryAt := opened.admission.opened.captures.2.2.2.2.1
  have callBudget : opened.metadataReadRequests + opened.payloadReadRequests ≤
      NativeMarkedBarrierAttempt.chunkBudget first.2.image history checkpoint := by
    refine Nat.le_trans chunks ?_
    unfold NativeMarkedBarrierAttempt.chunkBudget
    rw [ready.preserves.2.1]
    have frames : (ready.layout seed).range.through - (ready.layout seed).first ≤ history.length :=
      Nat.le_trans (Nat.sub_le ..) (Nat.le_of_eq (ready.layout seed).through)
    exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_right _ frames) _) _
  obtain ⟨previousChunks, previousDirectory, previousRepairs⟩ := ready.boundedWork
  refine ⟨state, requests, started, started.frames.1, path, owner, directorySlot, cache, census, ?_, ?_,
    active.trans ready.preserves.2.1, seals.trans ready.preserves.2.2.1, durable, checkpointEq, target.trans (ready.target seed),
    phaseFresh, sessionFresh, ?_, started.guardedReplay, counted, ?_, ?_, ?_⟩
  · rw [owner]
    exact opened.reads.identifiesLock.symm.trans objects.1
  · rw [directorySlot]
    exact directoryAt.symm.trans objects.2
  · rw [exactTable, ← exactCheckpoint]
    exact replay
  · rw [Nat.add_mul, Nat.one_mul]
    omega
  · rw [previousDirectory, listed]
    omega
  · rw [ready.preserves.2.2.2.2.1] at repairs
    rw [previousRepairs]
    omega

end NativeMarkedBarrierRetries
end Alvoki.Storage.DiskSession
