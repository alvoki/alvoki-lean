import Alvoki.Storage.Disk.CapturedMarkedReads
import Alvoki.Storage.Disk.HeldWalInstallation

namespace Alvoki.Storage.DiskSession

open System Manifest SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- The file-action projections for this captured open. The aligned repair
reports relate each reached sync to its actual cached callback. -/
structure CapturedAlignedCallbacks (admission : CensusOpenAdmissionReports input directory inventory retry) where
  nextRef : Nat
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < nextRef
  unlocked : UnlockReport
  flatName : String
  flatMessage : String
  flatAbsent : admission.lookup (directory.file .wal) (admission.reached, admission.held) =
    .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) (admission.reached, admission.held)
  bootstrap : CensusDirectoryCache → EStateM IO.Error FileImage Reopened
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : CensusDirectoryCache → FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : CensusDirectoryCache → Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace CapturedAlignedCallbacks

def lookup (_calls : CapturedAlignedCallbacks admission) (path : FilePath) :
    EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata) := fun files =>
  match admission.lookup path (admission.reached, { admission.held with image := files }) with
  | .ok value (_, reached) => .ok value reached.image
  | .error cause (_, reached) => .error cause reached.image

theorem flat (calls : CapturedAlignedCallbacks admission) :
    optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held) := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind, calls.flatAbsent, Pure.pure, EStateM.pure]

/-- Assign the operation packet its owner, census and cache directly from
the actual admission. The checked reader supplies every payload callback. -/
private def projectedCalls (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true)) :
    MarkedRetryChunkCalls CensusDirectoryCache directory retry where
  descriptors := admission.reached
  slot := admission.owner
  live := admission.opened.captures.2.1
  bindings := report.bindings
  lockObject := report.sameObjects.2.1
  flock := fun _ => .ok true
  acquired := rfl
  acquisition := vacant
  nextRef := calls.nextRef
  liveRefs := calls.liveRefs
  fresh := calls.fresh
  unlock := calls.unlocked
  openFiles := pure admission.cache
  lookup := calls.lookup
  bootstrap := calls.bootstrap
  cache := admission.cache
  initialized := rfl
  flatName := calls.flatName
  flatMessage := calls.flatMessage
  flatAbsent := by
    unfold lookup
    change (match admission.lookup (directory.file .wal) (admission.reached, admission.held) with
      | .ok value (_, reached) => EStateM.Result.ok value reached.image
      | .error cause (_, reached) => .error cause reached.image) = _
    rw [calls.flatAbsent]
    rfl
  reads := report.reads
  readKeeper := fun _ => readWalKeeperBytes report.reads
  removeFile := calls.removeFile
  write := calls.write
  sync := calls.sync
  renameFile := calls.renameFile

def wal (calls : CapturedAlignedCallbacks admission) (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true)) :
    HeldWalInstallReads layout (calls.projectedCalls report vacant) where
  inventory := report.inventoryWithOwner
  inventoryDescription := rfl
  inventoryOwners := rfl
  metadata := report.stat
  view := admission.view
  root := admission.root
  wal := report.wal
  keeperProjection := rfl

abbrev operations (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true)) :=
  (calls.wal report vacant).operations

private theorem mappedStored {get : Nat → Option ByteArray} {indices : List Nat} {files : List ByteArray}
    (successful : indices.mapM get = some files) {index : Nat} (found : index ∈ indices) :
    ∃ payload, get index = some payload := by
  induction indices generalizing files with
  | nil => simp at found
  | cons first rest ih =>
    cases read : get first with
    | none => simp [List.mapM_cons, read, Bind.bind, Option.bind] at successful
    | some payload =>
      rcases List.mem_cons.mp found with same | later
      · exact ⟨payload, same ▸ read⟩
      · cases readRest : rest.mapM get with
        | none => simp [List.mapM_cons, read, readRest, Bind.bind, Option.bind] at successful
        | some files => exact ih readRest later

private theorem storedAt {durable : CheckpointPublication.RunFiles} {binding checkpoint}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    {bytes manifest} (visible : binding = some bytes) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    {index : Nat} (within : index < manifest.header.runCount.toNat) :
    ∃ payload, durable manifest.header.generation index = some payload := by
  cases selected with
  | absent => contradiction
  | @present _ _ _ _ checked stored _ =>
    obtain rfl := Option.some.inj visible
    obtain rfl := Except.ok.inj (checked.symm.trans decoded)
    exact mappedStored stored (List.mem_range.mpr within)

/-- The held report is assembled from the actual listing and reads, with
the lock and directory lifetime indexed by the admitted cache capture. -/
noncomputable def heldReport (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) :
    HeldDirectoryMarkedRetryReports (calls.operations report vacant) published where
  lifetime := report.lifetime
  captured := rfl
  listing := report.listing
  listed := report.listed
  runs := by
    intro bytes manifest visible decoded index within
    apply Classical.choice
    obtain ⟨payload, stored⟩ := storedAt selected visible decoded within
    exact (report.runs bytes manifest visible decoded index within payload stored).choose_spec.2.2
  publishedBytes := by
    intro bytes manifest visible decoded index within payload stored
    obtain ⟨object, bound, contents, _⟩ := report.runs bytes manifest visible decoded index within payload stored
    exact ⟨object, bound, contents⟩

end CapturedAlignedCallbacks

/-- Reuse the listed repair's actual keeper open and grouped sync reports.
The last descriptor events are observed after the keeper sync has returned. -/
structure CapturedAlignedFinish (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  authorization : ListedDirectoryAuthorization (calls.heldReport report vacant selected)
  repair : ListedAlignedKeeperRepair authorization
  succeeded : ∃ reached, repair.keeperFsyncReturn = .ok () reached
  afterKeeper : List LockReferenceDrop
  lockRetained : admission.owner ∈
    (authorization.keeper.inventory.afterDrops (repair.beforeAuthorization ++ repair.afterAuthorization ++ afterKeeper)).slots
  directoryRetained : admission.cached ∈
    (authorization.keeper.inventory.afterDrops (repair.beforeAuthorization ++ repair.afterAuthorization ++ afterKeeper)).slots

namespace CapturedAlignedFinish

variable {calls : CapturedAlignedCallbacks admission} {report : CapturedMarkedReadReports admission layout published}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

def census (finish : CapturedAlignedFinish calls report vacant selected) : DescriptorInventory :=
  finish.authorization.keeper.inventory.afterDrops
    (finish.repair.beforeAuthorization ++ finish.repair.afterAuthorization ++ finish.afterKeeper)

private def finishAt (finish : CapturedAlignedFinish calls report vacant selected) (resolved : DiskDirectory)
    (_owner : DescriptorSlot) (cache : CensusDirectoryCache) (prepared : Plan × Reopened × Nat) :
    EStateM IO.Error CensusOpenState Reopened := fun (openCensus, before) =>
  let (plan, opened, size) := prepared
  match finishBoundedMarkedOpen resolved plan size calls.removeFile (calls.write cache) (calls.sync cache)
      calls.renameFile before.image with
  | .ok () reached => .ok opened (finish.census, { before with image := reached })
  | .error cause reached => .error cause (openCensus, { before with image := reached })

private def bootstrapAt (calls : CapturedAlignedCallbacks admission) (_resolved : DiskDirectory)
    (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState Reopened := fun (openCensus, before) =>
  match calls.bootstrap cache before.image with
  | .ok value reached => .ok value (openCensus, { before with image := reached })
  | .error cause reached => .error cause (openCensus, { before with image := reached })

private def recover (finish : CapturedAlignedFinish calls report vacant selected) (resolved : DiskDirectory)
    (owner : DescriptorSlot) (cache : CensusDirectoryCache) :
    EStateM IO.Error CensusOpenState SegmentedSession := do
  let opened ← report.recoverThroughReads finish.finishAt (bootstrapAt calls) resolved owner cache
  installReady opened.installed (fun phase => pure (phase, calls.nextRef)) (fun _ => pure (calls.nextRef + 1))
    fun (phase, phaseRef) sessionRef => pure ⟨resolved, owner.description, phase, phaseRef, sessionRef⟩

/-- The open schedule allocates the phase and snapshot identity only after
the recovery worker returns. Their distinct IDs come from the allocation
observation, as in the existing projected installer. -/
def run (finish : CapturedAlignedFinish calls report vacant selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run finish.recover

/-- The shared open and aligned repair install the table selected by the
checked reads at this admission. The proof follows the reported directory
and keeper syncs before allocating the returned session. -/
theorem installs {description keeperFirst : Nat} {initial : DescriptorInventory}
    {origin source : LockedFileState FileImage}
    (trace : LockCensusTrace directory description initial source inventory retry)
    (earlier : ReportedReopenPrefix directory keeperFirst origin source)
    (last : inventory.references description = [])
    (distinct : admission.owner.description ≠ description)
    (distinctCached : admission.cached.description ≠ description)
    (lockObject : inventory.inode admission.owner.description = initial.inode description)
    (finish : CapturedAlignedFinish calls report (trace.freshFlockAllowed.mpr last) selected)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (keeperValid : retry.image.keeper.Valid layout.target.Accepts)
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ReportedReopenPrefix directory keeperFirst origin retry ∧
    report.bindings (directory.file .lock) = some (initial.inode description) ∧
    ∃ session final,
      finish.run = .ok session (finish.census, final) ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      finish.census.inode = admission.reached.inode ∧
      finish.authorization.keeper = report.wal.keeper.observesFile ∧
      report.reads.ObservesSelected directory retry.image.directory.active.manifest published.durable ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session final) := by
  let vacant := trace.freshFlockAllowed.mpr last
  let operations := calls.operations report vacant
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected report.reads
    report.stat report.chunkReads
  obtain ⟨opened, actualCheckpoint, model, preparedRead, exactCheckpoint, replay, generation, bytes,
    keeper, committed, bounds, refined, represents, noPins⟩ :=
    report.walReads.prepares (admission.reached, admission.held) laterValid following accepted ordered
      sizes (report.metadata.manifestRead layout.decoded) (report.metadata.markerRead layout.decoded)
  have prepared : Prepared retry.image layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  obtain ⟨after, repaired, ready, effects⟩ :=
    finishMarkedOpen_completes prepared directory operations.removeFile (operations.write operations.cache)
      (operations.sync operations.cache) operations.renameFile (finish.authorization.settles finish.repair.completed)
      (finish.repair.healthyFinish finish.succeeded)
  have bounded : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      calls.removeFile (calls.write admission.cache) (calls.sync admission.cache) calls.renameFile retry.image =
      .ok () after := by
    rw [layout.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full _ _ prepared.valid]
    exact repaired
  have reached : report.recoverThroughReads finish.finishAt (bootstrapAt calls) directory admission.owner admission.cache
      (admission.reached, admission.held) =
      .ok opened (finish.census, { admission.held with image := after }) := by
    rw [report.recoverThroughReads_prepared calls.flat marker preparedRead]
    simp only [finishAt, CensusOpenAdmissionReports.held, bounded]
  let final : LockedFileState FileImage := { admission.held with image := after }
  let session : SegmentedSession := ⟨directory, admission.owner.description, .ready opened.installed,
    calls.nextRef, calls.nextRef + 1⟩
  obtain ⟨prefixReached, _, _, _, _, oldObject, _, admitted⟩ :=
    trace.capturesAfterAdmission earlier last admission distinct distinctCached lockObject finish.recover
  have returned : finish.run = .ok session (finish.census, final) := by
    unfold run
    rw [admitted]
    simp only [recover, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, Bind.bind, EStateM.bind, reached]
    rfl
  have lock : final.owners.Owns directory session.descriptor := admission.opened.held
  have different : calls.nextRef ≠ calls.nextRef + 1 := by omega
  have freshSession : calls.nextRef + 1 ∉ calls.liveRefs := by
    intro present
    have fresh := calls.fresh _ present
    omega
  have sameObjects : finish.census.inode = admission.reached.inode := by
    unfold census
    rw [finish.repair.opened]
    rfl
  refine ⟨prefixReached, report.sameObjects.2.1.trans (congrArg some oldObject),
    session, final, returned, finish.lockRetained, finish.directoryRetained, sameObjects,
    (calls.wal report vacant).keeperObserved finish.authorization, report.chunkReads, ?_⟩
  exact ⟨opened, actualCheckpoint, model, session, final, rfl, rfl, rfl, rfl, admission.opened.captures.2.1,
    report.sameObjects.2.1, vacant rfl, rfl, lock, different,
    fun present => Nat.lt_irrefl _ (calls.fresh _ present), freshSession, ready, effects,
    exactCheckpoint, replay, generation, bytes, keeper, committed, bounds, refined, represents, noPins⟩

end CapturedAlignedFinish

end Alvoki.Storage.DiskSession
