import Alvoki.Storage.Disk.CapturedKeeperCustody
import Alvoki.Storage.Disk.CapturedCheckpointReadCensus
import Alvoki.Storage.Disk.HeldWalInstallation

namespace Alvoki.Storage.DiskSession

open System Manifest SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- The reached reader state supplies the cache, descriptor inventory and
files for the selected finisher. Carry reached state on both results. -/
def finishPreparedWithCensus
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (finish : Plan → Nat → EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit)
    (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState Reopened :=
  fun initial => match prepare (cache, initial) with
    | .error cause (_, reached) => .error cause reached
    | .ok (plan, opened, size) reached =>
      match finish plan size reached with
      | .ok () (_, final) => .ok opened final
      | .error cause (_, final) => .error cause final

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
    {renameMarker : Bool} (report : CapturedMarkedReadReports admission layout published renameMarker)
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

def wal (calls : CapturedAlignedCallbacks admission) {renameMarker : Bool} (report : CapturedMarkedReadReports admission layout published renameMarker)
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
    {renameMarker : Bool} (report : CapturedMarkedReadReports admission layout published renameMarker)
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
    {renameMarker : Bool} (report : CapturedMarkedReadReports admission layout published renameMarker)
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

theorem sameKeeper (finish : CapturedAlignedFinish calls report vacant selected) :
    finish.authorization.keeper = report.wal.keeper.observesFile :=
  (calls.wal report vacant).keeperObserved finish.authorization

/-- The aligned installation's own observed keeper allocation and first
barrier census supply the keeper-read custody. They describe the same
read-only payload report used by the installed table. -/
def readCustody (finish : CapturedAlignedFinish calls report vacant selected) : CapturedKeeperOpenReports report := by
  have same := finish.sameKeeper
  refine {
    beforeOpen := finish.repair.beforeKeeper
    free := ?_
    fresh := ?_
    opened := ?_
    duringRead := finish.repair.beforeAuthorization
    keeperRetained := ?_
    ownerRetained := ?_
    directoryRetained := ?_ }
  · have available := finish.repair.available
    rw [same] at available
    exact available
  · have fresh := finish.repair.fresh
    rw [same] at fresh
    exact fresh
  · have opened := finish.repair.opened
    simp only [same] at opened
    exact opened
  · have keeper := finish.repair.barrierCensus.1
    rw [same] at keeper
    exact keeper
  · have owner := finish.repair.barrierCensus.2.1
    rw [same] at owner
    exact owner
  · have cached := finish.repair.barrierCensus.2.2.1
    rw [same] at cached
    exact cached

private theorem keeperDescription_ne_cached (finish : CapturedAlignedFinish calls report vacant selected) :
    report.wal.keeper.calls.slot.description ≠ admission.cached.description := by
  have cached := finish.authorization.directoryRetained
  rw [finish.repair.firstDrops, ← DescriptorInventory.afterDrops_append] at cached
  have atOpen : admission.cached ∈ finish.readCustody.atOpen.slots := (List.mem_filter.mp cached).1
  intro same
  have member := finish.readCustody.atOpen.mem_references.mpr ⟨admission.cached, atOpen, rfl, same.symm⟩
  change admission.cached.reference ∈
    ((report.listing.afterClose.afterDrops finish.readCustody.beforeOpen).references report.wal.keeper.calls.slot.description) at member
  rw [finish.readCustody.fresh] at member
  exact List.not_mem_nil member

private abbrev KeeperRepairState := CensusDirectoryCache × CensusOpenState

private def fileAction {result : Type} (action : EStateM IO.Error FileImage result) :
    EStateM IO.Error KeeperRepairState result := fun (cache, census, before) =>
  match action before.image with
  | .ok value after => .ok value (cache, census, { before with image := after })
  | .error cause after => .error cause (cache, census, { before with image := after })

private def openForSync (finish : CapturedAlignedFinish calls report vacant selected) (name : FilePath) :
    EStateM IO.Error CensusOpenState (DescriptorInventory × DescriptorSlot × Nat) := fun (census, before) =>
  match finish.authorization.openRead name before with
  | .ok opened after => .ok opened (census, after)
  | .error cause after => .error cause (census, after)

/-- Both reached fsyncs use the same callbacks as the settled file-image
proof, with the measured drops applied at each successful return. -/
private def fsyncWithCensus (finish : CapturedAlignedFinish calls report vacant selected)
    (handle : DescriptorInventory × DescriptorSlot × Nat) : EStateM IO.Error CensusOpenState Unit :=
  fun (census, before) =>
    match finish.authorization.fsync handle before with
    | .ok () after =>
      let drops := if handle.2.1.description = admission.cached.description then
        finish.repair.afterAuthorization else finish.afterKeeper
      .ok () (census.afterDrops drops, after)
    | .error cause after => .error cause (census, after)

private def actions (finish : CapturedAlignedFinish calls report vacant selected) (resolved : DiskDirectory)
    (plan : Plan) (size : Nat) : EStateM IO.Error KeeperRepairState Unit :=
  finishBoundedMarkedOpen resolved plan size
    (fun path => fileAction (calls.removeFile path))
    (fun path bytes state => fileAction (calls.write state.1 path bytes) state)
    (SyncPathGroup.run (sync resolved.path finish.openForSync finish.fsyncWithCensus))
    (fun source target => fileAction (calls.renameFile source target))

private def rawTail (finish : CapturedAlignedFinish calls report vacant selected) :
    EStateM IO.Error KeeperRepairState Unit := do
  let _ ← finish.readCustody.readKeeper
  finish.actions directory layout.boundedPlan report.wal.keeper.calls.metadata.byteSize.toNat

private theorem keeperAligned (finish : CapturedAlignedFinish calls report vacant selected) :
    layout.keeper.bytes.size = report.wal.keeper.calls.metadata.byteSize.toNat := by
  have extent := finish.repair.aligned
  rw [finish.sameKeeper] at extent
  exact extent

private theorem keeperTailEmpty (finish : CapturedAlignedFinish calls report vacant selected) :
    layout.tail = ByteArray.empty := by
  have measured := finish.keeperAligned.trans report.wal.keeper.observesFile.extent
  rw [ByteArray.size_append] at measured
  exact ByteArray.size_eq_zero_iff.mp (by omega)

/-- Derive the cache-bearing keeper read and the two reached syncs from
the aligned installation's existing primitive observations. The pending
entry comes from that read and is consumed by the keeper sync. -/
theorem rawTail_returns (finish : CapturedAlignedFinish calls report vacant selected) :
    finish.rawTail (admission.cache, finish.readCustody.atOpen, admission.held) =
      .ok () (admission.cache, finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  let observed := finish.readCustody
  have aligned := finish.keeperAligned
  have authCensus : observed.afterRead.afterDrops finish.repair.afterAuthorization =
      finish.authorization.keeper.inventory.afterDrops
        (finish.repair.beforeAuthorization ++ finish.repair.afterAuthorization) := by
    unfold CapturedKeeperOpenReports.afterRead observed readCustody
    dsimp only
    rw [DescriptorInventory.afterDrops_append, finish.sameKeeper]
    rfl
  have retained (ref : DescriptorSlot)
      (live : ref ∈ (finish.authorization.keeper.inventory.afterDrops
        (finish.repair.beforeAuthorization ++ finish.repair.afterAuthorization)).slots) :
      ∀ event ∈ finish.repair.afterAuthorization, event.removes ref.reference = false := by
    have kept := List.all_eq_true.mp (List.mem_filter.mp live).2
    intro event inDrops
    have selected := kept event (List.mem_append_right _ inDrops)
    cases reports : event.removes ref.reference <;> simp_all
  have first :
      finish.fsyncWithCensus (admission.reached, admission.cached, 0) (observed.afterRead, admission.held) =
      .ok () (observed.afterRead.afterDrops finish.repair.afterAuthorization,
        { admission.held with image := retry.image.syncDirectory }) := by
    have raw := finish.authorization.effect
    change finish.authorization.fsync (admission.reached, admission.cached, 0) admission.held = _ at raw
    rw [show finish.authorization.outcome = .completed from finish.repair.completed] at raw
    have ended : finish.authorization.fsync (admission.reached, admission.cached, 0) admission.held =
        .ok () { admission.held with image := retry.image.syncDirectory } := raw
    simp [fsyncWithCensus, ended]
  have second : finish.authorization.fsync (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
      { admission.held with image := retry.image.syncDirectory } =
    .ok () { admission.held with image := retry.image.syncDirectory.syncKeeper } := by
    have actual := finish.repair.outcome.completed_of_return finish.succeeded
    change finish.authorization.fsync (finish.authorization.keeper.inventory, finish.authorization.keeper.slot, 0)
      { admission.held with image := retry.image.syncDirectory } =
      .ok () { admission.held with image := retry.image.syncDirectory.syncKeeper } at actual
    rw [finish.sameKeeper] at actual
    exact actual
  have keeperAt : ∀ event ∈ finish.repair.afterAuthorization,
      event.removes report.wal.keeper.calls.slot.reference = false := by
    have keeping := retained _ finish.repair.keeperRetained
    rw [finish.sameKeeper] at keeping
    exact keeping
  have routed := observed.syncFromRead aligned finish.repair.noLater finish.openForSync finish.fsyncWithCensus
    (fun path => fileAction (calls.removeFile path))
    (fun path bytes state => fileAction (calls.write state.1 path bytes) state)
    (fun source target => fileAction (calls.renameFile source target)) finish.repair.afterAuthorization keeperAt
    (retained _ finish.repair.lockRetained) first
  change finish.rawTail (admission.cache, observed.atOpen, admission.held) = _
  rw [show finish.rawTail (admission.cache, observed.atOpen, admission.held) = _ from routed.2.2.2]
  simp only [fsyncWithCensus, second, ite_eq_right finish.keeperDescription_ne_cached]
  rw [authCensus, DescriptorInventory.afterDrops_append]
  rfl

private theorem actions_returns (finish : CapturedAlignedFinish calls report vacant selected) :
    let keeper := (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
    finish.actions directory layout.boundedPlan layout.plan.keeperBytes.size
      (admission.cache.remember (directory.file (.walSegment layout.keeper.first)) keeper,
        finish.readCustody.afterRead, admission.held) =
      .ok () (admission.cache, finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  have returned := finish.rawTail_returns
  have read := finish.readCustody.readsAligned finish.keeperAligned
  simp only [rawTail, Bind.bind, EStateM.bind, read] at returned
  have extent : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    report.wal.keeper.observesFile.extent
  rw [extent] at returned
  exact returned

private def finishAt (finish : CapturedAlignedFinish calls report vacant selected) (resolved : DiskDirectory)
    (_owner : DescriptorSlot) (cache : CensusDirectoryCache) (prepared : Plan × Reopened × Nat) :
    EStateM IO.Error CensusOpenState Reopened := fun (_, before) =>
  let (plan, opened, size) := prepared
  let handle := (report.wal.keeper.calls.inventory, report.wal.keeper.calls.slot, 0)
  let remembered := cache.remember (resolved.file (.walSegment plan.keeper)) handle
  match finish.actions resolved plan size (remembered, finish.readCustody.afterRead, before) with
  | .ok () (_, reached) => .ok opened reached
  | .error cause (_, reached) => .error cause reached

/-- Restore the state effects of the selected keeper callback at the
read-only worker's boundary. The continuation begins after its read, and
the same raw tail proves the pending cache and census passed to repair. -/
theorem finishAt_returns (finish : CapturedAlignedFinish calls report vacant selected) (opened : Reopened) :
    finish.finishAt directory admission.owner admission.cache
      (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) =
      .ok opened (finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  have keeperPath : (directory.file (.walSegment layout.boundedPlan.keeper)) =
      directory.file (.walSegment layout.keeper.first) := rfl
  simp only [finishAt, keeperPath, finish.actions_returns]

end CapturedAlignedFinish

namespace CapturedAlignedCallbacks

variable {calls : CapturedAlignedCallbacks admission} {report : CapturedMarkedReadReports admission layout published}

private def bootstrapAt (calls : CapturedAlignedCallbacks admission) (_resolved : DiskDirectory)
    (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState Reopened := fun (openCensus, before) =>
  match calls.bootstrap cache before.image with
  | .ok value reached => .ok value (openCensus, { before with image := reached })
  | .error cause reached => .error cause (openCensus, { before with image := reached })

private def installAfterRecovery (calls : CapturedAlignedCallbacks admission)
    (resolved : DiskDirectory) (owner : DescriptorSlot) (recover : EStateM IO.Error CensusOpenState Reopened) :
    EStateM IO.Error CensusOpenState SegmentedSession := do
  let opened ← recover
  installReady opened.installed (fun phase => pure (phase, calls.nextRef)) (fun _ => pure (calls.nextRef + 1))
    fun (phase, phaseRef) sessionRef => pure ⟨resolved, owner.description, phase, phaseRef, sessionRef⟩

def recoverWithFinish (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened)
    (resolved : DiskDirectory) (owner : DescriptorSlot) (cache : CensusDirectoryCache) :
    EStateM IO.Error CensusOpenState SegmentedSession :=
  calls.installAfterRecovery resolved owner (report.recoverThroughReads finish calls.bootstrapAt resolved owner cache)

/-- The native-shaped open can keep the reached read state all the way
through marked repair, under the same guards and ready installation. -/
def runWithMarked (calls : CapturedAlignedCallbacks admission)
    (marked : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run fun resolved owner cache =>
    calls.installAfterRecovery resolved owner
      (admission.recoverWithMarked resolved (marked resolved cache) (calls.bootstrapAt resolved cache))

/-- Use the shared marked recovery and allocate the ready session after the
reached repair callback returns. -/
def runWithFinish (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run (calls.recoverWithFinish report finish)

/-- In the marked route, two interpretations with the same reached
recovery return allocate the same session and expose the same final state. -/
theorem runWithMarked_eq (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (marked : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (agrees : marked directory admission.cache (admission.reached, admission.held) =
      (report.walReads.prepare report.reads.readPrefix >>= finish directory admission.owner admission.cache)
        (admission.reached, admission.held)) :
    calls.runWithMarked marked = calls.runWithFinish report finish := by
  have route : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some metadata) (admission.reached, admission.held) := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, marker, Pure.pure, EStateM.pure]
  simp only [runWithMarked, runWithFinish, admission.run_reachesRecovery, recoverWithFinish, installAfterRecovery,
    CapturedMarkedReadReports.recoverThroughReads, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    Bind.bind, EStateM.bind, admission.recoverWithMarked_selects calls.flat route, Option.isSome_some, ↓reduceIte, agrees]

/-- A successful reached repair completes the same admitted read and
installation, independent of which bounded repair path was selected. -/
theorem installsWithFinish
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened) {census : DescriptorInventory} {after : FileImage}
    (finished : ∀ opened, finish directory admission.owner admission.cache
      (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) =
      .ok opened (census, { admission.held with image := after }))
    (ready : after.Ready layout.target) (effects : EffectTrace layout.target retry.image after) :
    ∃ session, calls.runWithFinish report finish = .ok session (census, { admission.held with image := after }) ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session { admission.held with image := after }) := by
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected report.reads
    report.stat report.chunkReads
  obtain ⟨opened, actualCheckpoint, model, preparedRead, exactCheckpoint, replay, generation, bytes,
    keeper, committed, bounds, refined, represents, noPins⟩ :=
    report.walReads.prepares (admission.reached, admission.held) laterValid following accepted ordered
      sizes (report.metadata.manifestRead layout.decoded) (report.metadata.markerRead layout.decoded)
  have reached : report.recoverThroughReads finish calls.bootstrapAt directory admission.owner admission.cache
      (admission.reached, admission.held) = .ok opened (census, { admission.held with image := after }) := by
    rw [report.recoverThroughReads_prepared calls.flat marker preparedRead]
    exact finished opened
  let final : LockedFileState FileImage := { admission.held with image := after }
  let session : SegmentedSession := ⟨directory, admission.owner.description, .ready opened.installed,
    calls.nextRef, calls.nextRef + 1⟩
  have returned : calls.runWithFinish report finish = .ok session (census, final) := by
    unfold runWithFinish
    rw [admission.run_reachesRecovery]
    simp only [recoverWithFinish, installAfterRecovery, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
      Bind.bind, EStateM.bind, reached]
    rfl
  have lock : final.owners.Owns directory session.descriptor := admission.opened.held
  have different : calls.nextRef ≠ calls.nextRef + 1 := by omega
  have freshSession : calls.nextRef + 1 ∉ calls.liveRefs := by
    intro present
    have fresh := calls.fresh _ present
    omega
  refine ⟨session, returned, ?_⟩
  exact ⟨opened, actualCheckpoint, model, session, final, rfl, rfl, rfl, rfl, admission.opened.captures.2.1,
    report.sameObjects.2.1, vacant rfl, rfl, lock, different,
    fun present => Nat.lt_irrefl _ (calls.fresh _ present), freshSession, ready, effects,
    exactCheckpoint, replay, generation, bytes, keeper, committed, bounds, refined, represents, noPins⟩

end CapturedAlignedCallbacks

namespace CapturedAlignedFinish

variable {calls : CapturedAlignedCallbacks admission} {report : CapturedMarkedReadReports admission layout published}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

/-- This specialization executes the aligned repair using its captured
keeper before allocating the ready session. -/
def run (finish : CapturedAlignedFinish calls report vacant selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithFinish report finish.finishAt

/-- Use the cache and inventory returned by the chronological reader.
The same keeper handle remains pending until its reached file barrier. -/
def runFromCensus (finish : CapturedAlignedFinish calls report vacant selected)
    (metadataRelease runRelease sealRelease : FilePath → List LockReferenceDrop) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithMarked fun resolved cache =>
    finishPreparedWithCensus
      (report.prepareFromCensus metadataRelease runRelease sealRelease finish.readCustody.readKeeperAt)
      (finish.actions resolved) cache

/-- The aligned repair starts at the reported vacant admission. Its
captured directory and keeper barriers preserve the admitted pair. -/
theorem installsAfterVacancy (finish : CapturedAlignedFinish calls report vacant selected)
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
    ∃ session final, finish.run = .ok session (finish.census, final) ∧
      final.image.directory.active = retry.image.directory.active ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session final) := by
  have prepared : Prepared retry.image layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  let after := retry.image.syncDirectory.syncKeeper
  have visible : retry.image.syncDirectory.keeper.active = some layout.target.trimmed := by
    change retry.image.keeper.active = some layout.keeper.bytes
    simpa only [finish.keeperTailEmpty, ByteArray.append_empty] using layout.visible
  have emptyNames : retry.image.syncDirectory.later.DurablyEmpty := by
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.DurablyEmpty, LaterNames.settled,
      finish.repair.noLater]
  have effects : EffectTrace layout.target retry.image after := EffectTrace.aligned .authorized emptyNames visible
  have ready : after.Ready layout.target := by
    have safe := effects.valid prepared.pair prepared.keeperPrefix prepared.newer
    exact ⟨safe.selected, safe.settled, visible, congrArg (fun bytes => [bytes]) visible, emptyNames⟩
  obtain ⟨session, returned, installed⟩ :=
    CapturedAlignedCallbacks.installsWithFinish (calls := calls) (report := report) vacant marker laterValid
      following accepted ordered selected finish.finishAt finish.finishAt_returns ready effects
  exact ⟨session, _, returned, rfl, installed⟩

/-- The selected reads add the aligned keeper to the pending cache and
return its reached census. Both grouped barriers use that state before
the open returns the exact replayed table. -/
theorem installsFromCensus (finish : CapturedAlignedFinish calls report vacant selected)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    (markerRead : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (markerRead.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    {released : FilePath → List LockReferenceDrop} {required : List (Nat × IO.FS.Metadata)}
    (seals : CapturedSealReadChain report released required report.listing.afterClose finish.readCustody.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ finish.readCustody.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
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
    ∃ session final, finish.runFromCensus metadataRelease runs.released released = .ok session (finish.census, final) ∧
      final.image.directory.active = retry.image.directory.active ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session final) := by
  obtain ⟨opened, reached, projected⟩ := report.preparesFromCensus manifest runs selected markerRead chronology
    finish.readCustody seals offsets retained following laterValid accepted ordered finish.readCustody.readKeeperAt
    (finish.readCustody.readsAligned finish.keeperAligned)
  have same : finish.runFromCensus metadataRelease runs.released released = finish.run := by
    unfold runFromCensus run
    apply calls.runWithMarked_eq report _ finish.finishAt marker
    simp only [finishPreparedWithCensus, reached, finish.actions_returns, Bind.bind, EStateM.bind, projected,
      finish.finishAt_returns]
  rw [same]
  obtain ⟨session, final, returned, pair, installed⟩ :=
    finish.installsAfterVacancy marker keeperValid laterValid following accepted ordered
  exact ⟨session, final, returned, pair, finish.lockRetained, finish.directoryRetained, installed⟩

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
  obtain ⟨prefixReached, _, _, _, _, oldObject, _, _⟩ :=
    trace.capturesAfterAdmission earlier last admission distinct distinctCached lockObject (calls.recoverWithFinish report finish.finishAt)
  have sameLock := report.sameObjects.2.1.trans (congrArg some oldObject)
  obtain ⟨session, _, returned, _, installed⟩ :=
    finish.installsAfterVacancy marker keeperValid laterValid following accepted ordered
  have sameObjects : finish.census.inode = admission.reached.inode := by
    unfold census
    rw [finish.repair.opened]
    rfl
  exact ⟨prefixReached, sameLock, session, _, returned, finish.lockRetained, finish.directoryRetained,
    sameObjects, finish.sameKeeper, report.chunkReads, installed⟩

end CapturedAlignedFinish

end Alvoki.Storage.DiskSession
