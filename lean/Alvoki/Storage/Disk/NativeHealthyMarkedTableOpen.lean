import Alvoki.Storage.Disk.Proofs.Keeper.NativeLongKeeperTableOpen
import Alvoki.Storage.Disk.NativePrunedAlignedMarkedWorker

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

section

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {normalized : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

/-- The repair branch matches the exact measured and planned sizes and
the plan's actual later names. A longer keeper can have either suffix shape. -/
def CapturedKeeperFinish.UsesMeasuredRepair (chosen : CapturedKeeperFinish normalized reads vacant selected) : Prop :=
  let measured := reads.wal.keeper.calls.metadata.byteSize.toNat
  let plan := layout.boundedPlan
  match chosen with
  | .aligned _ => plan.keeperSize = measured ∧ plan.newer = []
  | .prunedAligned _ => plan.keeperSize = measured ∧ plan.newer ≠ []
  | .longer _ => plan.keeperSize < measured

theorem CapturedKeeperFinish.usesMeasuredRepair (chosen : CapturedKeeperFinish normalized reads vacant selected) :
    chosen.UsesMeasuredRepair := by
  have size : layout.boundedPlan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
  cases chosen with
  | aligned finish =>
    have measured := finish.repair.aligned
    rw [finish.sameKeeper] at measured
    exact ⟨size.trans measured, finish.repair.noLater⟩
  | prunedAligned finish =>
    have measured := finish.repair.aligned
    rw [finish.sameKeeper] at measured
    exact ⟨size.trans measured, finish.repair.nonempty⟩
  | longer finish =>
    show layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [size]
    exact finish.longer

/-- Equal extents stay in the original keeper read and remember scope.
The observation callback adds an explicit release only on the longer route. -/
private theorem scopedRead_aligned (reader : MarkedTemporaryReadCalls heap)
    (callbacks : AlignedKeeperCacheCallbacks heap) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (path : FilePath) (size : Nat) :
    reader.readKeeperWithRelease (fun name file => callbacks.modifyPending pending (pushPending name file))
      path size size = (callbacks.withFileReads reader).readKeeper pending path size size := by
  simp [MarkedTemporaryReadCalls.readKeeperWithRelease, AlignedKeeperCacheCallbacks.readKeeper,
    AlignedKeeperCacheCallbacks.withFileReads, readKeeperWith]

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry} {fileCalls : MarkedTemporaryReadCalls heap}
  {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- Each case observes just the keeper-specific portion of the same raw
marked worker. The common checkpoint, marker, directory and seal reads
are supplied once, outside this report. -/
inductive NativeHealthyMarkedKeeperReport (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (fileCalls : MarkedTemporaryReadCalls heap) (callbacks : AlignedKeeperCacheCallbacks heap)
    (beforeKeeper : heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (stage : LongKeeperStageCallbacks heap) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    CapturedKeeperFinish normalized reads vacant selected → heap → Type where
  | aligned {finish : CapturedAlignedFinish normalized reads vacant selected}
      (seen : AlignedKeeperCacheReport finish view init entry seed (callbacks.withFileReads fileCalls) beforeKeeper) :
      NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename (.aligned finish) seen.reached
  | prunedAligned {finish : CapturedPrunedAlignedFinish normalized reads vacant selected}
      (seen : PrunedAlignedKeeperCacheReport finish view init entry seed (callbacks.withFileReads fileCalls) remove beforeKeeper) :
      NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename (.prunedAligned finish) seen.reached
  | longer {finish : CapturedLongKeeperFinish normalized reads vacant selected}
      {read : NativeLongKeeperReadHeap finish seed fileCalls beforeKeeper}
      {authorization : NativeLongKeeperAuthorizationHeap read (callbacks.withFileReads fileCalls)}
      {suffix : NativeLongKeeperSuffixHeap authorization remove} {staged : NativeLongKeeperFreshStageHeap suffix stage}
      {names : heap → FilePath → Option Nat} {synced : NativeLongKeeperStagedSyncHeap staged names}
      {renamed : NativeLongKeeperRenameHeap synced rename} (seen : NativeLongKeeperSettlementHeap renamed) :
      NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename (.longer finish) seen.reached

variable {chosen : CapturedKeeperFinish normalized reads vacant selected} {reached : heap}

private noncomputable def CapturedKeeperFinish.settledFiles
    (chosen : CapturedKeeperFinish normalized reads vacant selected) : LockedFileState FileImage :=
  match chosen with
  | .aligned _ => {admission.held with image := retry.image.syncDirectory.syncKeeper}
  | .prunedAligned finish => finish.settled
  | .longer finish => finish.settled

private theorem CapturedKeeperFinish.preparesForMeasuredRepair
    (chosen : CapturedKeeperFinish normalized reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads chosen.reader)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened,
      reads.walReads.prepare reads.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) ∧
      chosen.markedWorker chronology directory admission.cache (admission.reached, admission.held) =
        .ok opened (chosen.census, chosen.settledFiles) := by
  cases chosen with
  | aligned finish =>
    obtain ⟨opened, prepared, repaired⟩ := finish.recoversWithSelectedPreparation chronology valid following accepted ordered
    exact ⟨opened, prepared, repaired⟩
  | prunedAligned finish =>
    obtain ⟨opened, prepared, repaired⟩ := finish.recoversWithSelectedPreparation chronology valid following accepted ordered
    exact ⟨opened, prepared, repaired⟩
  | longer finish =>
    obtain ⟨opened, prepared, repaired⟩ := finish.recoversWithSelectedPreparation chronology valid following accepted ordered
    exact ⟨opened, prepared, repaired⟩

private theorem NativeHealthyMarkedKeeperReport.repairSelectedKeeper
    (seen : NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename chosen reached)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    let keeper := callbacks.withFileReads fileCalls
    let read := fileCalls.readKeeperWithRelease (fun path file => keeper.modifyPending seed.pendingRef (pushPending path file))
    let write := stage.stage seed.pendingRef keeper.modifyPending
    let grouped := keeper.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    let measured := reads.wal.keeper.calls.metadata.byteSize.toNat
    ∃ afterRead,
      read (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size measured beforeKeeper =
        .ok layout.keeper.bytes afterRead ∧
      finishBoundedMarkedOpen directory layout.boundedPlan measured remove write grouped rename afterRead = .ok () reached ∧
      (view.cacheAt reached seed.directoryRef seed.activeRef seed.pendingRef, view.descriptors reached, view.files reached) =
        (admission.cache, chosen.census, chosen.settledFiles) := by
  intro keeper read write grouped measured
  cases seen with
  | @aligned finish observed =>
    have sameSize := observed.readsKeeper
    have extent := (CapturedKeeperFinish.aligned finish).usesMeasuredRepair.1
    have size : layout.keeper.bytes.size = measured := layout.target.trimmedSize.trans extent
    refine ⟨observed.remembered, ?_, observed.repairsAfterRead remove write rename, (observed.returns remove write rename).2.2.2.2⟩
    dsimp only [read, keeper, measured] at size ⊢
    rw [← size, scopedRead_aligned]
    rwa [← size] at sameSize
  | @prunedAligned finish observed =>
    have sameSize := observed.readsKeeper
    have extent := (CapturedKeeperFinish.prunedAligned finish).usesMeasuredRepair.1
    have size : layout.keeper.bytes.size = measured := layout.target.trimmedSize.trans extent
    refine ⟨observed.remembered, ?_, observed.repairsAfterRead later write rename, (observed.returns later write rename).final⟩
    dsimp only [read, keeper, measured] at size ⊢
    rw [← size, scopedRead_aligned]
    rwa [← size] at sameSize
  | longer observed =>
    exact ⟨_, NativeLongKeeperReadHeap.readsScoped _ _, observed.returns.ran, observed.returns.final⟩

variable {stream : Type} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {chronology : CapturedMarkedReadCensus reads chosen.reader}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}

/-- A single marked interpreter replays the selected reads, then uses
its measured extent and actual later names for the repair. The long
read's native finalization is supplied by the local release report. -/
noncomputable def recoverHealthyMarkedWithRefs (fileCalls : MarkedTemporaryReadCalls heap)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (stage : LongKeeperStageCallbacks heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (directory : DiskDirectory) (bootstrap : EStateM IO.Error heap Reopened) : EStateM IO.Error heap Reopened :=
  let keeper := callbacks.withFileReads fileCalls
  recoverSegmentedWalWith
    (rejectFlatWalWith directory (optionalMetadataWith (stat (directory.file .wal))))
    (optionalMetadataWith (stat (directory.file .walBoundary)))
    (reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
      fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
      fileCalls.seal (fileCalls.readKeeperWithRelease (fun path handle => keeper.modifyPending pending (pushPending path handle)))
      remove (stage.stage pending keeper.modifyPending) (keeper.syncPaths directory.path cached active pending) rename)
    bootstrap

theorem NativeHealthyMarkedKeeperReport.recovers
    (seen : NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename chosen reached)
    (extents : MarkedWalExtentReports prepared listing)
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (valid : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (bootstrap : EStateM IO.Error heap Reopened) :
    chosen.UsesMeasuredRepair ∧ ∃ opened,
      recoverHealthyMarkedWithRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove stage rename fileCalls.stat directory bootstrap seed.afterPending = .ok opened reached ∧
      chosen.markedWorker chronology directory admission.cache (admission.reached, admission.held) =
        .ok opened (view.descriptors reached, view.files reached) ∧
      view.cacheAt reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  obtain ⟨_, read, repair, settled⟩ := seen.repairSelectedKeeper (valid.newer _ List.mem_cons_self)
  obtain ⟨opened, raw, projected⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered flat marker
    _ read remove _ _ rename repair bootstrap
  obtain ⟨captured, samePreparation, normalized⟩ :=
    chosen.preparesForMeasuredRepair chronology valid following accepted ordered
  have sameOpened : captured = opened :=
    congrArg (fun result : Plan × Reopened × Nat => result.2.1)
      (EStateM.Result.ok.inj (samePreparation.symm.trans projected)).1
  subst captured
  refine ⟨chosen.usesMeasuredRepair, opened, raw, ?_, congrArg Prod.fst settled⟩
  rw [show (view.descriptors reached, view.files reached) = (chosen.census, chosen.settledFiles) from congrArg Prod.snd settled]
  exact normalized

end

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {report : MarkedOpenSuccessReports input directory history log recorded}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {slotOf : heap → stream → DescriptorSlot} {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper reached : heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- All three healthy marked repairs run one public table schedule.
The keeper report supplies local effects of the measured branch. The
exact cache constructor, replay and reached repair heap supply the one
common installer and start the same client ledger. -/
theorem MarkedOpenSuccessReports.opensHealthyFromAdmission
    (raw : RawOpenAdmissionReport report.opening.admission view calls entry)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init raw.afterFlock)
    (prepare : NativeMarkedCheckpointReadHeap seed report.opening.chronology fileCalls)
    (listing : MarkedDirectoryReadReport prepare directoryCalls slotOf)
    (extents : MarkedWalExtentReports prepare listing)
    (seals : MarkedSealReadChain seed fileCalls report.opening.chronology.seals listing.reached beforeKeeper)
    (keeper : NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename report.opening.finish reached)
    (sameLookup : fileCalls.stat = calls.lookup)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {metadata : IO.FS.Metadata}
    (marker : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some metadata) seed.afterPending)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors reached, view.files reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase
          allocation.afterToken) :
    let lockIdentity := fun handle => (view.handle raw.afterFlock handle).2.1.description
    let recovery := fun resolved cache =>
      recoverHealthyMarkedWithRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove stage rename calls.lookup resolved (bootstrap resolved cache)
    report.opening.finish.UsesMeasuredRepair ∧
    ∃ (installed : MarkedHeapInstallation report view init raw.afterFlock seed raw.lock lockIdentity
          phaseIdentity tokenIdentity allocatePhase allocateToken reached)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      (let cache := makeCache seed.directoryRef seed.activeRef seed.pendingRef;
        cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
          cache.AtDirectory directory.path) ∧
      calls.runOpen input init makeCache (fun resolved lock cache => do
        let opened ← recovery resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry =
        .ok installed.table installed.allocation.afterToken := by
  intro lockIdentity recovery
  have locked : lockIdentity raw.lock = report.opening.admission.owner.description :=
    congrArg (fun observed => observed.2.1.description) (raw.sameLock.trans raw.appendHandle)
  obtain ⟨guard, opened, rawRecovered, normalized, capturedCache⟩ := keeper.recovers extents seals
    report.prepared report.following report.accepted report.ordered flat marker
    (throw (IO.userError "bootstrap branch is unavailable after the marker check"))
  obtain ⟨installed⟩ := report.installsFromRepairedHeap view init raw.afterFlock seed reached
    raw.lock lockIdentity locked phaseIdentity tokenIdentity allocatePhase allocateToken ⟨opened, normalized⟩
    capturedCache observe
  have returned : recovery directory installed.files seed.afterPending = .ok opened reached := by
    dsimp only [recovery, recoverHealthyMarkedWithRefs] at rawRecovered ⊢
    rw [← sameLookup]
    simpa only [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure] using rawRecovered
  obtain ⟨cacheOpen, makeCache, action, source, useCache, native⟩ :=
    installed.opensFromAdmission recovery assemble constructs returned normalized
  exact ⟨guard, installed, cacheOpen, makeCache, action, source, useCache, native⟩

section MarkedPreparation

variable {heap stream : Type}
  (fileCalls : MarkedTemporaryReadCalls heap) (directoryCalls : MarkedDirectoryReadCalls heap stream)
  (callbacks : AlignedKeeperCacheCallbacks heap)
  (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
  (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (stage : LongKeeperStageCallbacks heap) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
  (stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
  (directory : DiskDirectory)

local notation "keeper" => AlignedKeeperCacheCallbacks.withFileReads callbacks fileCalls
local notation "readKeeper" => MarkedTemporaryReadCalls.readKeeperWithRelease fileCalls
  (fun path handle => AlignedKeeperCacheCallbacks.modifyPending keeper pending (pushPending path handle))
local notation "writeStage" => LongKeeperStageCallbacks.stage stage pending (AlignedKeeperCacheCallbacks.modifyPending keeper)
local notation "syncPaths" => AlignedKeeperCacheCallbacks.syncPaths keeper (DiskDirectory.path directory) cached active pending

/-- Follow the marked branch of the successful source recovery. The
read-only preparation gives this repair its exact plan and measured
keeper extent at the heap where it starts. -/
theorem reachedMarkedPreparation
    (bootstrap : EStateM IO.Error heap Reopened) {entry checked marked repaired : heap}
    {metadata : IO.FS.Metadata} {reopened : Reopened}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (stat (directory.file .wal))) entry = .ok () checked)
    (marker : optionalMetadataWith (stat (directory.file .walBoundary)) checked = .ok (some metadata) marked)
    (returned : recoverHealthyMarkedWithRefs fileCalls directoryCalls callbacks cached active pending remove stage
      rename stat directory bootstrap entry = .ok reopened repaired) :
    ∃ (plan : Plan) (extent : Nat) (prepared : heap),
      prepareBoundedMarkedFromReaders directory
        (readIntegrityCheckpointSized directory ((fileCalls.readOptional directory) (directory.file .manifest))
          fileCalls.runSize fileCalls.runPrefix)
        (fileCalls.readOptional directory)
        (fun watermark length => readSelectedWithCachedExtents directory watermark length directoryCalls.run
          (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal readKeeper) marked = .ok (plan, reopened, extent) prepared ∧
      finishBoundedMarkedOpen directory plan extent remove writeStage syncPaths rename prepared = .ok () repaired := by
  have markedReturn : reopenMarkedBoundedWithCachedExtents directory (fileCalls.readOptional directory)
      fileCalls.runSize fileCalls.runPrefix directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
      fileCalls.seal readKeeper remove writeStage syncPaths rename marked = .ok reopened repaired := by
    simpa only [recoverHealthyMarkedWithRefs, recoverSegmentedWalWith, Bind.bind, EStateM.bind, flat, marker, Option.isSome, ↓reduceIte] using returned
  let prepare := prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory ((fileCalls.readOptional directory) (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix)
    (fileCalls.readOptional directory)
    (fun watermark length => readSelectedWithCachedExtents directory watermark length directoryCalls.run
      (MarkedWalExtentReports.inspect fileCalls) fileCalls.seal readKeeper)
  change ((do
    let (plan, loaded, extent) ← prepare
    finishBoundedMarkedOpen directory plan extent remove writeStage syncPaths rename
    pure loaded) marked) = _ at markedReturn
  simp only [Bind.bind, EStateM.bind] at markedReturn
  cases prepared : prepare marked with
  | error cause reached => simp [prepared] at markedReturn
  | ok result reached =>
    obtain ⟨plan, loaded, extent⟩ := result
    simp only [prepared] at markedReturn
    cases finished : finishBoundedMarkedOpen directory plan extent remove writeStage syncPaths rename reached with
    | error cause failed => simp [finished] at markedReturn
    | ok value complete =>
      cases value
      simp only [finished, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at markedReturn
      exact ⟨plan, extent, reached, markedReturn.1 ▸ prepared, markedReturn.2 ▸ finished⟩

end MarkedPreparation

section Readers

variable {heap : Type}

/-- A successful bounded preparation determines its exact successful
checkpoint, marker and WAL callbacks. The pure replay preserves the
last callback heap and supplies the returned plan and table. -/
theorem reachedMarkedReaders (directory : DiskDirectory)
    (checkpoint : EStateM IO.Error heap (Option (PackedTable × UInt64)))
    (optional : FilePath → EStateM IO.Error heap (Option ByteArray))
    (wal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat))
    {entry prepared : heap} {plan : Plan} {opened : Reopened} {extent : Nat}
    (returned : prepareBoundedMarkedFromReaders directory checkpoint optional wal entry =
      .ok (plan, opened, extent) prepared) :
    ∃ selected afterCheckpoint marker afterMarker length reads writes table keeperStart keeperBytes,
      checkpoint entry = .ok selected afterCheckpoint ∧
      optional (directory.file .walBoundary) afterCheckpoint = .ok (some marker) afterMarker ∧
      WAL.Boundary.decode marker = .ok length ∧
      wal ((selected.getD (.empty, 0)).1.committed.toNat) length afterMarker = .ok (reads, extent) prepared ∧
      recoverMarkedWalSegments (selected.getD (.empty, 0)).1 length reads.files = .ok (writes, table) ∧
      reads.files.getLast? = some (keeperStart, keeperBytes) ∧
      plan = ⟨length.toNat / WAL.frameSize, keeperStart, reads.newer, keeperBytes⟩ ∧
      opened = ⟨table, (selected.getD (.empty, 0)).2, length, keeperStart⟩ := by
  simp only [prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind] at returned
  cases gotCheckpoint : checkpoint entry with
  | error cause reached => simp [gotCheckpoint] at returned
  | ok selected afterCheckpoint =>
    simp only [gotCheckpoint] at returned
    cases gotMarker : optional (directory.file .walBoundary) afterCheckpoint with
    | error cause reached => simp [gotMarker] at returned
    | ok marker afterMarker =>
      cases marker with
      | none => simp [gotMarker, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      | some marker =>
        simp only [gotMarker] at returned
        cases decoded : WAL.Boundary.decode marker with
        | error cause => simp [decoded, Except.mapError, liftExcept, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
        | ok length =>
          simp only [decoded, Except.mapError, liftExcept, EStateM.bind, Pure.pure, EStateM.pure] at returned
          cases gotWal : wal (selected.getD (.empty, 0)).1.committed.toNat length afterMarker with
          | error cause reached => simp [gotWal] at returned
          | ok payload reached =>
            obtain ⟨reads, physical⟩ := payload
            simp only [gotWal] at returned
            cases replayed : recoverMarkedWalSegments (selected.getD (.empty, 0)).1 length reads.files with
            | error cause => simp [replayed, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
            | ok value =>
              obtain ⟨writes, table⟩ := value
              simp only [replayed, EStateM.pure] at returned
              cases lastKeeper : reads.files.getLast? with
              | none => simp [lastKeeper, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
              | some entry =>
                obtain ⟨keeperStart, bytes⟩ := entry
                simp only [lastKeeper, EStateM.pure, EStateM.Result.ok.injEq, Prod.mk.injEq] at returned
                obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := returned
                exact ⟨selected, afterCheckpoint, marker, afterMarker, length, reads, writes, table, keeperStart, bytes,
                  rfl, by simp only [gotMarker], by simp only [decoded],
                  by simp only [gotWal], by simp only [replayed], by simp only [lastKeeper], rfl, rfl⟩

end Readers

end Alvoki.Storage.DiskSession
