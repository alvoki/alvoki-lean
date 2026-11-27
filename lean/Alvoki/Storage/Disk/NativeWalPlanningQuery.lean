import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Collection.WalCollectionCompletePlan

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A successful whole-file metadata read uses the object seen by the
no-follow probe. The native read projection and the observed temporary
descriptor lifetime refer to that same call. -/
structure WalPlanMetadataFile (paths : OpenPathReadReports) (entry : DescriptorInventory)
    (view : DirectoryReadNamespace) (root : DeviceInode) (path : FilePath) (name : String) (bytes : ByteArray) where
  child : RunChildLookup root name view
  stat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  metadata : IO.FS.Metadata
  probed : stat path = .ok (metadata, child.child)
  projected : paths.lstat path = (stat path).map Prod.fst
  regular : metadata.type = .file
  slot : DescriptorSlot
  free : ∀ old ∈ entry.slots, old.address ≠ slot.address
  fresh : entry.references slot.description = []
  openedObject : entry.inode slot.description = view.modelObject child.child
  openRead : FilePath → EStateM IO.Error DescriptorInventory DescriptorSlot
  readAll : DescriptorSlot → EStateM IO.Error DescriptorInventory ByteArray
  release : DescriptorSlot → EStateM IO.Error DescriptorInventory Unit
  opened : openRead path entry = .ok slot (entry.insert slot free)
  read : readAll slot (entry.insert slot free) = .ok bytes (entry.insert slot free)
  closed : release slot (entry.insert slot free) = .ok () ((entry.insert slot free).afterDrops [slot.closeEvent])
  payload : paths.readBin path = .ok bytes

namespace WalPlanMetadataFile

theorem returned (seen : WalPlanMetadataFile paths entry view root path name bytes) :
    paths.readOptional path = .ok (some bytes) := by
  have stamp : paths.lstat path = .ok seen.metadata := by
    rw [seen.projected, seen.probed]
    rfl
  simp [OpenPathReadReports.readOptional, readOptionalDatabaseFile, readOptionalDatabaseFileWithMetadata,
    stamp, seen.regular, seen.payload, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem releases (seen : WalPlanMetadataFile paths entry view root path name bytes) :
    seen.release seen.slot (entry.insert seen.slot seen.free) = .ok () entry := by
  rw [seen.closed, ← List.nil_append [seen.slot.closeEvent], DescriptorInventory.insert_thenClose]
  cases entry with
  | mk slots distinct inode =>
    simp only [EStateM.Result.ok.injEq, true_and, DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
    apply List.filter_eq_self.mpr
    intro old member
    by_cases process : old.reference.process = seen.slot.reference.process
    · have different : old.reference.fd ≠ seen.slot.reference.fd := fun same =>
        seen.free old member (Prod.ext process same)
      simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process, different]
    · simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process]

/-- The observed open, read and release return the bytes supplied by the
whole-file callback, with the same entry inventory. -/
theorem readAndClose (seen : WalPlanMetadataFile paths entry view root path name bytes) :
    (do
      let slot ← seen.openRead path
      let payload ← seen.readAll slot
      seen.release slot
      pure payload : EStateM IO.Error DescriptorInventory ByteArray) entry = .ok bytes entry ∧
    paths.readBin path = .ok bytes ∧
    ((entry.insert seen.slot seen.free).afterDrops [seen.slot.closeEvent]).references seen.slot.description = [] := by
  refine ⟨?_, seen.payload, ?_⟩
  · simp only [Bind.bind, EStateM.bind, seen.opened, seen.read, seen.releases, Pure.pure, EStateM.pure]
  · rw [(EStateM.Result.ok.inj (seen.closed.symm.trans seen.releases)).2]
    exact seen.fresh

end WalPlanMetadataFile

/-- The optional manifest can be absent. Each present metadata read
has a temporary open, full read and release on its reported inode. -/
inductive WalPlanOptionalRead (paths : OpenPathReadReports) (entry : DescriptorInventory)
    (view : DirectoryReadNamespace) (root : DeviceInode) (path : FilePath) (name : String) : Option ByteArray → Type where
  | missing (file message : String) (probe : paths.lstat path = .error (.noFileOrDirectory file 2 message))
      (absent : view.child root name = none) : WalPlanOptionalRead paths entry view root path name none
  | present {bytes} (seen : WalPlanMetadataFile paths entry view root path name bytes) :
      WalPlanOptionalRead paths entry view root path name (some bytes)

theorem WalPlanOptionalRead.returned (seen : WalPlanOptionalRead paths entry view root path name bytes) :
    paths.readOptional path = .ok bytes := by
  cases seen with
  | missing file message probe _ =>
    simp [OpenPathReadReports.readOptional, readOptionalDatabaseFile, readOptionalDatabaseFileWithMetadata,
      probe, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | present report => exact report.returned

def WalPlanOptionalRead.Released (seen : WalPlanOptionalRead paths entry view root path name bytes) : Prop :=
  match seen with
  | .missing .. => True
  | .present file => file.release file.slot (entry.insert file.slot file.free) = .ok () entry

theorem WalPlanOptionalRead.releases (seen : WalPlanOptionalRead paths entry view root path name bytes) : seen.Released := by
  cases seen with
  | missing => trivial
  | present file => exact file.releases

/-- The planner has reached and closed the checked directory listing
after its optional manifest and marker reads. Each observation starts
at the reached ready custody. The successful read handles are released
before the listing, and other observed drops retain the entry slots. -/
structure NativeWalPlanPrefix (state : NativeReadyState) (calls : WalCollectionReads) where
  lifetime : HeldDirectoryReadLifetime state.census state.owner
  directorySlot : lifetime.directorySlot = state.directorySlot
  manifest : WalPlanOptionalRead calls.paths state.census lifetime.namespaceView lifetime.root
    (state.session.directory.file .manifest) "MANIFEST" state.writer.target.pair.manifest
  marker : WalPlanOptionalRead calls.paths state.census lifetime.namespaceView lifetime.root
    (state.session.directory.file .walBoundary) "WAL.commit" state.writer.target.pair.walBoundary
  listing : HeldDirectoryScan lifetime
  listed : calls.list state.session.directory.path = (CheckedDirectoryReadReport.scanned listing.scan).result state.session.directory.path
  noEarlierDrops : listing.beforeOpen = []
  retained : ∀ slot ∈ state.census.slots, ∀ drop ∈ lifetime.drops, drop.removes slot.reference = false

namespace NativeWalPlanPrefix

variable {state : NativeReadyState} {calls : WalCollectionReads}

private theorem preservesInventory (entry : DescriptorInventory) (drops : List LockReferenceDrop)
    (retained : ∀ slot ∈ entry.slots, ∀ drop ∈ drops, drop.removes slot.reference = false) :
    entry.afterDrops drops = entry := by
  cases entry with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
    apply List.filter_eq_self.mpr
    intro slot member
    exact List.all_eq_true.mpr fun drop reported => by simp [retained slot member drop reported]

theorem retainsCensus (observed : NativeWalPlanPrefix state calls) : observed.listing.afterClose = state.census := by
  rw [observed.listing.afterClose_eq]
  exact preservesInventory state.census observed.lifetime.drops observed.retained

theorem readListing (observed : NativeWalPlanPrefix state calls) :
    calls.list state.session.directory.path = .ok (observed.listing.scan.entries state.session.directory.path) :=
  observed.listed.trans (CheckedDirectoryReadReport.scan_complete state.session.directory.path
    observed.listing.eof observed.listing.closed observed.listing.complete).1

/-- The two metadata reads and the directory stream have separate
observed temporary slots. The extent operations following the list are
no-follow stats, so they have no temporary handle to release. -/
theorem releases (observed : NativeWalPlanPrefix state calls) :
    observed.manifest.Released ∧ observed.marker.Released ∧
    observed.listing.Custody ∧ observed.listing.afterClose = state.census :=
  ⟨observed.manifest.releases, observed.marker.releases, observed.listing.custody, observed.retainsCensus⟩

end NativeWalPlanPrefix

/-- The successful extent scan sees every canonical retained segment.
An error comes from the first failing canonical probe in the actual
directory traversal, after each preceding entry was accepted. -/
inductive NativeWalPlanExtents {state : NativeReadyState} {calls : WalCollectionReads}
    (observed : NativeWalPlanPrefix state calls) where
  | complete (unique : (observed.lifetime.namespaceView.names observed.lifetime.root).Nodup)
      (canonical : ∀ first object, observed.lifetime.namespaceView.child observed.lifetime.root
        (renderWalSegmentName first) = some object → first ∈ state.writer.wal.segments.map WalSegment.first)
      (stat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode))
      (extent : ∀ segment ∈ state.writer.wal.segments,
        WalCollectionExtentStat calls state.session.directory observed.lifetime.namespaceView observed.lifetime.root stat segment)
  | rejected (cause : IO.Error) (before after : List String) (first : Nat)
      (ordered : ((observed.listing.scan.entries state.session.directory.path).toList.map (·.fileName)) =
        before ++ renderWalSegmentName first :: after)
      (accepted : ∀ name ∈ before, ∃ found, readWalSegmentExtentWith state.session.directory calls.inspect name = .ok found)
      (probe : calls.inspect (state.session.directory.file (.walSegment first)) = .error cause ∨
        ∃ checked, calls.inspect (state.session.directory.file (.walSegment first)) = .ok checked ∧
          classifyWalSegmentLookup (state.session.directory.file (.walSegment first)) first checked = .error cause)

private theorem extentScanError (directory : DiskDirectory) (calls : WalCollectionReads) (before after : List String)
    (failed : String) (cause : IO.Error)
    (accepted : ∀ name ∈ before, ∃ found, readWalSegmentExtentWith directory calls.inspect name = .ok found)
    (error : readWalSegmentExtentWith directory calls.inspect failed = .error cause) :
    readWalSegmentExtentsWith directory calls.inspect (before ++ failed :: after) = .error cause := by
  suffices (before ++ failed :: after).filterMapM (readWalSegmentExtentWith directory calls.inspect) = .error cause by
    simp [readWalSegmentExtentsWith, this, Bind.bind, Except.bind]
  induction before with
  | nil => simp [List.filterMapM_cons, error, Bind.bind, Except.bind]
  | cons name rest ih =>
    obtain ⟨found, read⟩ := accepted name List.mem_cons_self
    have later := ih (fun tail member => accepted tail (List.mem_cons_of_mem _ member))
    cases found <;> simp [List.filterMapM_cons, read, later, Bind.bind, Except.bind]

private theorem planAfterExtentError {state : NativeReadyState} {calls : WalCollectionReads}
    (observed : NativeWalPlanPrefix state calls) (ready : state.writer.RetainedReady state.session.directory state.session.descriptor)
    {cause : IO.Error} (failed : readWalSegmentExtentsWith state.session.directory calls.inspect
      ((observed.listing.scan.entries state.session.directory.path).toList.map (·.fileName)) = .error cause) :
    calls.plan state.session.directory state.writer.installed = .error cause := by
  have generation := SelectedIntegrityCheckpoint.collectionGeneration ready.resumed.selected
  dsimp only at generation
  rw [← ready.resumed.generation] at generation
  have count : state.writer.installed.walBytes = state.writer.target.range.through * WAL.frameSize := by
    rw [ready.resumed.bytes, ready.resumed.through, WAL.encode_size, Nat.mul_comm]
  have pair : DirectoryPublication.Bindings.mk state.writer.target.pair.manifest state.writer.target.pair.walBoundary =
      state.writer.target.pair := by cases state.writer.target.pair; rfl
  unfold WalCollectionReads.plan planWalCollectionWith
  simp only [Bind.bind, Except.bind, observed.manifest.returned, observed.marker.returned, generation, Except.mapError,
    liftExcept, Pure.pure, Except.pure]
  rw [pair, state.writer.target.decoded]
  simp only [count, ↓reduceIte, observed.readListing, failed]

namespace NativeWalPlanExtents

variable {state : NativeReadyState} {calls : WalCollectionReads} {observed : NativeWalPlanPrefix state calls}

def result : NativeWalPlanExtents observed → Except IO.Error (List Nat)
  | .complete .. => .ok state.writer.wal.collectionOffsets
  | .rejected cause .. => .error cause

theorem plans (extents : NativeWalPlanExtents observed) (valid : state.Valid) :
    calls.plan state.session.directory state.writer.installed = extents.result := by
  cases extents with
  | complete unique canonical stat measurements =>
    exact valid.retained.completeObservedWalPlan calls
      ⟨state.census, state.owner, valid.owner, observed.lifetime, observed.listing, observed.listed, unique, canonical, stat, measurements⟩
      observed.manifest.returned observed.marker.returned
  | rejected cause before after first names accepted probe =>
    have failed : readWalSegmentExtentWith state.session.directory calls.inspect (renderWalSegmentName first) = .error cause := by
      unfold readWalSegmentExtentWith
      rw [show parseWalSegmentName (renderWalSegmentName first) = some first from parseWalSegmentName_render first]
      rcases probe with rejected | ⟨checked, read, rejected⟩
      · simp [rejected, Bind.bind, Except.bind]
      · simp [read, rejected, Bind.bind, Except.bind]
        rfl
    exact planAfterExtentError observed valid.retained (names.symm ▸ extentScanError _ _ before after _ cause accepted failed)

theorem eligibleInOrder (extents : NativeWalPlanExtents observed) (valid : state.Valid)
    {offsets : List Nat} (returned : extents.result = .ok offsets) :
    offsets = state.writer.wal.collectionOffsets ∧ offsets.Pairwise (· < ·) ∧
      ∀ first, first ∈ offsets ↔ ∃ segment ∈ state.writer.wal.sealed,
        state.writer.wal.Eligible segment ∧ segment.first = first := by
  cases extents with
  | rejected => contradiction
  | complete =>
    have exactOffsets := (Except.ok.inj returned).symm
    subst offsets
    refine ⟨rfl, ?_, ?_⟩
    · have sorted := (List.pairwise_append.mp valid.retained.layout.ordered).1
      exact (sorted.filter _).map _ (fun _ _ earlier => earlier.1)
    · intro first
      simp only [WalSegmentImage.collectionOffsets, List.mem_map, List.mem_filter, WalSegmentImage.canRemove_iff]
      exact ⟨fun ⟨segment, ⟨stored, covered⟩, atFirst⟩ => ⟨segment, stored, covered, atFirst⟩,
        fun ⟨segment, stored, covered, atFirst⟩ => ⟨segment, ⟨stored, covered⟩, atFirst⟩⟩

end NativeWalPlanExtents

/-- The operation-level report bundles only the reached filesystem
callbacks and the local extent outcome. -/
structure NativeWalPlanningObservation (state : NativeReadyState) where
  calls : WalCollectionReads
  read : NativeWalPlanPrefix state calls
  extents : NativeWalPlanExtents read

/-- The query runs the public planner at the reached phase with no
mutation or ledger entry. A success returns all eligible sealed offsets
in their model order. A rejected extent returns the reached error. -/
theorem NativeReadPosition.plansWalCollection (current : NativeReadPosition history log)
    (observed : NativeWalPlanningObservation current.state) :
    let reached := (current.state.session.phase, ⟨(current.state.cache, current.state.files.image), current.state.files.owners⟩)
    observed.calls.runPlan current.state.session.directory reached = (match observed.extents.result with
      | .ok offsets => .ok offsets reached
      | .error cause => .error cause reached) ∧
    observed.read.manifest.Released ∧ observed.read.marker.Released ∧ observed.read.listing.Custody ∧
    observed.read.listing.afterClose = current.state.census ∧ current.state.Valid ∧
    InstalledClientReplay log current.reads history current.state.writer.installed current.state.session := by
  have valid := current.readPrefix.refines.1
  obtain ⟨manifest, marker, stream, census⟩ := observed.read.releases
  refine ⟨?_, manifest, marker, stream, census, valid, current.readPrefix.guardedReplay⟩
  rw [valid.phase, WalCollectionReads.runPlan_ready, observed.extents.plans valid]
  rfl

end Alvoki.Storage.DiskSession
