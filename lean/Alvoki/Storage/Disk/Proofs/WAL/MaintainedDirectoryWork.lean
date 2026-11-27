import Alvoki.Storage.Disk.Proofs.Session.MaintainedRecoveryWork
import Alvoki.Storage.Disk.Proofs.WAL.WalInventoryWork

namespace Alvoki.Storage

open System CheckpointPublication WalSegmentRepair

/-- All nonmanaged entries observed by the checked stream. This includes
discarded dot entries and visible metadata, scratch and unrelated names. -/
def OpenedDirectoryScan.unmanagedNameCount (scan : OpenedDirectoryScan) : Nat :=
  scan.names.length - scan.visibleNames.length +
    (scan.visibleNames.filter fun name => (parseRunFileName name).isNone && (parseWalSegmentName name).isNone).length

private theorem managedNamePartition (directory : DiskDirectory) (names : List String) :
    (names.filterMap parseRunFileName).length + (names.filterMap parseWalSegmentName).length +
      (names.filter fun name => (parseRunFileName name).isNone && (parseWalSegmentName name).isNone).length =
      names.length := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    cases run : parseRunFileName name with
    | none =>
      cases wal : parseWalSegmentName name <;> simp [run, wal] <;> omega
    | some address =>
      obtain ⟨generation, index⟩ := address
      have notWal : parseWalSegmentName name = none := by
        cases wal : parseWalSegmentName name with
        | none => rfl
        | some first =>
          have same := (parseRunFileName_eq_some_iff.mp run).symm.trans
            (parseWalSegmentName_eq_some_iff.mp wal)
          have paths : directory.file (.run generation index) = directory.file (.walSegment first) := by
            exact congrArg (fun basename => FilePath.mk (directory.path.toString ++ "/" ++ basename)) same
          obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive paths
          contradiction
      simp [run, notWal]
      omega

private theorem namedRunCount_filter (files : RunFiles) (catalog : List RunAddress) :
    (catalog.filter fun address => (files address.1 address.2).isSome).length =
      files.namedRunTotal (fun _ => 1) catalog := by
  induction catalog with
  | nil => rfl
  | cons address rest ih =>
    obtain ⟨generation, index⟩ := address
    cases binding : files generation index <;> simp [binding, RunFiles.namedRunTotal] at ih ⊢ <;> omega

private theorem listedRunCount (files : RunFiles) {catalog : List RunAddress} {names : List String}
    (uniqueNames : names.Nodup) (uniqueCatalog : catalog.Nodup)
    (covered : ∀ generation index bytes, files generation index = some bytes → (generation, index) ∈ catalog)
    (listed : ∀ generation index, renderRunFileName generation index ∈ names ↔ (files generation index).isSome) :
    (names.filterMap parseRunFileName).length = files.namedRunTotal (fun _ => 1) catalog := by
  have uniqueRuns : (names.filterMap parseRunFileName).Nodup := by
    apply uniqueNames.filterMap parseRunFileName
    intro left right different address run next other same
    subst next
    obtain ⟨generation, index⟩ := address
    exact different ((parseRunFileName_eq_some_iff.mp run).trans (parseRunFileName_eq_some_iff.mp other).symm)
  rw [← namedRunCount_filter]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup uniqueRuns (uniqueCatalog.filter _)).mpr
  intro address
  obtain ⟨generation, index⟩ := address
  simp only [List.mem_filter, List.mem_filterMap]
  refine ⟨?_, fun present => ⟨_, (listed generation index).mpr present.2, parseRunFileName_render ..⟩⟩
  rintro ⟨name, member, parsed⟩
  rw [parseRunFileName_eq_some_iff.mp parsed] at member
  have present := (listed generation index).mp member
  obtain ⟨bytes, stored⟩ := Option.isSome_iff_exists.mp present
  exact ⟨covered _ _ _ stored, present⟩

private theorem listedKeeperCount {names : List String} {keeper : Nat}
    (uniqueNames : names.Nodup)
    (listed : ∀ first, renderWalSegmentName first ∈ names ↔ first = keeper) :
    (names.filterMap parseWalSegmentName).length = 1 := by
  have uniqueWal : (names.filterMap parseWalSegmentName).Nodup := by
    apply uniqueNames.filterMap parseWalSegmentName
    intro left right different first wal next other same
    subst next
    exact different ((parseWalSegmentName_eq_some_iff.mp wal).trans
      (parseWalSegmentName_eq_some_iff.mp other).symm)
  have exactlyKeeper : (names.filterMap parseWalSegmentName).Perm [keeper] := by
    apply (List.perm_ext_iff_of_nodup uniqueWal (by simp)).mpr
    intro first
    rw [List.mem_singleton, ← listed first]
    exact ⟨fun member => by
        obtain ⟨name, present, parsed⟩ := List.mem_filterMap.mp member
        exact (parseWalSegmentName_eq_some_iff.mp parsed) ▸ present,
      fun member => List.mem_filterMap.mpr ⟨_, member, parseWalSegmentName_render first⟩⟩
  exact exactlyKeeper.length_eq

end Alvoki.Storage

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

/-- The stable full listing reports exactly the canonical managed names
in the maintained image. The selected-file custody proof alone does not
supply this agreement for unselected runs or preexisting WAL names. -/
structure CheckpointHeldOpen.ManagedDirectoryNames {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) (wal : WalSegmentImage) : Prop where
  runs : ∀ generation index, renderRunFileName generation index ∈ opened.held.listing.scan.visibleNames ↔
    (physical.durable generation index).isSome
  segments : ∀ first, renderWalSegmentName first ∈ opened.held.listing.scan.visibleNames ↔
    first ∈ wal.segments.map WalSegment.first

def CheckpointHeldOpen.directoryWork {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) : DirectoryReadWork :=
  (CheckedDirectoryReadReport.scanned opened.held.listing.scan).work

/-- Count parser visits and the extent sort with the actual listing and
metadata callbacks of this admitted cached open. -/
noncomputable def CheckpointHeldOpen.inventoryWork {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) : WalInventoryWork :=
  let reported := opened.wal.operations.reported
  readWalSegmentExtentsWithWork directory (fun path => .ok (reported.inventory.reports.lstat path))
    (reported.entries.toList.map (·.fileName))

/-- Counts at the checked listing and subsequent cached WAL inventory
in the same held open. -/
structure CheckpointHeldOpen.DirectoryWorkBound {input directory history physical}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical) (catalog : List RunAddress)
    (managedRunCap unmanagedCap : Nat) : Prop where
  openCount : opened.directoryWork.opendirCalls = 1
  closeCount : opened.directoryWork.closedirCalls = 1
  readCount : opened.directoryWork.readdirCalls = physical.durable.namedRunTotal (fun _ => 1) catalog +
    opened.held.listing.scan.unmanagedNameCount + 2
  readBound : opened.directoryWork.readdirCalls ≤ managedRunCap + unmanagedCap + 2
  visited : opened.inventoryWork.visited.length = opened.directoryWork.materializedEntries
  visitBound : opened.inventoryWork.visited.length ≤ managedRunCap + unmanagedCap + 1
  extents : opened.inventoryWork.result.map List.length = .ok 1
  comparisons : opened.inventoryWork.comparisons = 0

/-- One clean checked directory scan consumes the surviving run names,
the single retained WAL keeper name, and the supplied unmanaged budget.
Only the visible entries reach the WAL parser. The actual extent sort
receives one extent, so it makes zero comparisons. -/
theorem CheckpointHeldOpen.maintainedDirectoryWork {input directory history physical wal}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image history}
    (opened : CheckpointHeldOpen input directory layout physical)
    (agreement : opened.ManagedDirectoryNames wal) (keeperOnly : wal.segments = [wal.active])
    {catalog : List RunAddress} (unique : catalog.Nodup)
    (covered : ∀ generation index bytes, physical.durable generation index = some bytes →
      (generation, index) ∈ catalog)
    {managedRunCap unmanagedCap : Nat}
    (runs : physical.durable.namedRunTotal (fun _ => 1) catalog ≤ managedRunCap)
    (unmanaged : opened.held.listing.scan.unmanagedNameCount ≤ unmanagedCap) :
    opened.DirectoryWorkBound catalog managedRunCap unmanagedCap := by
  let scan := opened.held.listing.scan
  let reported := opened.wal.operations.reported
  change scan.unmanagedNameCount ≤ unmanagedCap at unmanaged
  have reportedNames : reported.inventory.names = scan.visibleNames := by
    rw [← reported.names, opened.held.checkedListing.1]
    simp [scan, OpenedDirectoryScan.entries_toList, List.map_map, Function.comp_def]
  have uniqueScan := reportedNames ▸ reported.unique
  have walNames (first : Nat) : renderWalSegmentName first ∈ scan.visibleNames ↔ first = wal.active.first := by
    have names := agreement.segments first
    simpa [keeperOnly] using names
  have runNames := listedRunCount physical.durable uniqueScan unique covered agreement.runs
  have walCount := listedKeeperCount uniqueScan walNames
  have total : scan.names.length =
      physical.durable.namedRunTotal (fun _ => 1) catalog + scan.unmanagedNameCount + 1 := by
    have counting := managedNamePartition directory scan.visibleNames
    have visible : scan.visibleNames.length ≤ scan.names.length := List.length_filter_le ..
    dsimp only [OpenedDirectoryScan.unmanagedNameCount]
    omega
  have offsets := reported.inventory.scanRegular (expected := [wal.active.first]) reported.unique (by simp)
    (fun first => by simpa only [reportedNames, List.mem_singleton] using walNames first)
    (by
      intro first member
      have actual := (reported.present first).mp
        (reportedNames ▸ (walNames first).mpr (List.mem_singleton.mp member))
      obtain ⟨metadata, probe, regular, _⟩ := reported.regular first actual
      exact ⟨metadata, probe, regular⟩)
  have projection :
      (readWalSegmentExtentsWith (m := Except IO.Error) directory
        (fun path => .ok (reported.inventory.reports.lstat path)) (reported.entries.toList.map (·.fileName))).map
        (List.map Prod.fst) = .ok [wal.active.first] := by
    rw [reported.inventory.reports.walSegmentExtents_offsets, reported.names]
    exact offsets
  let work := opened.inventoryWork
  have spec := readWalSegmentExtentsWithWork_spec directory
    (fun path => .ok (reported.inventory.reports.lstat path)) (reported.entries.toList.map (·.fileName))
  rw [show readWalSegmentExtentsWithWork directory
    (fun path => .ok (reported.inventory.reports.lstat path)) (reported.entries.toList.map (·.fileName)) = work from rfl] at spec
  rw [← spec.1] at projection
  obtain ⟨extents, result, extentCount⟩ :
      ∃ extents, work.result = .ok extents ∧ extents.length = 1 := by
    cases returned : work.result with
    | error cause => simp [returned, Except.map] at projection
    | ok extents =>
      have addresses : extents.map Prod.fst = [wal.active.first] := Except.ok.inj (by
        simpa only [returned, Except.map] using projection)
      exact ⟨extents, rfl, by simpa using congrArg List.length addresses⟩
  have success := spec.2
  rw [result] at success
  have visited : work.visited.length = scan.visibleNames.length := by
    rw [success.1, reported.names, reportedNames]
  have compared := success.2 0 (by simp [extentCount])
  have noComparisons : work.comparisons = 0 := by simpa using compared
  refine ⟨rfl, rfl, ?_, ?_, visited, ?_, ?_, noComparisons⟩
  · change scan.names.length + 1 = physical.durable.namedRunTotal (fun _ => 1) catalog + scan.unmanagedNameCount + 2
    omega
  · change scan.names.length + 1 ≤ _
    omega
  · rw [visited]
    have visible : scan.visibleNames.length ≤ scan.names.length := List.length_filter_le ..
    omega
  · change work.result.map List.length = _
    simp [result, Except.map, extentCount]

/-- Apply the complete maintenance name budget to the exact held packet
that returns the next admitted session. The handoff reports agreement
for all canonical names and a cap on everything else in that stream. -/
theorem MaintainedRecoveryBounds.closeAndReopenDirectoryWork {directory descriptor input}
    {before maintained : SegmentedWriterState} (bounds : MaintainedRecoveryBounds before maintained)
    (ready : maintained.RetainedReady directory descriptor) (positive : before.wal.PositiveSeals)
    (closed : CleanUnlockReports directory descriptor)
    {catalog : List RunAddress} (unique : catalog.Nodup)
    (covered : ∀ generation index bytes, maintained.published.durable generation index = some bytes →
      (generation, index) ∈ catalog)
    {managedRunCap unmanagedCap : Nat}
    (runs : maintained.published.durable.namedRunTotal (fun _ => 1) catalog ≤ managedRunCap)
    (observed : closed.HeldReopenObservations (before := maintained) input (fun opened =>
      opened.ManagedDirectoryNames maintained.wal ∧ opened.held.listing.scan.unmanagedNameCount ≤ unmanagedCap)) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory maintained).image maintained.history)
      (opened : CheckpointHeldOpen input directory layout maintained.published) (after : SegmentedWriterState),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after ∧
      opened.DirectoryWorkBound catalog managedRunCap unmanagedCap := by
  obtain ⟨layout, opened, after, endpoint, names, unmanaged⟩ :=
    ready.closeWithHeldEvidence closed _ observed
  exact ⟨layout, opened, after, endpoint,
    opened.maintainedDirectoryWork names (bounds.singleSegment positive) unique covered runs unmanaged⟩

end Alvoki.Storage.DiskSession
