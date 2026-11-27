import Alvoki.Storage.Disk.Proofs.Collection.WalCollectionDirectoryFsync

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A no-follow stat of the canonical seal or keeper. It supplies the
exact length of that stable object in the held directory. -/
structure WalCollectionExtentStat (calls : WalCollectionReads) (directory : DiskDirectory)
    (view : DirectoryReadNamespace) (root : DeviceInode)
    (stat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)) (segment : WalSegment) where
  child : RunChildLookup root (renderWalSegmentName segment.first) view
  metadata : IO.FS.Metadata
  observed : stat (directory.file (.walSegment segment.first)) = .ok (metadata, child.child)
  projected : calls.paths.lstat (directory.file (.walSegment segment.first)) =
    (stat (directory.file (.walSegment segment.first))).map Prod.fst
  kind : metadata.type = .file
  links : metadata.numLinks = 1
  size : metadata.byteSize.toNat = segment.bytes.size

theorem WalCollectionExtentStat.lstat {calls directory view root stat segment}
    (seen : WalCollectionExtentStat calls directory view root stat segment) :
    calls.paths.lstat (directory.file (.walSegment segment.first)) = .ok seen.metadata := by
  rw [seen.projected, seen.observed]
  rfl

theorem WalCollectionExtentStat.inspect {calls directory view root stat segment}
    (seen : WalCollectionExtentStat calls directory view root stat segment) :
    calls.inspect (directory.file (.walSegment segment.first)) = .ok (.ok seen.metadata) := by
  simp [WalCollectionReads.inspect, inspectWalSegmentWith, seen.lstat, checkPrivateRegularWith, seen.kind,
    seen.links, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- The successful directory stream uses the writer's live lock and
captured parent. Its non-dot names exhaust that namespace. Every
canonical binding corresponds to a retained WAL descriptor, and the
same held no-follow probes establish each descriptor's physical size. -/
structure WalCollectionInventoryReport (calls : WalCollectionReads) (directory : DiskDirectory)
    (descriptor : Nat) (wal : WalSegmentImage) where
  descriptors : DescriptorInventory
  owner : DescriptorSlot
  ownerDescription : owner.description = descriptor
  lifetime : HeldDirectoryReadLifetime descriptors owner
  listing : HeldDirectoryScan lifetime
  listed : calls.list directory.path = (CheckedDirectoryReadReport.scanned listing.scan).result directory.path
  unique : (lifetime.namespaceView.names lifetime.root).Nodup
  canonical : ∀ first object, lifetime.namespaceView.child lifetime.root (renderWalSegmentName first) = some object →
    first ∈ wal.segments.map WalSegment.first
  stat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  extent : ∀ segment ∈ wal.segments,
    WalCollectionExtentStat calls directory lifetime.namespaceView lifetime.root stat segment

namespace WalCollectionInventoryReport

variable {calls : WalCollectionReads} {directory : DiskDirectory} {descriptor : Nat} {wal : WalSegmentImage}

def entries (report : WalCollectionInventoryReport calls directory descriptor wal) : Array IO.FS.DirEntry :=
  report.listing.scan.entries directory.path

def names (report : WalCollectionInventoryReport calls directory descriptor wal) : List String :=
  report.entries.toList.map (·.fileName)

def extents (report : WalCollectionInventoryReport calls directory descriptor wal) : List (Nat × IO.FS.Metadata) :=
  wal.segments.attach.map fun segment => (segment.val.first, (report.extent segment.val segment.property).metadata)

theorem enumerated (report : WalCollectionInventoryReport calls directory descriptor wal) :
    calls.list directory.path = .ok report.entries ∧
      report.names.Perm (report.lifetime.namespaceView.names report.lifetime.root) ∧
      report.names.Nodup ∧ report.listing.Custody := by
  obtain ⟨actual, names⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    report.listing.eof report.listing.closed report.listing.complete
  have exactNames : report.names.Perm (report.lifetime.namespaceView.names report.lifetime.root) := by
    simpa only [WalCollectionInventoryReport.names, WalCollectionInventoryReport.entries, report.listing.sameRoot] using names
  exact ⟨report.listed.trans actual, exactNames, exactNames.symm.nodup report.unique, report.listing.custody⟩

theorem bound (report : WalCollectionInventoryReport calls directory descriptor wal)
    (segment : WalSegment) (member : segment ∈ wal.segments) :
    report.lifetime.namespaceView.child report.lifetime.root (renderWalSegmentName segment.first) =
      some (report.extent segment member).child.child := by
  let seen := (report.extent segment member).child
  simpa only [seen.atRoot, seen.atName] using seen.binds

theorem listedCanonical (report : WalCollectionInventoryReport calls directory descriptor wal) (first : Nat) :
    renderWalSegmentName first ∈ report.names ↔ first ∈ wal.segments.map WalSegment.first := by
  rw [report.enumerated.2.1.mem_iff, report.lifetime.namespaceView.namesExact]
  constructor
  · rintro ⟨object, child⟩
    exact report.canonical first object child
  · rintro member
    obtain ⟨segment, seen, rfl⟩ := List.mem_map.mp member
    exact ⟨_, report.bound segment seen⟩

theorem regular (report : WalCollectionInventoryReport calls directory descriptor wal)
    (first : Nat) (member : first ∈ wal.segments.map WalSegment.first) :
    ∃ metadata, calls.paths.lstat (directory.file (.walSegment first)) = .ok metadata ∧
      metadata.type = .file ∧ metadata.numLinks = 1 := by
  obtain ⟨segment, listed, rfl⟩ := List.mem_map.mp member
  let seen := report.extent segment listed
  exact ⟨seen.metadata, seen.lstat, seen.kind, seen.links⟩

theorem physical (report : WalCollectionInventoryReport calls directory descriptor wal)
    (segment : WalSegment) (member : segment ∈ wal.segments) {metadata : IO.FS.Metadata}
    (seen : calls.paths.lstat (directory.file (.walSegment segment.first)) = .ok metadata) :
    metadata.byteSize.toNat = segment.bytes.size := by
  rw [Except.ok.inj (seen.symm.trans (report.extent segment member).lstat)]
  exact (report.extent segment member).size

theorem starts (report : WalCollectionInventoryReport calls directory descriptor wal)
    {owners : LockOwners} (held : owners.Owns directory descriptor) {history : List WAL.Write} (layout : wal.ReadLayout history) :
    calls.paths.walSegmentOffsets directory report.names = .ok (wal.segments.map WalSegment.first) := by
  let inventory : LockedWalSegmentInventory directory := ⟨owners, descriptor, held, report.names, calls.paths⟩
  exact inventory.scanRegular report.enumerated.2.2.1 (layout.ordered.map WalSegment.first (fun _ _ order => order.1))
    report.listedCanonical fun first member => by
      obtain ⟨metadata, checked, kind, _⟩ := report.regular first member
      exact ⟨metadata, checked, kind⟩

private theorem scanNames (calls : WalCollectionReads) (directory : DiskDirectory) (names : List String)
    (regular : ∀ name ∈ names, ∀ first, parseWalSegmentName name = some first →
      ∃ metadata, calls.paths.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        calls.inspect (directory.file (.walSegment first)) = .ok (.ok metadata) ∧ metadata.type = .file) :
    ∃ extents, names.filterMapM (readWalSegmentExtentWith directory calls.inspect) = .ok extents ∧
      names.filterMapM (readWalSegmentExtentWith (m := Except IO.Error) directory
        (fun path => .ok (calls.paths.lstat path))) = .ok extents := by
  induction names with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons name tail ih =>
    obtain ⟨extents, inspected, raw⟩ := ih fun later member => regular later (List.mem_cons_of_mem _ member)
    cases parsed : parseWalSegmentName name with
    | none =>
      exact ⟨extents, by simp [List.filterMapM_cons, readWalSegmentExtentWith, parsed, inspected,
        Bind.bind, Except.bind, Pure.pure, Except.pure],
        by simp [List.filterMapM_cons, readWalSegmentExtentWith, parsed, raw, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
    | some first =>
      obtain ⟨metadata, seen, checked, kind⟩ := regular name List.mem_cons_self first parsed
      exact ⟨(first, metadata) :: extents,
        by simp [List.filterMapM_cons, readWalSegmentExtentWith, parsed, checked, classifyWalSegmentLookup, kind,
          inspected, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.toOption] <;> rfl,
        by simp [List.filterMapM_cons, readWalSegmentExtentWith, parsed, seen, classifyWalSegmentLookup, kind,
          raw, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.toOption] <;> rfl⟩

private def fromLstat (calls : WalCollectionReads) (directory : DiskDirectory) (first : Nat) :
    Option (Nat × IO.FS.Metadata) :=
  (calls.paths.lstat (directory.file (.walSegment first))).toOption.map (first, ·)

private theorem extentsFromStarts (calls : WalCollectionReads) (directory : DiskDirectory)
    (extents : List (Nat × IO.FS.Metadata))
    (observed : ∀ extent ∈ extents, calls.paths.lstat (directory.file (.walSegment extent.1)) = .ok extent.2) :
    extents = (extents.map Prod.fst).filterMap (fromLstat calls directory) := by
  induction extents with
  | nil => rfl
  | cons extent tail ih =>
    have later := ih (fun next member => observed next (List.mem_cons_of_mem _ member))
    obtain ⟨first, metadata⟩ := extent
    simp only [List.map_cons, List.filterMap_cons, fromLstat, observed (first, metadata) List.mem_cons_self,
      Except.toOption, Option.map_some]
    exact congrArg ((first, metadata) :: ·) later

theorem extentStarts (report : WalCollectionInventoryReport calls directory descriptor wal) :
    report.extents.map Prod.fst = wal.segments.map WalSegment.first := by
  simp [extents, List.map_map, Function.comp_def]

/-- The guarded extent scan returns the exact metadata vector in canonical
offset order. Both the guard and the extent use the same no-follow probe. -/
theorem scanned (report : WalCollectionInventoryReport calls directory descriptor wal)
    {owners : LockOwners} (held : owners.Owns directory descriptor) {history : List WAL.Write}
    (layout : wal.ReadLayout history) :
    readWalSegmentExtentsWith directory calls.inspect report.names = .ok report.extents ∧
    readWalSegmentExtentsWith (m := Except IO.Error) directory
      (fun path => .ok (calls.paths.lstat path)) report.names = .ok report.extents := by
  obtain ⟨unsorted, inspected, raw⟩ := scanNames calls directory report.names (by
    intro name member first parsed
    rw [parseWalSegmentName_eq_some_iff.mp parsed] at member
    obtain ⟨segment, stored, rfl⟩ := List.mem_map.mp ((report.listedCanonical first).mp member)
    let stat := report.extent segment stored
    exact ⟨stat.metadata, stat.lstat, stat.inspect, stat.kind⟩)
  let extents := unsorted.mergeSort (fun left right => left.1 ≤ right.1)
  have scanned : readWalSegmentExtentsWith directory calls.inspect report.names = .ok extents := by
    simp [readWalSegmentExtentsWith, inspected, Bind.bind, Except.bind, Pure.pure, Except.pure, extents]
  have plain : readWalSegmentExtentsWith (m := Except IO.Error) directory
      (fun path => .ok (calls.paths.lstat path)) report.names = .ok extents := by
    simp [readWalSegmentExtentsWith, raw, Bind.bind, Except.bind, Pure.pure, Except.pure, extents]
  have projected := calls.paths.walSegmentExtents_offsets directory report.names
  rw [plain, report.starts held layout] at projected
  have starts : extents.map Prod.fst = wal.segments.map WalSegment.first := Except.ok.inj projected
  have expected (extent : Nat × IO.FS.Metadata) (member : extent ∈ report.extents) :
      calls.paths.lstat (directory.file (.walSegment extent.1)) = .ok extent.2 := by
    obtain ⟨segment, _, rfl⟩ := List.mem_map.mp member
    exact (report.extent segment.val segment.property).lstat
  have same := (extentsFromStarts calls directory extents
    (fun _ member => OpenPathReadReports.walSegmentExtents_metadata plain member)).trans
      (congrArg (List.filterMap (fromLstat calls directory)) (starts.trans report.extentStarts.symm))
  have exactExtents := same.trans (extentsFromStarts calls directory report.extents expected).symm
  exact ⟨exactExtents ▸ scanned, exactExtents ▸ plain⟩

private theorem dropCovered (first : Nat) (extents : List (Nat × IO.FS.Metadata))
    (ordered : (extents.map Prod.fst).Pairwise (· < ·)) :
    (extents.dropWhile fun entry => entry.1 < first) =
      extents.filter fun entry => first ≤ entry.1 := by
  induction extents with
  | nil => rfl
  | cons extent rest ih =>
    obtain ⟨earlier, later⟩ := List.pairwise_cons.mp ordered
    by_cases covered : extent.1 < first
    · have skip := Nat.not_le_of_gt covered
      simpa [List.dropWhile_cons, List.filter_cons, covered, skip] using ih later
    · have kept := Nat.le_of_not_gt covered
      rw [List.dropWhile_cons_of_neg (p := fun entry : Nat × IO.FS.Metadata => decide (entry.1 < first))
        (by simpa using covered)]
      symm
      apply List.filter_eq_self.mpr
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact decide_eq_true kept
      · have after := earlier entry.1 (List.mem_map_of_mem later)
        exact decide_eq_true (Nat.le_trans kept (Nat.le_of_lt after))

private theorem chainStart {history : List WAL.Write} {start : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history start segments) :
    segments.head?.elim history.length WalSegment.first = start := by
  cases chain <;> rfl

private theorem suffixChecks {history : List WAL.Write} {start : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history start segments) (keeper : WalSegment)
    (ends : segments.getLast? = some keeper)
    (ordered : (segments.map WalSegment.first).Pairwise (· < ·))
    {extents : List (Nat × IO.FS.Metadata)}
    (starts : extents.map Prod.fst = segments.map WalSegment.first)
    (sizes : ∀ entry ∈ extents, ∀ segment ∈ segments, segment.first = entry.1 →
      entry.2.byteSize.toNat = (segment.last - segment.first) * WAL.frameSize) :
    checkWalCollectionSuffix history.length keeper.first extents = true := by
  induction chain generalizing extents with
  | endOfHistory => simp at ends
  | @cons segment tail _ _ _ continued ih =>
    cases extents with
    | nil => simp at starts
    | cons entry rest =>
      have ⟨first, later⟩ := List.cons.inj starts
      have width := sizes entry List.mem_cons_self segment List.mem_cons_self first.symm
      cases tail with
      | nil =>
        have empty : rest = [] := List.map_eq_nil_iff.mp later
        have same : segment = keeper := Option.some.inj ends
        have endAt : history.length = segment.last := chainStart continued
        simp [empty, checkWalCollectionSuffix, first, ← same, width, endAt]
      | cons next tail =>
        cases rest with
        | nil => simp at later
        | cons nextEntry entries =>
          have ⟨nextFirst, _⟩ := List.cons.inj later
          have adjacent : next.first = segment.last := chainStart continued
          have nextOrdered := (List.pairwise_cons.mp ordered).1 next.first List.mem_cons_self
          have restChecked := ih ends (List.pairwise_cons.mp ordered).2 later
            (fun extent member piece listed same =>
              sizes extent (List.mem_cons_of_mem _ member) piece (List.mem_cons_of_mem _ listed) same)
          change (decide (entry.1 < nextEntry.1) && _ && checkWalCollectionSuffix _ _ (nextEntry :: entries)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          exact ⟨⟨by simpa [first, nextFirst] using nextOrdered, by simpa [first, nextFirst, adjacent] using width⟩,
            restChecked⟩

private theorem splitThrough {offsets : List Nat} (limit : Nat)
    (within : ∀ offset ∈ offsets, offset ≤ limit) :
    let needed := fun offset => decide (offset ≤ limit)
    offsets.takeWhile needed = offsets ∧ offsets.dropWhile needed = [] := by
  induction offsets with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    have firstWithin := within first List.mem_cons_self
    obtain ⟨kept, drop⟩ := ih (fun offset member => within offset (List.mem_cons_of_mem _ member))
    simp [firstWithin, kept, drop]

/-- The checked suffix succeeds on the complete stable inventory of a
retained writer. The same reported extents express the contiguous suffix
from the checkpoint watermark to the keeper's installed end. -/
theorem checks {state : SegmentedWriterState} (ready : state.RetainedReady directory descriptor)
    (report : WalCollectionInventoryReport calls directory descriptor state.wal) :
    checkWalCollectionInventory report.extents state.installed.activeFirst state.target.range = true := by
  let wal := state.wal
  let range := state.target.range
  let selected := wal.readDescriptors range.watermark
  have chosenPair : wal.Selects state.target.pair := ready.walPair ▸ List.mem_cons_self ..
  obtain ⟨first, _, _, chosen, chain, _⟩ := ready.layout.selects ready.valid chosenPair state.target.decoded
  change selectWalSegmentReads (wal.segments.map WalSegment.first) range.watermark =
    some (first, selected.map WalSegment.first) at chosen
  change WalSegment.Chain state.history first selected at chain
  have filtered : (wal.segments.map WalSegment.first).filter (fun offset => decide (first ≤ offset)) =
      selected.map WalSegment.first := by
    unfold selectWalSegmentReads at chosen
    cases best : ((wal.segments.map WalSegment.first).filter (fun offset => decide (offset ≤ range.watermark))).max? with
    | none => simp [best, Bind.bind, Option.bind] at chosen
    | some highest =>
      have result : (highest, (wal.segments.map WalSegment.first).filter (fun offset => decide (highest ≤ offset))) =
          (first, selected.map WalSegment.first) := by
        simpa [best, Bind.bind, Option.bind, Pure.pure] using chosen
      obtain ⟨rfl, exact⟩ := Prod.mk.inj result
      exact exact
  have endAt := ready.resumed.through.trans ready.layout.activeEnd.symm
  have limit (offset : Nat) (member : offset ∈ selected.map WalSegment.first) :
      offset ≤ range.through := by
    rw [← filtered] at member
    obtain ⟨segment, visible, rfl⟩ := List.mem_map.mp (List.mem_filter.mp member).1
    change segment.first ≤ state.target.range.through
    rw [endAt]
    rcases List.mem_append.mp visible with sealed | active
    · have before := (List.pairwise_append.mp ready.layout.ordered).2.2
        segment sealed wal.active (List.mem_singleton_self _)
      exact Nat.le_trans (Nat.le_of_lt before.1) (ready.layout.forward wal.active (List.mem_append_right _ (List.mem_singleton_self _)))
    · cases List.mem_singleton.mp active
      exact ready.layout.forward wal.active visible
  obtain ⟨needed, newer⟩ := splitThrough range.through limit
  have through : selectWalSegmentReadsThrough (report.extents.map Prod.fst) range.watermark range.through =
      some (selected.map WalSegment.first, []) := by
    unfold selectWalSegmentReadsThrough
    rw [report.extentStarts, chosen]
    exact congrArg some (Prod.ext needed newer)
  obtain ⟨sealed, ends⟩ := wal.readDescriptors_endsActive range.watermark
  have last : selected.getLast? = some wal.active := by
    rw [show selected = sealed ++ [wal.active] from ends]
    simp
  have nonempty : selected ≠ [] := by
    intro empty
    simp [empty] at last
  have firstAt : (selected.map WalSegment.first).head? = some first := by
    rw [List.head?_map]
    cases reached : selected with
    | nil => exact (nonempty reached).elim
    | cons firstSeal rest =>
      have start := chainStart chain
      rw [reached] at start
      exact congrArg some start
  have orderedExtents : (report.extents.map Prod.fst).Pairwise (· < ·) := by
    rw [report.extentStarts]
    exact ready.layout.ordered.map _ (fun _ _ earlier => earlier.1)
  have suffixStarts :
      (report.extents.dropWhile fun extent => extent.1 < first).map Prod.fst = selected.map WalSegment.first := by
    rw [dropCovered first report.extents orderedExtents]
    change (report.extents.filter ((fun offset => decide (first ≤ offset)) ∘ Prod.fst)).map Prod.fst =
      selected.map WalSegment.first
    rw [← List.filter_map, report.extentStarts]
    exact filtered
  have ordered : (selected.map WalSegment.first).Pairwise (· < ·) := by
    rw [← filtered]
    exact (ready.layout.ordered.map _ (fun _ _ earlier => earlier.1)).filter _
  have sameKeeper := ready.resumed.keeper.trans ready.active
  have subset : selected.Sublist wal.segments := by
    unfold selected WalSegmentImage.readDescriptors
    split
    · exact List.filter_sublist
    · exact List.sublist_append_right _ _
  have found := (report.scanned ready.held ready.layout).2
  have checked := suffixChecks chain wal.active last ordered suffixStarts (by
    intro extent member segment listed same
    rw [dropCovered first report.extents orderedExtents] at member
    have measured := OpenPathReadReports.walSegmentExtents_metadata found (List.mem_filter.mp member).1
    rw [← same] at measured
    exact (report.physical segment (subset.subset listed) measured).trans (chain.member_byteSize listed))
  change checkWalCollectionInventory report.extents state.installed.activeFirst range = true
  unfold checkWalCollectionInventory
  rw [through]
  cases offsets : selected.map WalSegment.first with
  | nil => simp [offsets] at firstAt
  | cons head tail =>
    rw [offsets] at firstAt
    have atFirst := Option.some.inj firstAt
    have count : range.through = state.history.length := ready.resumed.through
    simpa only [atFirst, sameKeeper, count] using checked

end WalCollectionInventoryReport

/-- A complete clean listing and exact guarded extents determine the
planner's entire ordered result and pass the installed suffix check.
The keeper stat verifies its span. The covered seals supply their own
sizes, independently of the gaps between their names. -/
theorem SegmentedWriterState.RetainedReady.completeObservedWalPlan
    {directory : DiskDirectory} {descriptor : Nat} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) (calls : WalCollectionReads)
    (inventory : WalCollectionInventoryReport calls directory descriptor state.wal)
    (manifest : calls.paths.readOptional (directory.file .manifest) = .ok state.target.pair.manifest)
    (marker : calls.paths.readOptional (directory.file .walBoundary) = .ok state.target.pair.walBoundary) :
    calls.plan directory state.installed = .ok state.wal.collectionOffsets := by
  obtain ⟨scanned, raw⟩ := inventory.scanned ready.held ready.layout
  have keeper := ready.resumed.keeper.trans ready.active
  have sealAt (extent : Nat × IO.FS.Metadata) (member : extent ∈ inventory.extents)
      (notKeeper : extent.1 ≠ state.wal.active.first) :
      ∃ segment ∈ state.wal.sealed, segment.first = extent.1 := by
    have offset := List.mem_map_of_mem (f := Prod.fst) member
    rw [inventory.extentStarts] at offset
    obtain ⟨segment, listed, same⟩ := List.mem_map.mp offset
    rcases List.mem_append.mp listed with old | active
    · exact ⟨segment, old, same⟩
    · cases List.mem_singleton.mp active
      exact (notKeeper same.symm).elim
  have measured (extent : Nat × IO.FS.Metadata) (member : extent ∈ inventory.extents)
      (segment : WalSegment) (sealed : segment ∈ state.wal.sealed) (same : segment.first = extent.1) :
      extent.2.byteSize.toNat = segment.bytes.size := by
    apply inventory.physical segment (List.mem_append_left _ sealed)
    rw [same]
    exact OpenPathReadReports.walSegmentExtents_metadata raw member
  have planned := (ready.planObservedWalCollection calls manifest marker inventory.enumerated.1 scanned (inventory.checks ready) sealAt measured).1
  have exactOffsets := calls.paths.walCollectionOffsets_eq_extents directory state.installed.activeFirst state.target.decoded
    inventory.extents (fun _ member => OpenPathReadReports.walSegmentExtents_metadata raw member)
  rw [inventory.extentStarts, keeper] at exactOffsets
  have exactPlan := calls.paths.walCollectionOffsets_of_layout directory ready.layout ready.walPair
    (ready.walDirectorySettled.trans (congrArg (fun pair => [pair]) ready.walPair)) state.target.decoded
      inventory.regular (fun segment member _ read =>
        inventory.physical segment (List.mem_append_left _ member) read) ready.spans
  rw [keeper] at planned
  exact planned.trans (congrArg Except.ok (exactOffsets.symm.trans exactPlan))

/-- The actual full plan feeds the ordered unlinks and the final barrier
from the same rooted observation. When the barrier takes effect, every
eligible seal stays absent in every reported crash image. -/
theorem SegmentedWriterState.RetainedReady.collectsCompleteObservedWalPlan
    {directory : DiskDirectory} {descriptor : Nat} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) (calls : WalCollectionReads)
    (inventory : WalCollectionInventoryReport calls directory descriptor state.wal)
    (manifest : calls.paths.readOptional (directory.file .manifest) = .ok state.target.pair.manifest)
    (marker : calls.paths.readOptional (directory.file .walBoundary) = .ok state.target.pair.walBoundary)
    {effectView : DirectoryReadNamespace} {atBarrier : WalSealedUnlinkImage} {removed : List Nat}
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (unlinked : WalUnlinkPrefix directory inventory.lifetime.root removeFile state.wal.collectionOffsets
      inventory.lifetime.namespaceView (.start state.wal) [] none effectView atBarrier removed)
    (barrier : WalCollectionDirectoryFsync directory inventory.lifetime.root inventory.lifetime.namespaceView
      effectView descriptor atBarrier)
    (sameDirectory : barrier.handle.2.1 = inventory.lifetime.directorySlot)
    (sameWriter : barrier.writerSlot = inventory.owner) :
    inventory.lifetime.directorySlot ∈ barrier.reached.slots ∧
      inventory.owner ∈ barrier.reached.slots ∧
      (barrier.outcome.effective = true → barrier.after.crashSealed = [atBarrier.visible.sealed] ∧
        ∀ segment ∈ state.wal.sealed, state.wal.Eligible segment →
          ∀ sealed ∈ barrier.after.crashSealed, segment ∉ sealed) ∧
      calls.collectWithEffects directory removeFile barrier.syncDirectory
        (.ready state.installed, ⟨.start state.wal, state.owners⟩) =
        match barrier.outcome with
        | .completed => .ok () (.ready state.installed, ⟨barrier.after, state.owners⟩)
        | .errorBeforeEffect cause | .errorAfterEffect cause =>
          .error (IO.userError s!"sync failed for '{directory.path}': {cause}")
            (.poisoned, ⟨barrier.after, state.owners⟩) := by
  have planned := ready.completeObservedWalPlan calls inventory manifest marker
  obtain ⟨_, _, _, settles, _, returned⟩ := ready.reportedWalCollectionBarrier calls planned
    (fun _ member => member)
    (fun segment member => by rw [inventory.bound segment (List.mem_append_left _ member)]; rfl)
    removeFile unlinked barrier
  refine ⟨?_, ?_, ?_, returned⟩
  · simpa only [sameDirectory] using barrier.directoryLive
  · simpa only [sameWriter] using barrier.writerLive
  · intro effective
    obtain ⟨exactNames, absent⟩ := settles effective
    refine ⟨exactNames, ?_⟩
    intro segment old eligible sealed survived present
    have offset : segment.first ∈ state.wal.collectionOffsets := List.mem_map.mpr
      ⟨segment, List.mem_filter.mpr ⟨old, WalSegmentImage.canRemove_iff.mpr eligible⟩, rfl⟩
    exact absent segment.first offset sealed survived segment present rfl

end Alvoki.Storage.DiskSession
