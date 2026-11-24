import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession
open WAL (frameSize)

/-- Read-only observations from the held directory, including later names
that only need metadata. Payload callbacks concern the selected seals and
keeper, whose prefix and physical extent come from the file image. -/
structure CachedRetryReadReports (directory : DiskDirectory) {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) where
  inventory : LockedWalSegmentInventory directory
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  entries : Array IO.FS.DirEntry
  listed : list directory.path = .ok entries
  names : entries.toList.map (·.fileName) = inventory.names
  unique : inventory.names.Nodup
  older : List Nat
  ordered : (older ++ (layout.sealed ++ [layout.keeper]).map WalSegment.first ++
    image.later.visible).Pairwise (· < ·)
  present : ∀ first, renderWalSegmentName first ∈ inventory.names ↔
    first ∈ older ++ (layout.sealed ++ [layout.keeper]).map WalSegment.first ++ image.later.visible
  regular : ∀ first ∈ older ++ (layout.sealed ++ [layout.keeper]).map WalSegment.first ++ image.later.visible,
    ∃ metadata, inventory.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
      metadata.type = .file ∧ metadata.numLinks = 1
  readSeal : FilePath → Nat → Except IO.Error ByteArray
  readKeeper : FilePath → Nat → Nat → Except IO.Error ByteArray
  seals : ∀ segment ∈ layout.sealed, ∀ metadata,
    inventory.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
      image.kept segment.first = some segment.bytes ∧ metadata.byteSize.toNat = segment.bytes.size ∧
      segment.bytes.size < USize.size ∧ readSeal (directory.file (.walSegment segment.first)) segment.bytes.size =
        .ok segment.bytes
  keeper : ∀ metadata, inventory.reports.lstat (directory.file (.walSegment layout.keeper.first)) = .ok metadata →
    metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size ∧
    readKeeper (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size metadata.byteSize.toNat =
      .ok layout.keeper.bytes

private theorem chainOffsets_head {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history first segments) (nonempty : segments ≠ []) :
    ∃ rest, segments.map WalSegment.first = first :: rest := by
  cases chain with
  | endOfHistory => contradiction
  | cons => exact ⟨_, rfl⟩

/-- The actual cached scan derives both the exact selected payload vector
and the remaining visible names to prune. In particular, a healthy report
of these names need not open any of their payloads, and gaps stay intact. -/
theorem CachedRetryReadReports.readSelected {state : Type} {directory : DiskDirectory}
    {image : FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ image.later.visible, layout.range.through < start)
    {count : UInt64} (absolute : count.toNat = layout.range.through * frameSize) (initial : state) :
    let files := layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(layout.keeper.first, layout.keeper.bytes)]
    (readSelectedWithCachedExtents (m := EStateM IO.Error state) directory layout.range.watermark count
      (fun path => liftExcept (reported.list path))
      (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (reported.readSeal path size))
      (fun path size physical => liftExcept (reported.readKeeper path size physical))) initial =
      .ok (⟨files, image.later.visible⟩, (layout.keeper.bytes ++ layout.tail).size) initial := by
  intro files
  let segments := layout.sealed ++ [layout.keeper]
  let offsets := segments.map WalSegment.first
  have fileOffsets : files.map Prod.fst = offsets := by
    simp [offsets, segments, files, List.map_append, List.map_map, Function.comp_def]
  obtain ⟨rest, head⟩ : ∃ rest, offsets = layout.first :: rest := chainOffsets_head layout.chain (by simp [segments])
  have inventory := reported.inventory.scanRegular reported.unique reported.ordered reported.present (by
    intro first member
    obtain ⟨metadata, probe, regular, _⟩ := reported.regular first member
    exact ⟨metadata, probe, regular⟩)
  have atThrough : count.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have covered := (DirectoryPublication.Bindings.walRange_accounting layout.decoded).2.1
  have beforeFirst : ∀ start ∈ reported.older, start < layout.first := by
    intro start member
    have order := (List.pairwise_append.mp (List.pairwise_append.mp reported.ordered).1).2.2
    exact order _ member _ (show layout.first ∈ offsets from head ▸ List.mem_cons_self)
  have follows : ∀ start ∈ rest, layout.range.watermark < start ∧ start ≤ layout.range.through := by
    intro start member
    have inOffsets : start ∈ offsets := head ▸ List.mem_cons_of_mem _ member
    obtain ⟨segment, present, rfl⟩ := List.mem_map.mp inOffsets
    have laterStart : segment.first ∈ offsets.drop 1 := by rw [head, List.drop_one, List.tail_cons]; exact member
    exact ⟨following _ laterStart, layout.through ▸ layout.chain.startsWithin segment present⟩
  have chosen : selectWalSegmentReadsThrough (reported.older ++ offsets ++ image.later.visible)
      layout.range.watermark (count.toNat / frameSize) = some (files.map Prod.fst, image.later.visible) := by
    rw [atThrough, fileOffsets, head]
    exact selectWalSegmentReadsThrough_split reported.older rest image.later.visible layout.first
      layout.range.watermark layout.range.through layout.covers covered beforeFirst follows later
  have projection :
      (readWalSegmentExtentsWith (m := Except IO.Error) directory
        (fun path => .ok (reported.inventory.reports.lstat path)) (reported.entries.toList.map (·.fileName))).map
        (List.map Prod.fst) = .ok (reported.older ++ offsets ++ image.later.visible) := by
    rw [reported.inventory.reports.walSegmentExtents_offsets, reported.names]
    exact inventory
  obtain ⟨extents, scanned, exactOffsets⟩ : ∃ extents,
      readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (reported.inventory.reports.lstat path))
        (reported.entries.toList.map (·.fileName)) = .ok extents ∧
      extents.map Prod.fst = reported.older ++ offsets ++ image.later.visible := by
    cases measured : readWalSegmentExtentsWith (m := Except IO.Error) directory
        (fun path => .ok (reported.inventory.reports.lstat path)) (reported.entries.toList.map (·.fileName)) with
    | error cause => simp [measured, Except.map] at projection
    | ok extents =>
      exact ⟨extents, rfl, Except.ok.inj (by simpa only [measured, Except.map] using projection)⟩
  obtain ⟨required, selection, addresses⟩ : ∃ required,
      selectWalExtentsThrough extents layout.range.watermark (count.toNat / frameSize) =
        some (required, image.later.visible) ∧ required.map Prod.fst = files.map Prod.fst := by
    have actual := selectWalExtentsThrough_offsets extents layout.range.watermark (count.toNat / frameSize)
    rw [exactOffsets, chosen] at actual
    cases found : selectWalExtentsThrough extents layout.range.watermark (count.toNat / frameSize) with
    | none => rw [found] at actual; contradiction
    | some pair =>
      obtain ⟨required, later⟩ := pair
      rw [found] at actual
      obtain ⟨addresses, rfl⟩ := Prod.mk.inj (Option.some.inj actual)
      exact ⟨required, rfl, addresses⟩
  have spans : WalSegmentSpans (count.toNat / frameSize) files := by
    rw [atThrough]
    have chainSpans := layout.chain.checkReadSpans (tail := ByteArray.empty)
      (Nat.le_trans layout.covers covered) (Nat.le_of_eq layout.through)
    exact (checkWalSegmentSpans_iff ..).mp (by simpa [files] using chainSpans) |>.2
  have exactLast : files.getLast? = some (layout.keeper.first, layout.keeper.bytes) := by simp [files]
  have keeperWidth : layout.keeper.bytes.size = (count.toNat / frameSize - layout.keeper.first) * frameSize := by
    rw [atThrough]
    exact layout.target.trimmedSize
  have metadata (entry) (needed : entry ∈ required) :
      reported.inventory.reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2 :=
    OpenPathReadReports.walSegmentExtents_metadata scanned (selectWalExtentsThrough_required_subset selection needed)
  have payloads : CachedWalPayloadReports directory (count.toNat / frameSize) reported.readSeal reported.readKeeper
      required files (layout.keeper.bytes ++ layout.tail).size := by
    apply CachedWalPayloadReports.of_spans spans addresses exactLast keeperWidth
    · intro entry needed file selected same
      have sealed : file ∈ layout.sealed.map (fun segment => (segment.first, segment.bytes)) := by simpa [files] using selected
      obtain ⟨segment, present, rfl⟩ := List.mem_map.mp sealed
      exact (reported.seals segment present entry.2 (by simpa only [same] using metadata entry needed)).2
    · intro entry needed same
      obtain ⟨size, bytes⟩ := reported.keeper entry.2 (by simpa only [same] using metadata entry needed)
      exact ⟨size, by rw [size, ByteArray.size_append]; exact Nat.le_add_right .., bytes⟩
  have checked : count.toNat % frameSize = 0 ∧ layout.range.watermark ≤ count.toNat / frameSize :=
    ⟨aligned, atThrough.symm ▸ covered⟩
  exact readSelectedWithCachedExtents_reportedEffects directory layout.range.watermark count reported.list
    (fun path => .ok (reported.inventory.reports.lstat path)) reported.readSeal reported.readKeeper checked
    reported.listed scanned selection payloads initial

end Alvoki.Storage.WalSegmentRepair
