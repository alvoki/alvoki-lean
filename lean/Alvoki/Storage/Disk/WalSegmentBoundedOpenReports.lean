import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.WalSegmentReadPlan
import Alvoki.Storage.Disk.WalSegmentRetryReads

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- Successful primitive reads use the visible directory and the same
exclusive owner for the whole attempt. Only the selected runs and sealed
payloads need successful binary reads. The keeper report returns its
marker-selected bytes and the physical size including any unread tail.
The canonical WAL descriptors contain the selected keeper prefix. -/
structure HealthyBoundedWalReports (directory : DiskDirectory) (owners : DiskSession.LockOwners)
    (descriptor : Nat) (wal : WalSegmentImage) (pair : DirectoryPublication.Bindings) (watermark : Nat)
    (durable : CheckpointPublication.RunFiles) (tail : ByteArray) where
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  entries : Array IO.FS.DirEntry
  listing : list directory.path = .ok entries
  reports : OpenPathReadReports
  readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix
  held : owners.Owns directory descriptor
  unique : (entries.toList.map (·.fileName)).Nodup
  names : ∀ first, renderWalSegmentName first ∈ entries.toList.map (·.fileName) ↔
    first ∈ wal.segments.map WalSegment.first
  regular : ∀ first ∈ wal.segments.map WalSegment.first, ∃ metadata,
    reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
      metadata.type = .file ∧ metadata.numLinks = 1
  manifest : reports.readOptional (directory.file .manifest) = .ok pair.manifest
  marker : reports.readOptional (directory.file .walBoundary) = .ok pair.walBoundary
  runs : ∀ bytes manifest, pair.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
      (reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
        durable manifest.header.generation index
  sealed : ∀ segment ∈ (wal.readDescriptors watermark).dropLast,
    reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes
  keeper : readPrefix (directory.file (.walSegment wal.active.first)) wal.active.bytes.size =
    .ok ⟨wal.active.bytes, (wal.active.bytes ++ tail).size⟩

/-- The manifest and scoped run reports execute the strict checkpoint
loader on the selected durable run vector. -/
theorem HealthyBoundedWalReports.readCheckpoint {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint) :
    readIntegrityCheckpoint (raw.reports.readOptional (directory.file .manifest))
      (fun generation index => raw.reports.readBin (directory.file (.run generation index)))
      (fun result => result.mapError IO.userError) = .ok checkpoint :=
  raw.reports.readIntegrityCheckpoint_exact directory selected raw.manifest raw.runs

/-- Interpret the prefix report against the exact visible whole file.
The visible contents come from the file model, so this needs no whole-file
read at the keeper path. -/
theorem HealthyBoundedWalReports.readVisibleKeeper {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {image : FileImage} {bytes : ByteArray} (observed : image.keeper.active = some bytes)
    (selected : image.keeper.active = some (wal.active.bytes ++ tail)) :
    raw.readPrefix (directory.file (.walSegment wal.active.first)) wal.active.bytes.size =
      .ok ⟨bytes.extract 0 wal.active.bytes.size, bytes.size⟩ := by
  rw [Option.some.inj (observed.symm.trans selected), ByteArray.extract_append_eq_left rfl]
  exact raw.keeper

private theorem scanRegularSegmentNames
    (reports : OpenPathReadReports) (directory : DiskDirectory) (names : List String)
    (regular : ∀ name ∈ names, ∀ first, parseWalSegmentName name = some first →
      ∃ metadata, reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧ metadata.type = .file) :
    ∃ offsets, reports.walSegmentOffsets directory names = .ok offsets := by
  suffices ∃ offsets, names.filterMapM
      (probeListedWalSegment (reports.probeWalSegment directory)) = .ok offsets by
    obtain ⟨offsets, scan⟩ := this
    exact ⟨offsets.mergeSort, by
      simp [OpenPathReadReports.walSegmentOffsets, scanWalSegmentOffsets, scan, Functor.map, Except.map]⟩
  induction names with
  | nil => exact ⟨[], rfl⟩
  | cons name rest ih =>
    obtain ⟨offsets, further⟩ := ih fun next member =>
      regular next (List.mem_cons_of_mem _ member)
    cases parsed : parseWalSegmentName name with
    | none =>
      exact ⟨offsets, by simp [List.filterMapM_cons, probeListedWalSegment, parsed, further,
        Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
    | some first =>
      obtain ⟨metadata, observed, kind⟩ := regular name List.mem_cons_self first parsed
      exact ⟨first :: offsets, by simp [List.filterMapM_cons, probeListedWalSegment, parsed,
        OpenPathReadReports.probeWalSegment, classifyWalSegmentLookup, observed, kind, further,
        Bind.bind, Except.bind, Pure.pure, Except.pure] <;> rfl⟩

/-- Complete raw listing and regular metadata identify the exact sorted
segment addresses without assuming success of a preparation worker. -/
theorem HealthyBoundedWalReports.scan {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history) :
    raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName)) =
      .ok (wal.segments.map WalSegment.first) := by
  obtain ⟨offsets, scanned⟩ := scanRegularSegmentNames raw.reports directory _ (by
    intro name listed first parsed
    rw [parseWalSegmentName_eq_some_iff.mp parsed] at listed
    obtain ⟨metadata, observed, kind, _⟩ := raw.regular first ((raw.names first).mp listed)
    exact ⟨metadata, observed, kind⟩)
  let inventory : LockedWalSegmentInventory directory :=
    ⟨owners, descriptor, raw.held, raw.entries.toList.map (·.fileName), raw.reports⟩
  have exactOffsets := inventory.offsets_eq scanned raw.unique
    (layout.ordered.map WalSegment.first (fun _ _ ordered => ordered.1)) (by
      intro first
      constructor
      · intro member
        obtain ⟨metadata, observed, kind, _⟩ := raw.regular first member
        exact ⟨(raw.names first).mpr member, metadata, observed, kind⟩
      · intro present
        exact (raw.names first).mp present.1)
  rw [scanned, exactOffsets]

private theorem readSealedSegmentReports (reports : OpenPathReadReports) (directory : DiskDirectory)
    (sealed : List WalSegment)
    (reads : ∀ segment ∈ sealed, reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes) :
    readWalSegmentPayloadsWith directory reports.readBin (sealed.map WalSegment.first) =
      .ok (sealed.map WalSegment.bytes) := by
  induction sealed with
  | nil => rfl
  | cons segment rest ih =>
    have head := reads segment List.mem_cons_self
    have tail := ih fun later member => reads later (List.mem_cons_of_mem _ member)
    simp only [readWalSegmentPayloadsWith, List.map_cons, List.mapM_cons, head, Bind.bind, Except.bind]
    change (Except.map (segment.bytes :: ·) (readWalSegmentPayloadsWith directory reports.readBin
      (rest.map WalSegment.first))) = _
    rw [tail]
    rfl

private theorem layoutFirstAtOrBeforeEnd {wal : WalSegmentImage} {history : List WAL.Write}
    (layout : wal.ReadLayout history) {segment : WalSegment} (member : segment ∈ wal.segments) :
    segment.first ≤ history.length := by
  rw [← layout.activeEnd]
  rcases List.mem_append.mp member with sealed | active
  · have ordered := (List.pairwise_append.mp layout.ordered).2.2 segment sealed wal.active (by simp)
    exact Nat.le_trans (Nat.le_of_lt ordered.1) (layout.forward wal.active (List.mem_append_right _ (by simp)))
  · obtain rfl := List.mem_singleton.mp active
    exact layout.forward wal.active member

/-- Raw bounded reads derive the exact keeper request, payload order and
physical size. The whole-file reference read of the keeper is unnecessary. -/
theorem HealthyBoundedWalReports.readSelectedBounded {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history)
    {through : Nat} (atEnd : through = history.length) (covered : watermark ≤ through)
    {count : UInt64} (absolute : count.toNat = through * frameSize)
    {first : Nat}
    (selected : selectWalSegmentReads (wal.segments.map WalSegment.first) watermark =
      some (first, (wal.readDescriptors watermark).map WalSegment.first)) :
    readSelectedWithPrefix directory watermark count raw.list (fun path => .ok (raw.reports.lstat path))
      raw.reports.readBin raw.readPrefix =
      .ok (⟨(wal.readDescriptors watermark).map (fun segment => (segment.first, segment.bytes)), []⟩,
        (wal.active.bytes ++ tail).size) := by
  obtain ⟨sealed, split⟩ := wal.readDescriptors_endsActive watermark
  have sealedExact : (wal.readDescriptors watermark).dropLast = sealed := by simp [split]
  have allNeeded : ∀ start ∈ (wal.readDescriptors watermark).map WalSegment.first, decide (start ≤ through) = true := by
    intro start member
    obtain ⟨segment, selected, rfl⟩ := List.mem_map.mp member
    have present : segment ∈ wal.segments := by
      unfold WalSegmentImage.readDescriptors at selected
      split at selected
      · exact (List.mem_filter.mp selected).1
      · exact List.mem_append_right _ selected
    exact decide_eq_true (atEnd ▸ layoutFirstAtOrBeforeEnd layout present)
  have addresses : selectWalSegmentReadsThrough (wal.segments.map WalSegment.first) watermark through =
      some (sealed.map WalSegment.first ++ [wal.active.first], []) := by
    unfold selectWalSegmentReadsThrough
    rw [selected]
    change some (((wal.readDescriptors watermark).map WalSegment.first).takeWhile _,
      ((wal.readDescriptors watermark).map WalSegment.first).dropWhile _) = _
    have taken := List.takeWhile_append_of_pos (l₂ := []) allNeeded
    have dropped := List.dropWhile_append_of_pos (l₂ := []) allNeeded
    simp only [List.append_nil, List.takeWhile_nil, List.dropWhile_nil] at taken dropped
    exact congrArg some (by rw [taken, dropped, split]; simp)
  have counted : count.toNat / frameSize = through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have keeperSize : wal.active.bytes.size = (through - wal.active.first) * frameSize := by
    rw [layout.activeBytes, WAL.encode_size, List.length_drop, atEnd, Nat.mul_comm]
  have payloads := readSealedSegmentReports raw.reports directory sealed (by simpa only [sealedExact] using raw.sealed)
  have probe : probeWalSegmentWith directory (fun path => .ok (raw.reports.lstat path)) =
      raw.reports.probeWalSegment directory := by
    funext start
    simp only [probeWalSegmentWith, OpenPathReadReports.probeWalSegment, Bind.bind, Except.bind]
    cases classifyWalSegmentLookup (directory.file (.walSegment start)) start
      (raw.reports.lstat (directory.file (.walSegment start))) <;> rfl
  have scan := raw.scan layout
  change scanWalSegmentOffsets (raw.reports.probeWalSegment directory) _ = _ at scan
  rw [← probe] at scan
  have kept := readSelectedWithPrefix_reported directory watermark count raw.list
    (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix
    ⟨aligned, counted.symm ▸ covered⟩ raw.listing scan (counted.symm ▸ addresses) payloads
    (by rw [counted, ← keeperSize]; exact raw.keeper) (counted.symm ▸ keeperSize)
    (by rw [counted, ← keeperSize, ByteArray.size_append]; exact Nat.le_add_right ..)
  rw [kept, split]
  have zipped : (sealed.map WalSegment.first).zip (sealed.map WalSegment.bytes) =
      sealed.map (fun segment => (segment.first, segment.bytes)) := by
    exact (List.zip_of_prod (l := sealed.map WalSegment.first) (l' := sealed.map WalSegment.bytes)
      (xs := sealed.map (fun segment => (segment.first, segment.bytes)))
      (by simp [List.map_map, Function.comp_def]) (by simp [List.map_map, Function.comp_def])).symm
  rw [zipped, List.map_append]
  rfl

end Alvoki.Storage.WalSegmentRepair
