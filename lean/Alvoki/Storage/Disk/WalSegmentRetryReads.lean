import Alvoki.Storage.Disk.WalSegmentReplayStability
import Alvoki.Storage.Disk.WalSegmentReopenEffects

namespace Alvoki.Storage

open System
open WAL (frameSize)

/-- The covering start and subsequent required files are separated from
ignored older names and unused later names. Later names can contain gaps. -/
theorem selectWalSegmentReadsThrough_split (older required later : List Nat) (first watermark through : Nat)
    (covers : first ≤ watermark) (bounded : watermark ≤ through)
    (olderBefore : ∀ start ∈ older, start < first)
    (requiredBounds : ∀ start ∈ required, watermark < start ∧ start ≤ through)
    (laterBeyond : ∀ start ∈ later, through < start) :
    selectWalSegmentReadsThrough (older ++ (first :: required) ++ later) watermark through =
      some (first :: required, later) := by
  let needed := first :: required
  have greatest : ((older ++ needed ++ later).filter fun start => decide (start ≤ watermark)).max? =
      some first := by
    apply List.max?_eq_some_iff.mpr
    refine ⟨by simp [needed, covers], ?_⟩
    intro start member
    obtain ⟨member, within⟩ := List.mem_filter.mp member
    have before : start ≤ watermark := of_decide_eq_true within
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact Nat.le_of_lt (olderBefore _ member)
      · rcases List.mem_cons.mp member with rfl | member
        · exact Nat.le_refl _
        · exact False.elim (Nat.not_lt_of_ge before (requiredBounds _ member).1)
    · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans before bounded) (laterBeyond _ member))
  have skip : (older.filter fun start => decide (first ≤ start)) = [] :=
    List.filter_eq_nil_iff.mpr fun start member found => Nat.not_le_of_lt (olderBefore _ member)
      (of_decide_eq_true found)
  have keep : (needed.filter fun start => decide (first ≤ start)) = needed := by
    apply List.filter_eq_self.mpr
    intro start member
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · exact decide_eq_true (Nat.le_trans covers (Nat.le_of_lt (requiredBounds _ member).1))
  have keepLater : (later.filter fun start => decide (first ≤ start)) = later :=
    List.filter_eq_self.mpr fun start member =>
      decide_eq_true (Nat.le_trans (Nat.le_trans covers bounded) (Nat.le_of_lt (laterBeyond _ member)))
  have throughNeeded : ∀ start ∈ needed, decide (start ≤ through) = true := by
    intro start member
    rcases List.mem_cons.mp member with rfl | member
    · exact decide_eq_true (Nat.le_trans covers bounded)
    · exact decide_eq_true (requiredBounds _ member).2
  have takeLater : later.takeWhile (fun start => decide (start ≤ through)) = [] := by
    cases later with
    | nil => rfl
    | cons start rest => simp [List.takeWhile, Nat.not_le_of_lt (laterBeyond _ (List.mem_cons_self ..))]
  have dropLater : later.dropWhile (fun start => decide (start ≤ through)) = later := by
    cases later with
    | nil => rfl
    | cons start rest => simp [List.dropWhile, Nat.not_le_of_lt (laterBeyond _ (List.mem_cons_self ..))]
  change selectWalSegmentReadsThrough (older ++ needed ++ later) watermark through = some (needed, later)
  have suffix : selectWalSegmentReads (older ++ needed ++ later) watermark = some (first, needed ++ later) := by
    simp only [selectWalSegmentReads, Bind.bind, Option.bind, greatest, Pure.pure]
    simp only [List.filter_append, skip, keep, keepLater, List.nil_append]
  rw [selectWalSegmentReadsThrough, suffix]
  change some ((needed ++ later).takeWhile _, (needed ++ later).dropWhile _) = some (needed, later)
  rw [List.takeWhile_append_of_pos throughNeeded, List.dropWhile_append_of_pos throughNeeded,
    takeLater, dropLater, List.append_nil]

private theorem readWalSegmentPayloads_reported (reports : OpenPathReadReports) (directory : DiskDirectory)
    (files : List (Nat × ByteArray))
    (reads : ∀ file ∈ files, reports.readBin (directory.file (.walSegment file.1)) = .ok file.2) :
    reports.readWalSegmentPayloads directory (files.map Prod.fst) = .ok (files.map Prod.snd) := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    have first := reads file List.mem_cons_self
    have remaining := ih (fun pair member => reads pair (List.mem_cons_of_mem _ member))
    simp only [OpenPathReadReports.readWalSegmentPayloads, readWalSegmentPayloadsWith, List.map_cons,
      List.mapM_cons, first, Bind.bind, Except.bind]
    change (Except.map (file.2 :: ·) (reports.readWalSegmentPayloads directory (rest.map Prod.fst))) = _
    rw [remaining]
    rfl

/-- Actual listed entries, canonical metadata reports and successful
payload reads yield the exact selected vector, in plan order. -/
theorem LockedWalSegmentInventory.readsThrough {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) (entries : Array IO.FS.DirEntry)
    (names : entries.toList.map (·.fileName) = inventory.names)
    {offsets : List Nat} (scanned : inventory.offsets = .ok offsets)
    (watermark : Nat) (length : UInt64) (files : List (Nat × ByteArray)) (later : List Nat)
    (aligned : length.toNat % frameSize = 0) (bounded : watermark ≤ length.toNat / frameSize)
    (plan : selectWalSegmentReadsThrough offsets watermark (length.toNat / frameSize) =
      some (files.map Prod.fst, later))
    (reads : ∀ file ∈ files, inventory.reports.readBin (directory.file (.walSegment file.1)) = .ok file.2) :
    readWalSegmentsThroughWith directory watermark length (fun _ => .ok entries)
      (fun path => .ok (inventory.reports.lstat path)) inventory.reports.readBin = .ok ⟨files, later⟩ := by
  change readWalSegmentsThroughWith directory watermark length (fun _ => .ok entries)
    (fun path => pure (inventory.reports.lstat path)) inventory.reports.readBin = .ok ⟨files, later⟩
  rw [OpenPathReadReports.readWalSegmentsThroughWith_reports]
  have payloads := readWalSegmentPayloads_reported inventory.reports directory files reads
  have zipped : (files.map Prod.fst).zip (files.map Prod.snd) = files := (List.zip_of_prod rfl rfl).symm
  change inventory.reports.walSegmentOffsets directory inventory.names = .ok offsets at scanned
  simp [aligned, bounded, names, scanned, plan, payloads, zipped,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A complete canonical listing determines the exact numeric order of an
admitted layout, including gaps among obsolete or later names. -/
theorem LockedWalSegmentInventory.offsets_eq {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets expected : List Nat}
    (scanned : inventory.offsets = .ok offsets) (unique : inventory.names.Nodup)
    (ordered : expected.Pairwise (· < ·))
    (names : ∀ first, first ∈ expected ↔ renderWalSegmentName first ∈ inventory.names ∧
      ∃ metadata, inventory.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        metadata.type = .file) : offsets = expected := by
  have sorted := OpenPathReadReports.walSegmentOffsets_strict scanned unique
  have uniqueOffsets : offsets.Nodup := sorted.imp Nat.ne_of_lt
  have uniqueExpected : expected.Nodup := ordered.imp Nat.ne_of_lt
  have perm := (List.perm_ext_iff_of_nodup uniqueOffsets uniqueExpected).mpr (fun first =>
    (OpenPathReadReports.mem_walSegmentOffsets scanned).trans (names first).symm)
  exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => False.elim (Nat.lt_asymm ab ba)) sorted ordered perm

/-- Durable files and a strictly valid checkpoint match one accepted loader
result. An absent manifest selects the empty starting state. -/
inductive SelectedIntegrityCheckpoint (durable : CheckpointPublication.RunFiles) :
    Option ByteArray → Option (PackedTable × UInt64) → Prop where
  | absent : SelectedIntegrityCheckpoint durable none none
  | present {bytes : ByteArray} {manifest : Manifest.IntegrityCheckpoint} {files : List ByteArray}
      {table : PackedTable} (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok manifest)
      (stored : (List.range manifest.header.runCount.toNat).mapM (durable manifest.header.generation) = some files)
      (loaded : loadIntegrityRunSet manifest files = .ok table) :
      SelectedIntegrityCheckpoint durable (some bytes) (some (table, manifest.header.generation))

private theorem toOption_mapM_reported {error payload : Type} (indices : List Nat)
    (read : Nat → Except error payload) (stored : Nat → Option payload)
    (exact : ∀ index ∈ indices, (read index).toOption = stored index) :
    (indices.mapM read).toOption = indices.mapM stored := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    have head := exact index List.mem_cons_self
    have tail := ih (fun i member => exact i (List.mem_cons_of_mem _ member))
    rw [List.mapM_cons, List.mapM_cons, ← head, ← tail]
    cases read index <;> cases rest.mapM read <;> rfl

/-- A healthy observation of the selected manifest and its named runs
executes the strict decoder on the exact ordered durable bytes. -/
theorem OpenPathReadReports.readIntegrityCheckpoint_exact (reports : OpenPathReadReports)
    (directory : DiskDirectory) {durable : CheckpointPublication.RunFiles} {binding : Option ByteArray}
    {checkpoint : Option (PackedTable × UInt64)} (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    (manifestRead : reports.readOptional (directory.file .manifest) = .ok binding)
    (runs : ∀ bytes manifest, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok manifest →
      ∀ index, index < manifest.header.runCount.toNat →
        (reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
          durable manifest.header.generation index) :
    readIntegrityCheckpoint (reports.readOptional (directory.file .manifest))
      (fun generation index => reports.readBin (directory.file (.run generation index)))
      (fun result => result.mapError IO.userError) = .ok checkpoint := by
  cases selected with
  | absent => simp [readIntegrityCheckpoint, manifestRead, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @present bytes manifest files table decoded stored loaded =>
    let read := fun index => reports.readBin (directory.file (.run manifest.header.generation index))
    have exact := toOption_mapM_reported (List.range manifest.header.runCount.toNat) read
      (durable manifest.header.generation) (fun index member => runs bytes manifest rfl decoded index
        (List.mem_range.mp member))
    rw [stored] at exact
    have reads : (List.range manifest.header.runCount.toNat).mapM read = .ok files := by
      cases result : (List.range manifest.header.runCount.toNat).mapM read with
      | error error => rw [result] at exact; contradiction
      | ok output =>
        rw [result] at exact
        exact congrArg Except.ok (Option.some.inj exact)
    dsimp only [read] at reads
    simp [readIntegrityCheckpoint, manifestRead, decoded, readCheckpointRunBytes_eq_mapM, reads, loaded,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]

theorem SelectedIntegrityCheckpoint.watermark {durable : CheckpointPublication.RunFiles}
    {binding : Option ByteArray} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint) :
    selectedCheckpointWatermark binding = some (checkpoint.getD (.empty, 0)).1.committed.toNat := by
  cases selected with
  | absent => rfl
  | @present bytes manifest files table decoded _ loaded =>
    obtain ⟨_, _, restored⟩ := loadRunSet_restored (loadIntegrityRunSet_iff.mp loaded).2
    have clock := (PackedTable.restore_spec restored).2.2.1
    simp [selectedCheckpointWatermark, Manifest.VersionedCheckpoint.decode_integrity decoded,
      Manifest.VersionedCheckpoint.header, Except.toOption, clock]

private theorem recoverMarkedWalSegments_spans {base : PackedTable} {count : UInt64}
    {files : List (Nat × ByteArray)} {selected : ByteArray} {table : PackedTable}
    (replayed : recoverMarkedWalSegments base count files = .ok (selected, table)) :
    checkSelectedWalSegmentSpans (count.toNat / frameSize) files = true := by
  cases files with
  | nil => simp [recoverMarkedWalSegments] at replayed
  | cons file rest =>
    obtain ⟨first, bytes⟩ := file
    by_cases checked : checkSelectedWalSegmentSpans (count.toNat / frameSize) ((first, bytes) :: rest) = true
    · exact checked
    · simp [recoverMarkedWalSegments, checked] at replayed

namespace WalSegmentRepair

/-- A retry listing describes the stable visible layout. The older addresses
are ignored, the selected sealed bytes precede the keeper, and later names
only need metadata. All successful reads use the directory's held lock. -/
structure RetryInventory (directory : DiskDirectory) (image : FileImage) (target : Target) where
  listing : LockedWalSegmentInventory directory
  entries : Array IO.FS.DirEntry
  names : entries.toList.map (·.fileName) = listing.names
  unique : listing.names.Nodup
  older : List Nat
  sealed : List (Nat × ByteArray)
  ordered : ((older ++ sealed.map Prod.fst ++ [target.first]) ++ image.later.visible).Pairwise (· < ·)
  present : ∀ first, first ∈ ((older ++ sealed.map Prod.fst ++ [target.first]) ++ image.later.visible) ↔
    renderWalSegmentName first ∈ listing.names ∧
      ∃ metadata, listing.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧ metadata.type = .file
  references : ∀ file ∈ sealed, image.kept file.1 = some file.2
  sealedReads : ∀ file ∈ sealed, ∀ bytes, image.kept file.1 = some bytes →
    listing.reports.readBin (directory.file (.walSegment file.1)) = .ok bytes
  keeperRead : ∀ bytes, image.keeper.active = some bytes →
    listing.reports.readBin (directory.file (.walSegment target.first)) = .ok bytes

/-- Healthy retry preparation uses the actual canonical directory entries
and read reports. The exact plan and reopened table are derived from the
surviving keeper and immutable preceding files, even after partial pruning. -/
theorem EffectTrace.prepareObservedRetry {directory : DiskDirectory} {target : Target}
    {initial after : FileImage} {oldPlan : Plan} (trace : EffectTrace target initial after)
    (old : Prepared initial target oldPlan) (observed : RetryInventory directory after target)
    {scanned : List Nat} (scan : observed.listing.offsets = .ok scanned)
    (first : Nat) (required : List Nat)
    (needed : observed.sealed.map Prod.fst ++ [target.first] = first :: required)
    (covers : first ≤ target.range.watermark)
    (olderBefore : ∀ start ∈ observed.older, start < first)
    (requiredBounds : ∀ start ∈ required, target.range.watermark < start ∧ start ≤ target.range.through)
    {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selectedCheckpoint : SelectedIntegrityCheckpoint durable target.pair.manifest checkpoint)
    (manifestObserved : observed.listing.reports.readOptional (directory.file .manifest) =
      .ok after.directory.active.manifest)
    (runReports : ∀ bytes manifest, target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
        (observed.listing.reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
          durable manifest.header.generation index)
    (markerObserved : observed.listing.reports.readOptional (directory.file .walBoundary) =
      .ok after.directory.active.walBoundary)
    {count : UInt64} {selected : ByteArray} {table : PackedTable}
    (oldCount : count.toNat = target.range.through * frameSize)
    (replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count
      (observed.sealed ++ [(target.first, oldPlan.keeperBytes)]) = .ok (selected, table)) :
    ∃ plan,
      Prepared after target plan ∧
      prepareMarkedWith directory observed.listing.reports.readOptional (fun _ => .ok observed.entries)
        (fun path => .ok (observed.listing.reports.lstat path)) observed.listing.reports.readBin =
        .ok (plan, ⟨table, (checkpoint.getD (.empty, 0)).2, count, target.first⟩) ∧
      recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count
        (observed.sealed ++ [(target.first, plan.keeperBytes)]) = .ok (selected, table) := by
  have valid := trace.valid old.pair old.keeperPrefix old.newer
  obtain ⟨extra, keeper⟩ := valid.keeper.activeValid
  let bytes := target.trimmed ++ extra
  let plan : Plan := ⟨target.range.through, target.first, after.later.visible, bytes⟩
  obtain ⟨watermark, covered, marker, length, visible, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have clock := Option.some.inj (selectedCheckpoint.watermark.symm.trans watermark)
  have readsCheckpoint := observed.listing.reports.readIntegrityCheckpoint_exact directory selectedCheckpoint
    (by simpa only [valid.selected] using manifestObserved) runReports
  have same : length = count := UInt64.toNat_inj.mp (absolute.trans oldCount.symm)
  subst length
  have through : count.toNat / frameSize = target.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have scannedLayout := observed.listing.offsets_eq scan observed.unique observed.ordered observed.present
  have select : selectWalSegmentReadsThrough scanned target.range.watermark target.range.through =
      some ((observed.sealed ++ [(target.first, bytes)]).map Prod.fst, after.later.visible) := by
    rw [scannedLayout, List.map_append, List.map_cons, List.map_nil, needed]
    rw [List.append_assoc observed.older, needed]
    exact selectWalSegmentReadsThrough_split observed.older required after.later.visible first
      target.range.watermark target.range.through covers covered olderBefore requiredBounds
      (valid.later _ (List.mem_cons_self ..))
  have walRead := observed.listing.readsThrough observed.entries observed.names scan
    (checkpoint.getD (.empty, 0)).1.committed.toNat count (observed.sealed ++ [(target.first, bytes)])
    after.later.visible aligned (by rw [clock, through]; exact covered) (by rwa [clock, through]) (by
      intro file present
      rcases List.mem_append.mp present with sealed | keeperFile
      · exact observed.sealedReads file sealed _ (observed.references file sealed)
      · obtain rfl := List.mem_singleton.mp keeperFile
        exact observed.keeperRead bytes keeper)
  have sameReplay := trace.replayUnchanged old (checkpoint.getD (.empty, 0)).1 observed.sealed
    (fun file present => trace.keepsSealed ▸ observed.references file present)
    visible decoded (recoverMarkedWalSegments_spans replayed) (List.mem_cons.mpr (Or.inl keeper.symm))
  have replay : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count
      (observed.sealed ++ [(target.first, bytes)]) = .ok (selected, table) := sameReplay.1.trans replayed
  have prepared := prepareMarkedWith_reported directory observed.listing.reports.readOptional
    (fun _ => .ok observed.entries) (fun path => .ok (observed.listing.reports.lstat path))
    observed.listing.reports.readBin readsCheckpoint
    (by simpa only [valid.selected, visible] using markerObserved) decoded walRead replay
    (by simp : (observed.sealed ++ [(target.first, bytes)]).getLast? = some (target.first, bytes))
  exact ⟨plan, ⟨valid.selected, valid.keeper, valid.later, rfl, rfl, rfl, keeper⟩,
    by simpa [plan, through] using prepared, replay⟩

end WalSegmentRepair

end Alvoki.Storage
