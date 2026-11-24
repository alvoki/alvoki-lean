import Alvoki.Storage.Disk.VersionedMarkedRecovery
import Alvoki.Storage.Disk.WalSegmentFirstReplay
import Alvoki.Storage.Disk.WalSegmentRetryReads

namespace Alvoki.Storage

open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

private theorem runPresent_of_ordered {read : Nat → Option ByteArray} {indices : List Nat}
    {files : List ByteArray} (ordered : indices.mapM read = some files) (index : Nat) (member : index ∈ indices) :
    ∃ bytes, read index = some bytes := by
  induction indices generalizing files with
  | nil => contradiction
  | cons first rest ih =>
    cases found : read first with
    | none => simp [List.mapM_cons, found] at ordered
    | some bytes =>
      cases remaining : rest.mapM read with
      | none => simp [List.mapM_cons, found, remaining] at ordered
      | some later =>
        rcases List.mem_cons.mp member with rfl | after
        · exact ⟨bytes, found⟩
        · exact ih remaining after

/-- Recover the canonical reference from the selected publication's
durable ordered run map. The native reader subsequently loads the same
map from the reported paths. -/
private theorem selectedCheckpoint_replays {published : CheckpointPublication.Image} {binding : Option ByteArray}
    {history : List WAL.Write} {watermark : Nat}
    (strict : selectedCheckpointWatermark binding = some watermark)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) binding)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ checkpoint table model, SelectedIntegrityCheckpoint published.durable binding checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] := by
  cases binding with
  | none =>
    obtain ⟨table, applied, count⟩ := replay_ordinals_complete .empty history ordered
    have recovered : recoverSelected .empty (WAL.encode history) = .ok table := by
      simpa using (recoverSelected_encoded .empty [] history ordered rfl).trans applied
    obtain ⟨model, abstract, refined⟩ := replay_refines PackedTable.empty_refines applied
    change table.committed.toNat = 0 + history.length at count
    exact ⟨none, table, model, .absent, recovered, by simpa using count,
      replay_rowBounds PackedTable.empty_rowBounds applied, refined,
      List.nil_append history ▸ RepresentsWalHistory.empty.append abstract, by rw [replay_pins applied]; rfl⟩
  | some bytes =>
    obtain ⟨manifest, decoded, _⟩ := selectedCheckpointWatermark_present_iff.mp strict
    have tagged := Manifest.VersionedCheckpoint.decode_integrity decoded
    obtain ⟨files, stored, _, _, _⟩ := published.acceptsVersioned_runs accepted tagged
    let readStored (generation : UInt64) (index : Nat) : Except String ByteArray :=
      match published.durable generation index with
      | none => .error "unavailable durable run"
      | some bytes => .ok bytes
    let reads : VersionedCheckpointFileReads published.durable (some bytes) :=
      { readManifest := .ok (some bytes)
        readRun := readStored
        manifestVisible := fun _ result => (Except.ok.inj result).symm
        runDurable := by
          intro _ header _ _ index _ value expected read known
          change readStored header.generation index = .ok value at read
          unfold readStored at read
          rw [known] at read
          exact (Except.ok.inj read).symm
        integrityRunDurable := by
          intro _ manifest _ _ index _ value expected read known
          change readStored manifest.header.generation index = .ok value at read
          unfold readStored at read
          rw [known] at read
          exact (Except.ok.inj read).symm }
    have runReads : ∀ index, index < manifest.header.runCount.toNat →
        ∃ payload, reads.readRun manifest.header.generation index = .ok payload := by
      intro index within
      obtain ⟨payload, known⟩ := runPresent_of_ordered stored index (List.mem_range.mpr within)
      change published.durable manifest.header.generation index = some payload at known
      exact ⟨payload, by simp [reads, readStored, known]⟩
    obtain ⟨runs, base, table, durable, validated, structural, _, _, recovered, total, bounded, model,
      refinement, represents, fresh⟩ := reads.replays_selected tagged accepted rfl runReads fits ordered
    exact ⟨some (base, manifest.header.generation), table, model,
      .present decoded durable (loadIntegrityRunSet_iff.mpr ⟨validated, structural⟩),
      recovered, total, bounded, refinement, represents, fresh⟩

namespace WalSegmentRepair

/-- Derive a first native marked preparation from the visible directory
and per-file read reports. Only the visible keeper is needed to read and
replay. Its crash alternatives remain a separate durability obligation. -/
theorem RetryInventory.prepareFirstMarked {directory : DiskDirectory} {image : FileImage} {target : Target}
    (observed : RetryInventory directory image target)
    {scanned : List Nat} (scan : observed.listing.offsets = .ok scanned)
    (pair : image.directory.active = target.pair)
    {history : List WAL.Write} {first : Nat} {sealed : List WalSegment} {keeper : WalSegment}
    (chain : WalSegment.Chain history first (sealed ++ [keeper])) (extra : ByteArray)
    (through : target.range.through = history.length)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sealedLayout : observed.sealed = sealed.map fun segment => (segment.first, segment.bytes))
    (keeperStart : keeper.first = target.first) (keeperRead : image.keeper.active = some (keeper.bytes ++ extra))
    (covers : first ≤ target.range.watermark)
    (olderBefore : ∀ start ∈ observed.older, start < first)
    (following : ∀ start ∈ (observed.sealed.map Prod.fst ++ [target.first]).drop 1,
      target.range.watermark < start ∧ start ≤ target.range.through)
    (later : ∀ start ∈ image.later.visible, target.range.through < start)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      target.pair.manifest)
    (manifestRead : observed.listing.reports.readOptional (directory.file .manifest) =
      .ok image.directory.active.manifest)
    (runReads : ∀ bytes manifest, target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
        (observed.listing.reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
          published.durable manifest.header.generation index)
    (markerRead : observed.listing.reports.readOptional (directory.file .walBoundary) =
      .ok image.directory.active.walBoundary) :
    ∃ checkpoint table model count,
      SelectedIntegrityCheckpoint published.durable target.pair.manifest checkpoint ∧
      prepareMarkedWith directory observed.listing.reports.readOptional (fun _ => .ok observed.entries)
        (fun path => .ok (observed.listing.reports.lstat path)) observed.listing.reports.readBin =
        .ok (⟨target.range.through, target.first, image.later.visible, keeper.bytes ++ extra⟩,
          ⟨table, (checkpoint.getD (.empty, 0)).2, count, target.first⟩) ∧
      target.pair.walBoundary = some (WAL.Boundary.encode count) ∧ count.toNat = history.length * frameSize ∧
      keeper.bytes = WAL.encode (history.drop target.first) ∧ table.committed.toNat = history.length ∧
      table.RowBounds ∧ table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨watermark, covered, marker, count, visible, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, table, model, selectedCheckpoint, fullReplay, total, rowBounds, refined, represents, fresh⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  have checkpointClock := Option.some.inj (selectedCheckpoint.watermark.symm.trans watermark)
  have checkpointRead := observed.listing.reports.readIntegrityCheckpoint_exact directory selectedCheckpoint
    (by simpa only [pair] using manifestRead) runReads
  have reads := chain.replaysMarked extra (through ▸ absolute) (checkpointClock ▸ covers) ordered fullReplay
  let bytes := keeper.bytes ++ extra
  let files := observed.sealed ++ [(target.first, bytes)]
  have replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count files =
      .ok (WAL.encode (history.drop first), table) := by
    simpa only [files, bytes, sealedLayout, keeperStart] using reads
  obtain ⟨rest, head⟩ : ∃ rest, files.map Prod.fst = first :: rest := by
    dsimp only [files]
    rw [sealedLayout, ← keeperStart]
    cases sealed with
    | nil => cases chain; exact ⟨[], rfl⟩
    | cons segment later => cases chain; exact ⟨_, rfl⟩
  have scannedLayout := observed.listing.offsets_eq scan observed.unique observed.ordered observed.present
  have counted : count.toNat / frameSize = target.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have offsets : files.map Prod.fst = observed.sealed.map Prod.fst ++ [target.first] := by simp [files]
  rw [← offsets, head, List.drop_one, List.tail_cons] at following
  have selected : selectWalSegmentReadsThrough scanned (checkpoint.getD (.empty, 0)).1.committed.toNat
      (count.toNat / frameSize) = some (files.map Prod.fst, image.later.visible) := by
    rw [checkpointClock, counted, scannedLayout, List.append_assoc observed.older, ← offsets, head]
    exact selectWalSegmentReadsThrough_split observed.older rest image.later.visible first
      target.range.watermark target.range.through covers covered olderBefore following later
  have walRead := observed.listing.readsThrough observed.entries observed.names scan
    (checkpoint.getD (.empty, 0)).1.committed.toNat count files image.later.visible aligned
    (by rw [checkpointClock, counted]; exact covered) selected (by
      intro file member
      rcases List.mem_append.mp member with earlier | keeperFile
      · exact observed.sealedReads file earlier _ (observed.references file earlier)
      · obtain rfl := List.mem_singleton.mp keeperFile
        exact observed.keeperRead bytes keeperRead)
  have prepared := prepareMarkedWith_reported directory observed.listing.reports.readOptional
    (fun _ => .ok observed.entries) (fun path => .ok (observed.listing.reports.lstat path))
    observed.listing.reports.readBin checkpointRead
    (by simpa only [pair, visible] using markerRead) decoded walRead replayed
    (by simp [files] : files.getLast? = some (target.first, bytes))
  exact ⟨checkpoint, table, model, count, selectedCheckpoint, by simpa [counted, bytes] using prepared,
    visible.trans (congrArg some (WAL.Boundary.decode_reencode decoded).symm), through ▸ absolute,
    keeperStart ▸ chain.keeperBytes, total, rowBounds, refined, represents, fresh⟩

end WalSegmentRepair

end Alvoki.Storage
