import Alvoki.Storage.Disk.CheckpointRunChunkReports
import Alvoki.Storage.Disk.KeeperReadCustody
import Alvoki.Storage.Disk.WalSegmentCachedRetryReads

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting

/-- Interpret the adapter's keeper callback using the same prefix loop as
for checkpoint runs and seals. A captured cache entry retains the exact
open observation, including the descriptor used to read the prefix. -/
def readWalKeeperWithChunks {state : Type} (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize : Nat) :
    EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × state) ByteArray :=
  readKeeperWith
    (fun name (cache, before) => withCache cache
      ((liftExcept (reads.openRead name) : EStateM IO.Error state _) before))
    (fun opened size (cache, before) => withCache cache
      ((liftExcept (reads.readOpenedPrefix (IO.userError "short or oversized WAL keeper read") opened size) :
        EStateM IO.Error state _) before))
    (fun name opened (cache, before) => .ok () (cache.remember name opened, before))
    path count fileSize

/-- Only an aligned keeper enters the fsync cache. A longer keeper returns
the selected prefix and leaves its cached handle state unchanged. -/
theorem readWalKeeperWithChunks_exact
    {state : Type} {reads : CheckpointRunChunkReads} {path : FilePath} {selectedBytes tail : ByteArray}
    (seen : reads.ObservesFile path (selectedBytes ++ tail)) (fits : selectedBytes.size < USize.size)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat)) (initial : state) :
    readWalKeeperWithChunks reads path selectedBytes.size seen.metadata.byteSize.toNat (cache, initial) =
      .ok selectedBytes (cache.captureKeeper path (seen.inventory, seen.slot, 0)
        selectedBytes.size seen.metadata.byteSize.toNat, initial) := by
  have covered : selectedBytes.size ≤ (selectedBytes ++ tail).size := by simp
  have openedPrefix := seen.readOpenedExactPrefix (IO.userError "short or oversized WAL keeper read") _ fits covered
  rw [ByteArray.extract_append_eq_left rfl] at openedPrefix
  unfold readWalKeeperWithChunks
  refine readKeeperWith_success cache path selectedBytes.size seen.metadata.byteSize.toNat _ _
    (openedState := initial) ⟨seen.extent ▸ covered, fits⟩ ?_ ?_
  · simp [seen.opened, liftExcept, Pure.pure, EStateM.pure, withCache]
  · simp [openedPrefix, liftExcept, Pure.pure, EStateM.pure, withCache]

/-- Project the payload result for the read-only file image. Keeper handle
custody is available separately through `readWalKeeperWithChunks_exact`. -/
private def readWalKeeperBytes (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize : Nat) : Except IO.Error ByteArray :=
  match readWalKeeperWithChunks reads path count fileSize (⟨none, none, []⟩, ()) with
  | .ok payload _ => .ok payload
  | .error cause _ => .error cause

private theorem readWalKeeperWithChunks_project {state : Type} (reads : CheckpointRunChunkReads)
    (path : FilePath) (count fileSize : Nat) (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (initial : state) :
    (match readWalKeeperWithChunks reads path count fileSize (cache, initial) with
    | .ok payload _ => .ok payload
    | .error cause _ => .error cause) = readWalKeeperBytes reads path count fileSize := by
  by_cases admitted : count ≤ fileSize ∧ count < USize.size
  · cases opened : reads.openRead path with
    | error cause =>
      simp [readWalKeeperWithChunks, readWalKeeperBytes, readKeeperWith, admitted, opened,
        liftExcept, withCache, Bind.bind, EStateM.bind, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
    | ok handle =>
      cases read : reads.readOpenedPrefix (IO.userError "short or oversized WAL keeper read") handle count <;>
        cases aligned : count == fileSize <;>
        simp [readWalKeeperWithChunks, readWalKeeperBytes, readKeeperWith, admitted, opened, read, aligned,
          liftExcept, withCache, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  · simp [readWalKeeperWithChunks, readWalKeeperBytes, readKeeperWith, admitted, Bind.bind, EStateM.bind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Derive the selected payload callbacks from per-open reports on the held
WAL names. Stat and open must name the same stable file object. Liveness,
cursor and chunk behavior remain explicit primitive observations. Later names
contribute only metadata and need no open or payload observation. -/
def CachedRetryReadReports.ofChunkReads {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} (observed : CachedRetryReadInventory directory layout)
    (reads : CheckpointRunChunkReads)
    (metadata : ∀ path, observed.inventory.reports.lstat path = (reads.stat path).map Prod.fst)
    (seals : ∀ segment ∈ layout.sealed, image.kept segment.first = some segment.bytes ∧
      segment.bytes.size < USize.size ∧
      Nonempty (reads.ObservesFile (directory.file (.walSegment segment.first)) segment.bytes))
    (keeper : Nonempty (reads.ObservesFile (directory.file (.walSegment layout.keeper.first))
      (layout.keeper.bytes ++ layout.tail)))
    (keeperFits : layout.keeper.bytes.size < USize.size) : CachedRetryReadReports directory layout where
  toCachedRetryReadInventory := observed
  readSeal := reads.readFilePrefix selectedWalSpanError
  readKeeper := readWalKeeperBytes reads
  seals := by
    intro segment member actual stat
    obtain ⟨stored, fits, ⟨seen⟩⟩ := seals segment member
    rw [metadata, seen.stat] at stat
    have same : seen.metadata = actual := Except.ok.inj stat
    refine ⟨stored, same ▸ seen.extent, fits, ?_⟩
    simp [CheckpointRunChunkReads.readFilePrefix, Bind.bind, Except.bind, seen.opened,
      seen.readOpenedExactPrefix _ _ fits (Nat.le_refl _)]
  keeper := by
    intro actual stat
    obtain ⟨seen⟩ := keeper
    rw [metadata, seen.stat] at stat
    have same : seen.metadata = actual := Except.ok.inj stat
    subst actual
    exact ⟨seen.extent, by simp [readWalKeeperBytes, readWalKeeperWithChunks_exact seen keeperFits]⟩

/-- The keeper callback used to select WAL bytes is the projection of
the stateful read from any entered cache. In particular, the same read
that yields the reported bytes can supply the pending handle for fsync. -/
theorem CachedRetryReadReports.ofChunkReads_readKeeper
    {state : Type} {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history} (observed : CachedRetryReadInventory directory layout)
    (reads : CheckpointRunChunkReads)
    (metadata : ∀ path, observed.inventory.reports.lstat path = (reads.stat path).map Prod.fst)
    (seals : ∀ segment ∈ layout.sealed, image.kept segment.first = some segment.bytes ∧
      segment.bytes.size < USize.size ∧
      Nonempty (reads.ObservesFile (directory.file (.walSegment segment.first)) segment.bytes))
    (keeper : Nonempty (reads.ObservesFile (directory.file (.walSegment layout.keeper.first))
      (layout.keeper.bytes ++ layout.tail)))
    (keeperFits : layout.keeper.bytes.size < USize.size)
    (path : FilePath) (count fileSize : Nat) (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (initial : state) :
    (match readWalKeeperWithChunks reads path count fileSize (cache, initial) with
    | .ok payload _ => .ok payload
    | .error cause _ => .error cause) =
      (CachedRetryReadReports.ofChunkReads observed reads metadata seals keeper keeperFits).readKeeper
        path count fileSize :=
  readWalKeeperWithChunks_project reads path count fileSize cache initial

end Alvoki.Storage.WalSegmentRepair
