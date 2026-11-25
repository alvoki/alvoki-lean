import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- One WAL child of the captured directory. Stat and open resolve this
child separately. The observed inode supplies the bytes of the file, and the
extent guard requires a regular file with a single link. -/
structure HeldWalPayloadFile (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (view : DirectoryReadNamespace) (root : DeviceInode) (first : Nat) (payload : ByteArray) where
  object : DeviceInode
  bound : view.child root (renderWalSegmentName first) = some object
  contents : reads.objectBytes (view.modelObject object) = some payload
  calls : RunChunkPathReport reads (directory.file (.walSegment first)) (renderWalSegmentName first) root view
  oneLink : calls.metadata.numLinks = 1

def HeldWalPayloadFile.observesFile {reads directory view root first payload}
    (file : HeldWalPayloadFile reads directory view root first payload) :
    reads.ObservesFile (directory.file (.walSegment first)) payload :=
  file.calls.observesFile file.bound file.contents

theorem HeldWalPayloadFile.inspected {reads directory view root first payload}
    (file : HeldWalPayloadFile reads directory view root first payload) :
    inspectWalSegmentWith (m := Except IO.Error) (directory.file (.walSegment first))
      (.ok ((reads.stat (directory.file (.walSegment first))).map Prod.fst)) =
      .ok (.ok file.calls.metadata) := by
  simp [inspectWalSegmentWith, checkPrivateRegularWith, file.calls.stat, file.calls.regular,
    file.oneLink, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- The extent probe uses the same canonical child as the opened read.
The native callback's guard accepts the exact no-follow metadata. -/
theorem HeldWalPayloadFile.discovered {reads directory view root first payload}
    (file : HeldWalPayloadFile reads directory view root first payload) :
    readWalSegmentExtentWith (m := Except IO.Error) directory
      (fun path => inspectWalSegmentWith path (.ok ((reads.stat path).map Prod.fst)))
      (renderWalSegmentName first) = .ok (some (first, file.calls.metadata)) := by
  simp [readWalSegmentExtentWith, parseWalSegmentName_render, file.inspected, classifyWalSegmentLookup,
    file.calls.regular, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- Only the selected seal paths and keeper need opened-file observations.
For seals their full payload appears in the retained image. The keeper may
have a tail beyond the marker, which contributes only to its physical extent. -/
structure HeldWalPayloadReports (directory : DiskDirectory) {image : FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout image history) (reads : CheckpointRunChunkReads)
    (view : DirectoryReadNamespace) (root : DeviceInode) where
  sealedFile : ∀ segment ∈ layout.sealed,
    HeldWalPayloadFile reads directory view root segment.first segment.bytes
  kept : ∀ segment ∈ layout.sealed, image.kept segment.first = some segment.bytes
  sealFits : ∀ segment ∈ layout.sealed, segment.bytes.size < USize.size
  keeper : HeldWalPayloadFile reads directory view root layout.keeper.first (layout.keeper.bytes ++ layout.tail)
  keeperFits : layout.keeper.bytes.size < USize.size

namespace HeldWalPayloadReports

variable {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout image history} {reads : CheckpointRunChunkReads}
  {view : DirectoryReadNamespace} {root : DeviceInode}

def toCachedReads (report : HeldWalPayloadReports directory layout reads view root)
    (inventory : CachedRetryReadInventory directory layout)
    (metadata : ∀ path, inventory.inventory.reports.lstat path = (reads.stat path).map Prod.fst) :
    CachedRetryReadReports directory layout :=
  CachedRetryReadReports.ofChunkReads inventory reads metadata
    (fun segment present => ⟨report.kept segment present, report.sealFits segment present,
      ⟨(report.sealedFile segment present).observesFile⟩⟩)
    ⟨report.keeper.observesFile⟩ report.keeperFits

/-- The keeper callback returns the selected prefix. If the observed
physical extent equals that prefix, the pending sync uses this same
description. A longer keeper leaves the cache unchanged. -/
theorem keeperCache (report : HeldWalPayloadReports directory layout reads view root)
    {state : Type} (cache : Cache (DescriptorInventory × DescriptorSlot × Nat)) (initial : state) :
    let path := directory.file (.walSegment layout.keeper.first)
    let file := report.keeper.observesFile
    readWalKeeperWithChunks reads path layout.keeper.bytes.size file.metadata.byteSize.toNat (cache, initial) =
      .ok layout.keeper.bytes
        (cache.captureKeeper path (file.inventory, file.slot, 0) layout.keeper.bytes.size file.metadata.byteSize.toNat,
          initial) :=
  readWalKeeperWithChunks_exact report.keeper.observesFile report.keeperFits cache initial

end HeldWalPayloadReports

namespace HeldDirectoryMarkedRetryReports

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}

/-- The stat/open identity and the checked discovery of each selected WAL
file refer to the same child of the captured root. Both sides use the
canonical name of the segment's absolute first ordinal. -/
theorem selectedWalListed (held : HeldDirectoryMarkedRetryReports operations published)
    (wal : HeldWalPayloadReports directory layout operations.reads held.lifetime.namespaceView held.lifetime.root) :
    (∀ segment ∈ layout.sealed, renderWalSegmentName segment.first ∈ operations.reported.inventory.names) ∧
      renderWalSegmentName layout.keeper.first ∈ operations.reported.inventory.names := by
  constructor
  · intro segment present
    exact held.checkedListing.2.mem_iff.mpr
      ((held.lifetime.namespaceView.namesExact _ _).mpr ⟨_, (wal.sealedFile segment present).bound⟩)
  · exact held.checkedListing.2.mem_iff.mpr
      ((held.lifetime.namespaceView.namesExact _ _).mpr ⟨_, wal.keeper.bound⟩)

/-- In the cached marked worker, the actual payload callbacks must
project the per-description bounded readers. Under that observation,
the shared read-only schedule returns exactly the selected WAL bytes
and physical keeper extent. Later names are passed on to repair without
opening their payloads. -/
theorem selectedWalPayloads (held : HeldDirectoryMarkedRetryReports operations published)
    (wal : HeldWalPayloadReports directory layout operations.reads held.lifetime.namespaceView held.lifetime.root)
    (readSeal : operations.reported.readSeal = operations.reads.readFilePrefix selectedWalSpanError)
    (readKeeper : operations.readKeeper operations.cache = readWalKeeperBytes operations.reads)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (later : ∀ start ∈ before.image.later.visible, layout.range.through < start)
    {count : UInt64} (absolute : count.toNat = layout.range.through * WAL.frameSize)
    {state : Type} (initial : state) :
    let files := layout.sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(layout.keeper.first, layout.keeper.bytes)]
    readSelectedWithCachedExtents (m := EStateM IO.Error state) directory layout.range.watermark count
      (fun path => liftExcept (operations.reported.list path))
      (fun path => liftExcept
        (.ok (operations.reported.inventory.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (operations.reported.readSeal path size))
      (fun path size physical => liftExcept (operations.readKeeper operations.cache path size physical)) initial =
      .ok (⟨files, before.image.later.visible⟩, (layout.keeper.bytes ++ layout.tail).size) initial := by
  rw [readSeal, readKeeper]
  exact (wal.toCachedReads operations.reported.toCachedRetryReadInventory operations.metadata).readSelected
    following later absolute initial

end HeldDirectoryMarkedRetryReports
end Alvoki.Storage.DiskSession
