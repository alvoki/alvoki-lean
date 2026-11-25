import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair SyncHandleRouting

/-- The metadata callback projects the exact cursor-bearing schedule. Its
lookup uses no-follow metadata and its reads use the returned description. -/
def runCachedMetadataRead (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (path : FilePath) : EStateM IO.Error Nat (Option ByteArray) :=
  readOptionalCachedOpenFileWith directory path (pure ((reads.stat path).map Prod.fst))
    (fun path cursor => match reads.openRead path with
      | .error cause => .error cause cursor
      | .ok (_, slot, offset) => .ok slot offset)
    (fun slot => reads.readChunk slot.description)

def cachedMetadataReadResult (result : EStateM.Result IO.Error Nat (Option ByteArray)) :
    Except IO.Error (Option ByteArray) :=
  match result with
  | .ok bytes _ => .ok bytes
  | .error cause _ => .error cause

private theorem manifestPath_ne_boundary (directory : DiskDirectory) :
    directory.file .manifest ≠ directory.file .walBoundary := by
  intro same
  have names := congrArg FilePath.toString same
  change (directory.path.toString ++ "/") ++ "MANIFEST" =
    (directory.path.toString ++ "/") ++ "WAL.commit" at names
  exact (by decide : "MANIFEST" ≠ "WAL.commit") ((String.append_right_inj _).mp names)

theorem runCachedMetadataRead_missing (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (path : FilePath) (name message : String)
    (stat : reads.stat path = .error (.noFileOrDirectory name 2 message)) :
    runCachedMetadataRead reads directory path 0 = .ok none 0 := by
  simp [runCachedMetadataRead, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    stat, Except.map, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

/-- The immutable live object supplying one metadata file. The two path
resolutions enter separately, just as the native stat and open do. -/
structure HeldMetadataFile (reads : CheckpointRunChunkReads) (path : FilePath) (basename : String)
    (view : DirectoryReadNamespace) (root : DeviceInode) (payload : ByteArray) where
  object : DeviceInode
  bound : view.child root basename = some object
  contents : reads.objectBytes (view.modelObject object) = some payload
  calls : RunChunkPathReport reads path basename root view

def HeldMetadataFile.observesFile {reads path basename view root payload}
    (file : HeldMetadataFile reads path basename view root payload) : reads.ObservesFile path payload :=
  file.calls.observesFile file.bound file.contents

/-- The healthy reached MANIFEST read returns the exact bounded prefix of
the stable opened file, including the oversized-file witness when present. -/
theorem HeldMetadataFile.manifestPrefix {reads directory view root payload}
    (file : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" view root payload)
    (fits : IntegrityCheckpoint.acquisitionSize payload < USize.size) :
    runCachedMetadataRead reads directory (directory.file .manifest) 0 =
      .ok (some (payload.extract 0 (IntegrityCheckpoint.acquisitionSize payload)))
        (IntegrityCheckpoint.acquisitionSize payload) := by
  let seen := file.observesFile
  have objectBytes : reads.objectBytes (seen.inventory.inode seen.slot.description) = some payload := by
    rw [seen.sameObject, seen.contents]
  have exactRead := readIntegrityManifestPrefixWith_completes seen.extent
    (seen.observes payload objectBytes) (seen.healthy payload objectBytes) fits
  simp [runCachedMetadataRead, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    seen.stat, seen.opened, seen.regular, manifestPath_ne_boundary, exactRead, Except.map,
    show (IO.FS.FileType.file == .file) = true from rfl,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

/-- The marker reads at most the 24-byte marker and one extra byte. The
same opened description supplies the EOF observation on a short file. -/
theorem HeldMetadataFile.markerPrefix {reads directory view root payload}
    (file : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload)
    (available : PrefixChunksAvailableUntilEof payload (reads.readChunk file.observesFile.slot.description)) :
    runCachedMetadataRead reads directory (directory.file .walBoundary) 0 =
      .ok (some (payload.extract 0 (min WAL.Boundary.acquisitionLimit payload.size)))
        (min WAL.Boundary.acquisitionLimit payload.size) := by
  let seen := file.observesFile
  have objectBytes : reads.objectBytes (seen.inventory.inode seen.slot.description) = some payload := by
    rw [seen.sameObject, seen.contents]
  have fits : WAL.Boundary.acquisitionLimit < USize.size :=
    Nat.lt_of_lt_of_le (by decide) USize.le_size
  have exactRead := readPrefixUntilEofWith_completes (IO.userError "invalid WAL boundary length")
    (seen.observes payload objectBytes) available WAL.Boundary.acquisitionLimit fits
    (bytes := ByteArray.empty) (Nat.zero_le _)
  simp only [Nat.zero_add, ByteArray.empty_append] at exactRead
  simp [runCachedMetadataRead, readOptionalCachedOpenFileWith, readOptionalDatabaseFileWithMetadata,
    seen.stat, seen.opened, seen.regular, exactRead, Except.map,
    show (IO.FS.FileType.file == .file) = true from rfl, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

/-- Identify the optional metadata callbacks with the reached native reader.
The selected pair's payloads come from the stable objects at the captured
root. These premises do not require an installation or its read equations. -/
structure DirectoryMetadataReadReports (directory : DiskDirectory) (view : DirectoryReadNamespace)
    (root : DeviceInode) (reads : CheckpointRunChunkReads)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (pair : DirectoryPublication.Bindings) where
  projected : ∀ path, path = directory.file .manifest ∨ path = directory.file .walBoundary →
    readOptional path = cachedMetadataReadResult (runCachedMetadataRead reads directory path 0)
  manifestMissing : pair.manifest = none →
    view.child root "MANIFEST" = none ∧
    ∃ name message, reads.stat (directory.file .manifest) = .error (.noFileOrDirectory name 2 message)
  manifestFile : ∀ payload, pair.manifest = some payload →
    Nonempty (HeldMetadataFile reads (directory.file .manifest) "MANIFEST" view root payload) ∧
    IntegrityCheckpoint.acquisitionSize payload < USize.size
  markerFile : ∀ payload, pair.walBoundary = some payload →
    ∃ file : HeldMetadataFile reads (directory.file .walBoundary) "WAL.commit" view root payload,
      PrefixChunksAvailableUntilEof payload (reads.readChunk file.observesFile.slot.description)

namespace DirectoryMetadataReadReports

variable {directory : DiskDirectory} {view : DirectoryReadNamespace} {root : DeviceInode}
  {reads : CheckpointRunChunkReads} {readOptional : FilePath → Except IO.Error (Option ByteArray)}
  {pair : DirectoryPublication.Bindings}

/-- The valid marked layout supplies decoder acceptance. A missing manifest
comes only from the reported no-follow ENOENT at its canonical child. -/
theorem manifestRead (report : DirectoryMetadataReadReports directory view root reads readOptional pair)
    {range : MarkedWalRange} (accepted : pair.walRange = some range) :
    readOptional (directory.file .manifest) = .ok pair.manifest := by
  rw [report.projected _ (.inl rfl)]
  cases selected : pair.manifest with
  | none =>
    obtain ⟨_, name, message, missing⟩ := report.manifestMissing selected
    rw [runCachedMetadataRead_missing _ _ _ name message missing]
    rfl
  | some payload =>
    obtain ⟨⟨file⟩, fits⟩ := report.manifestFile payload selected
    have watermark := (DirectoryPublication.Bindings.walRange_accounting accepted).1
    rw [selected] at watermark
    obtain ⟨_, decoded, _⟩ := selectedCheckpointWatermark_present_iff.mp watermark
    rw [file.manifestPrefix fits, IntegrityCheckpoint.acquisitionPrefix_eq_of_decode decoded]
    rfl

/-- The selected layout's marker was accepted, so the bounded EOF reader
returns that whole marker from the held directory's canonical child. -/
theorem markerRead (report : DirectoryMetadataReadReports directory view root reads readOptional pair)
    {range : MarkedWalRange} (accepted : pair.walRange = some range) :
    readOptional (directory.file .walBoundary) = .ok pair.walBoundary := by
  obtain ⟨_, _, payload, count, selected, decoded, _⟩ := DirectoryPublication.Bindings.walRange_accounting accepted
  obtain ⟨file, available⟩ := report.markerFile payload selected
  have size : payload.size = 24 := by
    rw [← WAL.Boundary.decode_reencode decoded, WAL.Boundary.encode_size]
  rw [report.projected _ (.inr rfl), file.markerPrefix available, selected]
  have covered : payload.size ≤ WAL.Boundary.acquisitionLimit := by
    rw [size]
    decide
  simp [cachedMetadataReadResult, Nat.min_eq_right covered]

theorem manifestListed (report : DirectoryMetadataReadReports directory view root reads readOptional pair) :
    "MANIFEST" ∈ view.names root ↔ pair.manifest.isSome = true := by
  rw [view.namesExact]
  cases selected : pair.manifest with
  | none => simp [(report.manifestMissing selected).1]
  | some payload =>
    obtain ⟨⟨file⟩, _⟩ := report.manifestFile payload selected
    simp [file.bound]

theorem markerListed (report : DirectoryMetadataReadReports directory view root reads readOptional pair)
    {range : MarkedWalRange} (accepted : pair.walRange = some range) :
    "WAL.commit" ∈ view.names root := by
  obtain ⟨_, _, payload, _, selected, _, _⟩ := DirectoryPublication.Bindings.walRange_accounting accepted
  obtain ⟨file, _⟩ := report.markerFile payload selected
  exact (view.namesExact _ _).mpr ⟨file.object, file.bound⟩

end DirectoryMetadataReadReports

/-- Compose the exact metadata callbacks with the checked listing of the
same held directory used by the selected checkpoint runs. -/
theorem HeldDirectoryMarkedRetryReports.metadataReads {directory : DiskDirectory}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history}
    {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
    {published : CheckpointPublication.Image} (held : HeldDirectoryMarkedRetryReports operations published)
    (report : DirectoryMetadataReadReports directory held.lifetime.namespaceView held.lifetime.root
      operations.reads operations.reported.inventory.reports.readOptional before.image.directory.active) :
    operations.reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok before.image.directory.active.manifest ∧
    operations.reported.inventory.reports.readOptional (directory.file .walBoundary) =
      .ok before.image.directory.active.walBoundary ∧
    ("MANIFEST" ∈ operations.reported.inventory.names ↔ before.image.directory.active.manifest.isSome = true) ∧
    "WAL.commit" ∈ operations.reported.inventory.names :=
  ⟨report.manifestRead layout.decoded, report.markerRead layout.decoded,
    held.checkedListing.2.mem_iff.trans report.manifestListed,
    held.checkedListing.2.mem_iff.mpr (report.markerListed layout.decoded)⟩

/-- The first WAL.commit stat chooses the route before the bounded reads.
The primitive report includes the object observed at that earlier call.
Its canonical child is resolved in the same held directory as the later reads. -/
structure HeldMarkedMetadata {directory : DiskDirectory} {before : LockedFileState FileImage}
    {history : List WAL.Write} {layout : CanonicalKeeperLayout before.image history}
    {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
    {published : CheckpointPublication.Image} (held : HeldDirectoryMarkedRetryReports operations published) where
  reads : DirectoryMetadataReadReports directory held.lifetime.namespaceView held.lifetime.root
    operations.reads operations.reported.inventory.reports.readOptional before.image.directory.active
  route : RunChildLookup held.lifetime.root "WAL.commit" held.lifetime.namespaceView
  routeStat : Except IO.Error (IO.FS.Metadata × Nat)
  routeIdentified : ∃ result, routeStat = .ok (result, held.lifetime.namespaceView.modelObject route.child)
  routeProjected : operations.lookup (directory.file .walBoundary) before.image =
    .ok (routeStat.map Prod.fst) before.image

namespace HeldMarkedMetadata

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {held : HeldDirectoryMarkedRetryReports operations published}

/-- The separate route stat and payload open resolve to the same canonical
child. The earlier metadata itself need only establish that the marker exists. -/
theorem routeMatchesOpenedMarker (observed : HeldMarkedMetadata held) {payload : ByteArray}
    (file : HeldMetadataFile operations.reads (directory.file .walBoundary) "WAL.commit"
      held.lifetime.namespaceView held.lifetime.root payload) :
    ∃ result, observed.routeStat = .ok (result, file.observesFile.inventory.inode file.observesFile.slot.description) := by
  obtain ⟨result, identified⟩ := observed.routeIdentified
  have same : observed.route.child = file.calls.openLookup.child :=
    (observed.route.child_eq file.bound).trans (file.calls.openLookup.child_eq file.bound).symm
  refine ⟨result, ?_⟩
  change observed.routeStat = .ok (result, file.calls.inventory.inode file.calls.slot.description)
  simpa only [same, file.calls.identifiedOpen] using identified

/-- The operation packet receives the actual branch and payload equations
from the shared held-directory observations. -/
theorem callbackMetadata (observed : HeldMarkedMetadata held) : operations.MarkedMetadata := by
  obtain ⟨_, _, payload, _, selected, _, _⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  obtain ⟨file, _⟩ := observed.reads.markerFile payload selected
  obtain ⟨result, route⟩ := observed.routeMatchesOpenedMarker file
  obtain ⟨manifest, marker, _, _⟩ := held.metadataReads observed.reads
  refine ⟨⟨result, ?_⟩, manifest, marker⟩
  rw [observed.routeProjected, route]
  rfl

end HeldMarkedMetadata

end Alvoki.Storage.DiskSession
