import Alvoki.Storage.Disk.WalSegmentBoundedOpenEffects
import Alvoki.Storage.Disk.CachedWalOpenFailure
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects
import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.WalSegmentReplayStability
import Alvoki.Storage.Disk.SegmentedSessionInstall
import Alvoki.Storage.Disk.ReadRecoveryPrefix

namespace Alvoki.WAL.TwoSlot

open Alvoki.Storage.DirectoryPublication

/-- An exact bounded read from the held marker's rewound descriptor supplies
the same decode as its complete bytes, including oversized rejection. -/
theorem decode_heldRead {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    (mismatch : IO.Error) (observes : Storage.PrefixChunkObserves source read)
    (available : Storage.PrefixChunksAvailableUntilEof source read)
    (fits : acquisitionLimit < USize.size) :
    ∃ bytes, Storage.readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes (min acquisitionLimit source.size) ∧ decode bytes = decode source := by
  refine ⟨source.extract 0 (min acquisitionLimit source.size), ?_, decode_acquisitionPrefix source⟩
  simpa using Storage.readPrefixUntilEofWith_completes mismatch observes available
    acquisitionLimit fits (offset := 0) (bytes := ByteArray.empty) (Nat.zero_le source.size)

theorem decode_of_heldRead
    {source bytes : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray} {reached : Nat}
    (mismatch : IO.Error) (observes : Storage.PrefixChunkObserves source read)
    (available : Storage.PrefixChunksAvailableUntilEof source read)
    (fits : acquisitionLimit < USize.size)
    (returned : Storage.readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes reached) : decode bytes = decode source := by
  obtain ⟨bounded, result, agrees⟩ := decode_heldRead mismatch observes available fits
  rw [returned] at result
  have same : bytes = bounded := by injection result
  exact same.symm ▸ agrees

/-- Express a successfully decoded physical marker in the logical format
consumed by the shared checkpoint and segmented WAL recovery. -/
def projectBinding (visible : Bindings) (bytes : ByteArray) : Except String Bindings :=
  (decode bytes).map fun selected =>
    visible.replace .walBoundary (Boundary.encode selected.frontier)

theorem projectBinding_decodes {visible : Bindings} {bytes : ByteArray} {selected : Selection}
    (accepted : decode bytes = .ok selected) :
    projectBinding visible bytes = .ok
      ⟨visible.manifest, some (Boundary.encode selected.frontier)⟩ := by
  simp [projectBinding, accepted, Except.map, Bindings.replace]

/-- The observed bounded read used by reopen projects the full physical
marker to the same binding used by the shared WAL and checkpoint readers. -/
theorem projectBinding_of_heldRead
    {source bytes : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    {reached : Nat} {visible : Bindings} {selected : Selection}
    (mismatch : IO.Error) (observes : Storage.PrefixChunkObserves source read)
    (available : Storage.PrefixChunksAvailableUntilEof source read)
    (fits : acquisitionLimit < USize.size)
    (returned : Storage.readPrefixUntilEofWith mismatch read acquisitionLimit ByteArray.empty 0 =
      .ok bytes reached)
    (accepted : decode bytes = .ok selected) :
    projectBinding visible source = .ok
      ⟨visible.manifest, some (Boundary.encode selected.frontier)⟩ := by
  exact projectBinding_decodes ((decode_of_heldRead mismatch observes available fits returned).symm.trans accepted)

/-- Bootstrap exposes the same zero frontier and checkpoint binding as
the ordinary empty-WAL installer under the marker projection. -/
theorem projectBinding_initial (visible : Bindings) :
    projectBinding visible initial = .ok ⟨visible.manifest, some (Boundary.encode 0)⟩ :=
  by
    have projected := projectBinding_decodes (visible := visible)
      (bytes := initial) (selected := initialSelection) decode_initial
    simpa only [initialSelection] using projected

/-- A physically observed marker that decodes after an interrupted write
projects to one of the original batch frontiers. After successful sync its
projection is the new frontier. WAL validation is checked separately. -/
theorem decodedMarker_of_survivor {before after : ByteArray}
    {active : OrderedTwoSlot.Slot} {old next : OrderedTwoSlot.Record UInt64}
    {phase : OrderedTwoSlot.Phase} {selected : Selection}
    (report : OrderedTwoSlot.Survivor (decodedSlots before) active next phase (decodedSlots after))
    (present : decodedSlots before active = some old)
    (older : ∀ stale, decodedSlots before active.other = some stale → stale.epoch < old.epoch)
    (newer : old.epoch < next.epoch)
    (accepted : decode after = .ok selected) :
    match phase with
    | .beforeWalSync | .beforeSlotWrite => selected.frontier = old.frontier
    | .slotWriteUncertain => selected.frontier = old.frontier ∨ selected.frontier = next.frontier
    | .slotSynced => selected.frontier = next.frontier := by
  have logical := report.recovery (fun _ => true) present older newer rfl (fun _ => rfl)
  have newest := decode_agrees_with_protocol accepted
  change OrderedTwoSlot.selectNewest ((decodedSlots after) .first) ((decodedSlots after) .second) =
    .ok selected.toRecord at newest
  have same : OrderedTwoSlot.recover (fun _ => true) (decodedSlots after) = .ok selected.toRecord := by
    simp [OrderedTwoSlot.recover, newest, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [same] at logical
  have frontier {r : OrderedTwoSlot.Record UInt64}
      (h : Except.ok (ε := OrderedTwoSlot.SelectionError) selected.toRecord = .ok r) :
      selected.frontier = r.frontier := congrArg OrderedTwoSlot.Record.frontier (Except.ok.inj h)
  cases phase with
  | beforeWalSync | beforeSlotWrite | slotSynced => exact frontier logical
  | slotWriteUncertain =>
    exact logical.elim (fun sameOld => .inl (frontier sameOld)) (fun sameNew => .inr (frontier sameNew))

/-- The projected directory binding of an accepted uncertain marker
satisfies the old-or-whole premise of the retry model. -/
theorem projectBinding_oldOrNew {directory : Bindings} {before after : ByteArray}
    {active : OrderedTwoSlot.Slot} {current : Selection} {next : OrderedTwoSlot.Record UInt64}
    {projected : Bindings}
    (report : OrderedTwoSlot.Survivor (decodedSlots before) active next .slotWriteUncertain (decodedSlots after))
    (currentDecode : decode before = .ok current)
    (activeOffset : current.slot = slotIndex active)
    (newer : current.toRecord.epoch < next.epoch)
    (projection : projectBinding directory after = .ok projected) :
    projected.manifest = directory.manifest ∧
      (projected.walBoundary = some (Boundary.encode current.frontier) ∨
        projected.walBoundary = some (Boundary.encode next.frontier)) := by
  cases accepted : decode after with
  | error => simp [projectBinding, accepted, Except.map] at projection
  | ok selected =>
    have binding := projectBinding_decodes (visible := directory) accepted
    have equal := Except.ok.inj (binding.symm.trans projection)
    cases equal
    obtain ⟨present, older⟩ := decodedSlots_active currentDecode active activeOffset
    have selectedFrontier := decodedMarker_of_survivor report present older newer accepted
    exact ⟨rfl, selectedFrontier.imp
      (congrArg (fun value => some (Boundary.encode value)))
      (congrArg (fun value => some (Boundary.encode value)))⟩

/-- Model a successful file barrier where every present marker binding
names the held file. Absent bindings can survive a pending bootstrap
rename. The barrier changes neither that choice nor the manifest binding. -/
def settleMarker (image : Image) (selected : Selection) : Image :=
  let publish := fun bindings : Bindings =>
    { bindings with walBoundary := bindings.walBoundary.map fun _ => Boundary.encode selected.frontier }
  { image with active := publish image.active, crashImages := image.crashImages.map publish }

theorem settleMarker_survivor_iff (image : Image) (selected : Selection) (survivor : Bindings) :
    survivor ∈ (settleMarker image selected).crashImages ↔
      ∃ before ∈ image.crashImages, survivor.manifest = before.manifest ∧
        survivor.walBoundary = before.walBoundary.map fun _ => Boundary.encode selected.frontier := by
  simp only [settleMarker, List.mem_map]
  constructor
  · rintro ⟨before, present, rfl⟩
    exact ⟨before, present, rfl, rfl⟩
  · rintro ⟨before, present, manifest, wal⟩
    refine ⟨before, present, ?_⟩
    cases survivor
    simp_all

/-- The shared directory barrier settles the visible manifest and marker
bindings once preparation has observed a present marker. -/
theorem settleMarker_syncDirectory (image : Image) (selected : Selection)
    {bytes : ByteArray} (bound : image.active.walBoundary = some bytes)
    {survivor : Bindings} (present : survivor ∈ (settleMarker image selected).syncDirectory.crashImages) :
    survivor.manifest = image.active.manifest ∧
      survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have chosen := (Image.survives_syncDirectory_iff (settleMarker image selected) survivor).mp present
  rw [chosen]
  simp [settleMarker, bound]

open Alvoki.Storage.WalSegmentRepair

/-- Once the positional marker is settled, each reached shared destructive
repair prefix preserves that exact logical marker, including admitted cuts
while replacing or pruning a keeper. -/
theorem repair_preserves_settledMarker (initial : FileImage) (selected : Selection)
    {target : Target} {after : FileImage} {bytes : ByteArray}
    (bound : initial.directory.active.walBoundary = some bytes)
    (trace : EffectTrace target
      { initial with directory := settleMarker initial.directory selected } after)
    (pair : (settleMarker initial.directory selected).active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts)
    (later : initial.later.Beyond target.range.through)
    {survivor : Bindings} (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.walBoundary = some (Boundary.encode selected.frontier) := by
  have accepted := trace.valid pair keeper later
  have same : survivor = target.pair := by
    simpa [List.mem_cons, accepted.selected, accepted.settled] using chosen
  rw [same, ← pair]
  simp [settleMarker, bound]

/-- Before destructive repair, a retry can settle the observed marker
contents or crash. A returned error without effects leaves the same image.
The visible marker supplied to the file barrier is the one read during
validation under the writer lock. -/
inductive UnsettledRetries (initial : FileImage) : FileImage → Prop where
  | start : UnsettledRetries initial initial
  | settle (prior : UnsettledRetries initial before) (selected : Selection)
      (observed : before.directory.active.walBoundary = some (Boundary.encode selected.frontier)) :
      UnsettledRetries initial { before with directory := settleMarker before.directory selected }
  | crash (prior : UnsettledRetries initial before)
      (metadata : pair ∈ before.directory.crashImages)
      (keeper : bytes ∈ before.keeper.crashImages) (later : names ∈ before.later.crashImages) :
      UnsettledRetries initial (before.crash pair bytes names)

/-- No retry before repair introduces a new manifest or marker choice. Every
present marker still names one of the initial allowed frontiers. The file
barrier cannot introduce a missing binding or resurrect an absent marker. -/
theorem UnsettledRetries.preserves {initial after : FileImage}
    (retries : UnsettledRetries initial after)
    (allowedManifest : Option ByteArray → Prop) (allowedMarker : Option ByteArray → Prop)
    (initialChoices : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      allowedManifest pair.manifest ∧ allowedMarker pair.walBoundary) :
    ∀ pair ∈ after.directory.active :: after.directory.crashImages,
      allowedManifest pair.manifest ∧ allowedMarker pair.walBoundary := by
  induction retries with
  | start => exact initialChoices
  | @settle before _ selected observed ih =>
    intro pair present
    have current := ih before.directory.active (List.mem_cons_self ..)
    rcases List.mem_cons.mp present with visible | surviving
    · subst pair
      simpa [settleMarker, observed] using current
    · obtain ⟨previous, member, manifest, marker⟩ :=
        (settleMarker_survivor_iff before.directory selected pair).mp surviving
      have previousAllowed := ih previous (List.mem_cons_of_mem _ member)
      refine ⟨manifest ▸ previousAllowed.1, ?_⟩
      cases status : previous.walBoundary with
      | none => simpa [marker, status] using previousAllowed.2
      | some _ => simpa [marker, status, ← observed] using current.2
  | @crash before pair bytes names _ metadata _ _ ih =>
    intro survivor present
    have same : survivor = pair := by
      simpa [FileImage.crash, Image.settled] using present
    exact same ▸ ih pair (List.mem_cons_of_mem _ metadata)

/-- A retry before the directory barrier cannot replace WAL bytes. Its
keeper can only narrow to a surviving crash image. -/
theorem UnsettledRetries.keepsWal {initial after : FileImage}
    (retries : UnsettledRetries initial after) {accepts : Option ByteArray → Prop}
    (keeper : initial.keeper.Valid accepts) :
    after.keeper.Valid accepts := by
  induction retries with
  | start => exact keeper
  | settle _ _ _ ih => exact ih
  | crash _ _ survived _ ih =>
    exact Storage.Publication.Image.settled_valid (ih.crashValid _ survived)

theorem UnsettledRetries.keepsSealed {initial after : FileImage}
    (retries : UnsettledRetries initial after) : after.kept = initial.kept := by
  induction retries with
  | start => rfl
  | settle _ _ _ ih | crash _ _ _ _ ih => exact ih

/-- At a retry that reads a present marker, the chosen frontier is one
of the two complete publications. This applies even when every preceding
open returned an error. -/
theorem UnsettledRetries.selectsOldOrNew {initial after : FileImage}
    (retries : UnsettledRetries initial after) (checkpoint : Option ByteArray)
    (old new : UInt64)
    (initialChoices : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      pair.manifest = checkpoint ∧ (pair.walBoundary = none ∨
        pair.walBoundary = some (Boundary.encode old) ∨
        pair.walBoundary = some (Boundary.encode new)))
    {selected : Selection}
    (observed : after.directory.active.walBoundary = some (Boundary.encode selected.frontier)) :
    after.directory.active.manifest = checkpoint ∧ (selected.frontier = old ∨ selected.frontier = new) := by
  have ⟨manifest, marker⟩ := retries.preserves (· = checkpoint)
    (fun marker => marker = none ∨ marker = some (Boundary.encode old) ∨
      marker = some (Boundary.encode new)) initialChoices _ (List.mem_cons_self ..)
  rw [observed] at marker
  refine ⟨manifest, ?_⟩
  rcases marker with impossible | oldMarker | newMarker
  · contradiction
  · left
    have equal := congrArg Boundary.decode (Option.some.inj oldMarker)
    simpa only [Boundary.decode_encode, Except.ok.injEq] using equal
  · right
    have equal := congrArg Boundary.decode (Option.some.inj newMarker)
    simpa only [Boundary.decode_encode, Except.ok.injEq] using equal

/-- Physical image changes admitted after the first successful directory
barrier. A failed validation, lock handoff or other step without file effects
leaves the projected image unchanged. -/
inductive SettledRetries (target : Target) (initial : FileImage) : FileImage → Prop where
  | start : SettledRetries target initial initial
  | repair (prior : SettledRetries target initial before) (effects : EffectTrace target before after) :
      SettledRetries target initial after
  | crash (prior : SettledRetries target initial before)
      (metadata : pair ∈ before.directory.crashImages)
      (keeper : bytes ∈ before.keeper.crashImages) (later : names ∈ before.later.crashImages) :
      SettledRetries target initial (before.crash pair bytes names)

/-- An arbitrary number of admitted attempts preserves the exact selected
manifest and marker, sealed bytes and all required keeper data. -/
theorem SettledRetries.preserves {target : Target} {initial after : FileImage}
    (retries : SettledRetries target initial after) (valid : initial.Valid target) :
    after.Valid target ∧ after.kept = initial.kept := by
  induction retries with
  | start => exact ⟨valid, rfl⟩
  | repair _ effects ih =>
    exact ⟨effects.valid ih.1.selected ih.1.keeper ih.1.later, effects.keepsSealed.trans ih.2⟩
  | @crash before pair bytes names _ metadata keeper later ih =>
    have same := List.mem_singleton.mp (ih.1.settled ▸ metadata)
    exact ⟨⟨same, congrArg (fun pair => [pair]) same,
      Alvoki.Storage.Publication.Image.settled_valid (ih.1.keeper.crashValid _ keeper),
      (fun visible chosen => by
        have eq : visible = names := by simpa [FileImage.crash, LaterNames.settled] using chosen
        subst visible
        exact ih.1.later _ (List.mem_cons_of_mem _ later))⟩, ih.2⟩

private theorem appendRepairTrace {target : Target} {initial middle after : FileImage}
    (first : EffectTrace target initial middle) (rest : EffectTrace target middle after) :
    EffectTrace target initial after := by
  induction rest with
  | authorized => exact .syncPruned first
  | unlink _ later ih => exact .unlink ih later
  | syncPruned _ ih => exact .syncPruned ih
  | replace _ gone ran ih => exact .replace ih gone ran
  | aligned _ gone read ih => exact .aligned ih gone read
  | scratch _ ih => exact .scratch ih
  | crash _ metadata keeper later ih => exact .crash ih metadata keeper later

/-- Once authorized, repeated repair attempts are prefixes of the same
repair trace. Reuse its replay theorem on the entire retry sequence. -/
theorem SettledRetries.replayUnchanged {target : Target} {initial first after : FileImage} {plan : Plan}
    (firstRepair : EffectTrace target initial first)
    (retries : SettledRetries target first after) (prepared : Prepared initial target plan)
    (base : Storage.PackedTable) (sealed : List (Nat × ByteArray))
    (sealedRead : ∀ file ∈ sealed, initial.kept file.1 = some file.2)
    {marker : ByteArray} {length : UInt64} (markerRead : target.pair.walBoundary = some marker)
    (decoded : Boundary.decode marker = .ok length)
    (checked : Storage.checkSelectedWalSegmentSpans (length.toNat / frameSize)
      (sealed ++ [(target.first, plan.keeperBytes)]) = true)
    {bytes : ByteArray} (survives : some bytes ∈ after.keeper.active :: after.keeper.crashImages) :
    Storage.recoverMarkedWalSegments base length (sealed ++ [(target.first, bytes)]) =
      Storage.recoverMarkedWalSegments base length (sealed ++ [(target.first, plan.keeperBytes)]) ∧
    ∀ file ∈ sealed, after.kept file.1 = some file.2 := by
  have trace : EffectTrace target initial after := by
    clear survives
    induction retries with
    | start => exact firstRepair
    | repair _ effects ih => exact appendRepairTrace ih effects
    | crash _ metadata keeper later ih => exact .crash ih metadata keeper later
  exact trace.replayUnchanged prepared base sealed sealedRead markerRead decoded checked survives

/-- Compose the first authorized repair prefix with later attempts. Every
surviving binding still selects the same frontier, even if none of the
attempts has returned a ready writer. -/
theorem SettledRetries.preservesSelectedMarker
    (initial : FileImage) (selected : Selection)
    {target : Target} {first after : FileImage} {bytes : ByteArray}
    (bound : initial.directory.active.walBoundary = some bytes)
    (firstRepair : EffectTrace target
      { initial with directory := settleMarker initial.directory selected } first)
    (pair : (settleMarker initial.directory selected).active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts)
    (later : initial.later.Beyond target.range.through)
    (retries : SettledRetries target first after)
    {survivor : Bindings} (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.walBoundary = some (Boundary.encode selected.frontier) ∧
      after.kept = initial.kept := by
  have initialValid := firstRepair.valid pair keeper later
  have ⟨finalValid, sameSeals⟩ := retries.preserves initialValid
  have same : survivor = target.pair := by
    simpa [finalValid.selected, finalValid.settled] using chosen
  refine ⟨?_, sameSeals.trans firstRepair.keepsSealed⟩
  rw [same, ← pair]
  simp [settleMarker, bound]

/-- Join retries on both sides of the authorization barrier. Before it,
the open may select either complete publication. After it, all repair
and crash survivors keep that exact choice. -/
theorem retries_preservePublishedFrontier
    {initial prepared first after : FileImage} {target : Target}
    (beforeBarrier : UnsettledRetries initial prepared)
    (checkpoint : Option ByteArray) (old new : UInt64)
    (choices : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      pair.manifest = checkpoint ∧ (pair.walBoundary = none ∨
        pair.walBoundary = some (Boundary.encode old) ∨
        pair.walBoundary = some (Boundary.encode new)))
    (selected : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (firstRepair : EffectTrace target
      { prepared with directory := settleMarker prepared.directory selected } first)
    (pair : (settleMarker prepared.directory selected).active = target.pair)
    (keeper : prepared.keeper.Valid target.Accepts)
    (later : prepared.later.Beyond target.range.through)
    (retries : SettledRetries target first after)
    {survivor : Bindings} (chosen : survivor ∈ after.directory.active :: after.directory.crashImages) :
    survivor.manifest = checkpoint ∧
      survivor.walBoundary = some (Boundary.encode selected.frontier) ∧
      (selected.frontier = old ∨ selected.frontier = new) ∧ after.kept = initial.kept := by
  have ⟨manifest, allowed⟩ := beforeBarrier.selectsOldOrNew checkpoint old new choices observed
  have ⟨valid, keep⟩ := retries.preserves (firstRepair.valid pair keeper later)
  have same : survivor = target.pair := by
    simpa [valid.selected, valid.settled] using chosen
  rw [same, ← pair]
  exact ⟨manifest, by simp [settleMarker, observed], allowed,
    keep.trans (firstRepair.keepsSealed.trans beforeBarrier.keepsSealed)⟩

/-- The native preparation feeds its decoded slot frontier into the shared
bounded reader. The returned payload uses the table from the reported
checkpoint and selected WAL, and the exact keeper from those same reads. -/
theorem prepareSelected_reported (directory : Storage.DiskDirectory) (selection : Selection)
    (readCheckpoint : Except IO.Error (Option (Storage.PackedTable × UInt64)))
    (readWal : Nat → UInt64 → Except IO.Error (Storage.WalSegmentMarkerReads × Nat))
    {checkpoint : Option (Storage.PackedTable × UInt64)} (checkpointRead : readCheckpoint = .ok checkpoint)
    {reads : Storage.WalSegmentMarkerReads} {fileSize : Nat}
    (walRead : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat selection.frontier = .ok (reads, fileSize))
    {payload : ByteArray} {table : Storage.PackedTable} {keeper : Nat} {bytes : ByteArray}
    (replayed : Storage.recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1
      selection.frontier reads.files = .ok (payload, table))
    (keeperRead : reads.files.getLast? = some (keeper, bytes)) :
    prepareBoundedMarkedFromReaders directory readCheckpoint
      (fun _ => pure (some (Boundary.encode selection.frontier))) readWal =
      .ok (⟨selection.frontier.toNat / frameSize, keeper, reads.newer, bytes⟩,
        ⟨table, (checkpoint.getD (.empty, 0)).2, selection.frontier, keeper⟩, fileSize) :=
  prepareBoundedMarkedFromReaders_reported directory readCheckpoint _ readWal checkpointRead
    rfl (Boundary.decode_encode selection.frontier) walRead replayed keeperRead

/-- Reported cached reads satisfy the replay span check when their
requested extents all start at or before the marker. -/
theorem cachedPayloads_checkSpans {directory : Storage.DiskDirectory} {through : Nat}
    {readSeal : System.FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : System.FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports directory through readSeal readKeeper required files fileSize)
    (covered : ∀ entry ∈ required, entry.1 ≤ through) :
    Storage.checkSelectedWalSegmentSpans through files = true := by
  induction reports with
  | @keeper first metadata bytes size _ _ =>
    have within := covered (first, metadata) (by simp)
    rw [Storage.checkSelectedWalSegmentSpans, Bool.and_eq_true, Storage.checkWalSegmentSpans_iff]
    exact ⟨by simp [within], ⟨_, _, rfl, within⟩, .active (Nat.le_of_eq size.symm)⟩
  | @sealed first next metadata nextMetadata bytes nextBytes rest later fileSize forward size _ _ _ _ ih =>
    have within := covered (first, metadata) (by simp)
    have tail := ih (fun entry member => covered entry (List.mem_cons_of_mem _ member))
    rw [Storage.checkSelectedWalSegmentSpans, Bool.and_eq_true, Storage.checkWalSegmentSpans_iff] at tail ⊢
    exact ⟨by simpa [within] using tail.1, ⟨_, _, rfl, within⟩, .sealed forward size tail.2.2⟩

/-- The last reported payload is the keeper prefix. Its physical size
and bytes come from the same callback. -/
theorem cachedPayloads_keeper {directory : Storage.DiskDirectory} {through : Nat}
    {readSeal : System.FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : System.FilePath → Nat → Nat → Except IO.Error ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {files : List (Nat × ByteArray)} {fileSize : Nat}
    (reports : CachedWalPayloadReports directory through readSeal readKeeper required files fileSize) :
    ∃ keeper bytes, files.getLast? = some (keeper, bytes) ∧
      bytes.size = (through - keeper) * frameSize ∧
      readKeeper (directory.file (.walSegment keeper)) bytes.size fileSize = .ok bytes := by
  induction reports with
  | @keeper first metadata bytes size _ read =>
    exact ⟨first, bytes, rfl, size, by simpa only [size] using read⟩
  | sealed _ _ _ _ _ _ ih =>
    obtain ⟨keeper, bytes, last, size, read⟩ := ih
    exact ⟨keeper, bytes, by simpa using last, size, read⟩

/-- The bounded read vector for the selected marker can omit bytes after
its keeper. Given the retained replay from the same bytes, preparation
returns that table and the physical keeper prefix for repair. -/
theorem prepareSelected_of_retainedReplay
    (directory : Storage.DiskDirectory) (selection : Selection)
    (readCheckpoint : Except IO.Error (Option (Storage.PackedTable × UInt64)))
    (list : System.FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : System.FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    {checkpoint : Option (Storage.PackedTable × UInt64)} (checkpointRead : readCheckpoint = .ok checkpoint)
    {reads : Storage.WalSegmentMarkerReads} {fileSize first : Nat}
    {firstBytes : ByteArray} {rest : List (Nat × ByteArray)}
    (files : reads.files = (first, firstBytes) :: rest)
    {markerBytes : ByteArray} (accepted : decode markerBytes = .ok selection)
    {readSeal : System.FilePath → Nat → Except IO.Error ByteArray}
    {readKeeper : System.FilePath → Nat → Nat → Except IO.Error ByteArray}
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    {extents required : List (Nat × IO.FS.Metadata)}
    (scanned : Storage.readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) = .ok extents)
    (watermark : (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ selection.frontier.toNat / frameSize)
    (selected : selectWalExtentsThrough extents (checkpoint.getD (.empty, 0)).1.committed.toNat
      (selection.frontier.toNat / frameSize) = some (required, reads.newer))
    (reports : CachedWalPayloadReports directory (selection.frontier.toNat / frameSize)
      readSeal readKeeper required reads.files fileSize)
    {physical tail payload : ByteArray} {table : Storage.PackedTable}
    (exactBytes : physical = Storage.walSegmentPayloadBytes reads.files ++ tail)
    (replayed : Boundary.recoverRetainedMarked (checkpoint.getD (.empty, 0)).1
      first selection.frontier physical = .ok (payload, table)) :
    ∃ keeper bytes,
      readKeeper (directory.file (.walSegment keeper)) bytes.size fileSize = .ok bytes ∧
      prepareBoundedMarkedFromReaders directory readCheckpoint
        (fun _ => pure (some (Boundary.encode selection.frontier)))
        (fun start frontier => readSelectedWithCachedExtents directory start frontier list lstat readSeal readKeeper) =
        .ok (⟨selection.frontier.toNat / frameSize, keeper, reads.newer, bytes⟩,
          ⟨table, (checkpoint.getD (.empty, 0)).2, selection.frontier, keeper⟩, fileSize) := by
  obtain ⟨_, _, _, aligned, _⟩ := decode_valid accepted
  have readWal := readSelectedWithCachedExtents_reported directory _ _ list lstat readSeal readKeeper
    ⟨aligned, watermark⟩ listed scanned selected reports
  have walRead : readSelectedWithCachedExtents directory (checkpoint.getD (.empty, 0)).1.committed.toNat
      selection.frontier list lstat readSeal readKeeper = .ok (reads, fileSize) := by
    cases reads
    exact readWal
  have covered : ∀ entry ∈ required, entry.1 ≤ selection.frontier.toNat / frameSize := by
    unfold selectWalExtentsThrough at selected
    cases found : ((extents.map Prod.fst).filter
      (fun offset => decide (offset ≤ (checkpoint.getD (.empty, 0)).1.committed.toNat))).max? with
    | none => simp [found, Bind.bind, Option.bind] at selected
    | some first =>
      simp [found, Bind.bind, Option.bind, Pure.pure] at selected
      rw [← selected.1]
      intro entry member
      have checked := List.all_eq_true.mp (List.all_takeWhile (p := fun item : Nat × IO.FS.Metadata =>
        decide (item.1 ≤ selection.frontier.toNat / frameSize))) entry member
      exact of_decide_eq_true checked
  obtain ⟨keeper, bytes, keeperRead, _, read⟩ := cachedPayloads_keeper reports
  refine ⟨keeper, bytes, read, ?_⟩
  refine prepareSelected_reported (payload := payload) directory selection readCheckpoint _ checkpointRead walRead ?_ keeperRead
  have checked := cachedPayloads_checkSpans reports covered
  rw [files] at checked exactBytes ⊢
  rw [Storage.recoverMarkedWalSegments_eq_retained _ _ _ _ _ tail aligned checked, ← exactBytes]
  exact replayed

open Storage.DiskSession

/-- The shared installer returns the payload from the reached two-slot
preparation. The marker barrier and repair must both report success before
allocation, and the previous session's snapshot references stay foreign. -/
theorem reopenWith_installsPrepared {image : Type} {directory : Storage.DiskDirectory}
    {descriptor nextRef : Nat} {unlock : UnlockReport}
    {before : LockedFileState image} {prepared settled after : image}
    {prepare : EStateM IO.Error image (Plan × Reopened × Nat)}
    {stabilize : EStateM IO.Error image Unit} {finish : Plan → Nat → EStateM IO.Error image Unit}
    {plan : Plan} {opened : Reopened} {size : Nat} (liveRefs : List Nat)
    (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves before.owners directory (.ok true))
    (read : prepare before.image = .ok (plan, opened, size) prepared)
    (barrier : stabilize prepared = .ok () settled)
    (repaired : finish plan size settled = .ok () after) :
    ∃ session final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (reopenWith prepare stabilize finish) before = .ok session final ∧
      session.phase = .ready opened.installed ∧ final.image = after ∧
      final.owners.Owns directory descriptor ∧ session.sessionRef ∉ liveRefs := by
  have report : reopenWith prepare stabilize finish before.image = .ok opened after := by
    simp only [reopenWith_reports, read, barrier, repaired]
  obtain ⟨session, final, success, _, _, phase, files, _, owner, _, _, freshSession⟩ :=
    runOpenWithInstallation_ready (unlock := unlock) liveRefs fresh acquisition report
  exact ⟨session, final, success, phase, files, owner, freshSession⟩

/-- Syncing the marker selected by preparation preserves its repair plan.
Only the crash choices of the marker bytes can change. -/
theorem prepared_settleMarker {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) (selected : Selection)
    (bound : image.directory.active.walBoundary = some (Boundary.encode selected.frontier)) :
    Prepared { image with directory := settleMarker image.directory selected } target plan := by
  have active : (settleMarker image.directory selected).active = image.directory.active := by
    have eta : (⟨image.directory.active.manifest, image.directory.active.walBoundary⟩ : Bindings) =
        image.directory.active := by cases image.directory.active; rfl
    simpa [settleMarker, bound] using eta
  exact ⟨active.trans prepared.pair, prepared.keeperPrefix, prepared.newer,
    prepared.through, prepared.start, prepared.names, prepared.keeperRead⟩

/-- A successful two-slot reopen uses the shared keeper repair proof
before it installs the table and allocates a fresh snapshot identity. -/
theorem reopenWith_installsAfterRepair
    {directory : Storage.DiskDirectory} {descriptor nextRef : Nat} {unlock : UnlockReport}
    {before : LockedFileState FileImage} {prepared settled : FileImage}
    {prepare : EStateM IO.Error FileImage (Plan × Reopened × Nat)}
    {stabilize : EStateM IO.Error FileImage Unit}
    {full : Plan} {opened : Reopened} {target : Target}
    (removeFile : System.FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : System.FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array System.FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : System.FilePath → System.FilePath → EStateM IO.Error FileImage Unit)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves before.owners directory (.ok true))
    (read : prepare before.image =
      .ok ({ full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize },
        opened, full.keeperBytes.size) prepared)
    (selected : Selection)
    (bound : prepared.directory.active.walBoundary = some (Boundary.encode selected.frontier))
    (plan : Prepared prepared target full)
    (reached : settled = { prepared with directory := settleMarker prepared.directory selected })
    (barrier : stabilize prepared = .ok () settled)
    (settles : sync #[directory.path] settled = .ok () settled.syncDirectory)
    (healthy : ∀ action state next, ReachesAction target settled.syncDirectory full.finishActions action state →
      state.effect target action = some next →
      performPaths directory full removeFile throw write sync renameFile action state = .ok () next) :
    ∃ session final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (reopenWith prepare stabilize (fun bounded size =>
          finishBoundedMarkedOpen directory bounded size removeFile write sync renameFile)) before =
        .ok session final ∧
      session.phase = .ready opened.installed ∧
      final.image.Ready target ∧ EffectTrace target settled final.image ∧
      final.owners.Owns directory descriptor ∧ session.sessionRef ∉ liveRefs := by
  have settledPlan : Prepared settled target full := reached.symm ▸ prepared_settleMarker plan selected bound
  obtain ⟨after, repaired, ready, trace⟩ :=
    finishMarkedOpen_completes settledPlan directory removeFile write sync renameFile settles healthy
  have bounded := finishBoundedMarkedOpen_eq_full directory full plan.valid removeFile write sync renameFile
  obtain ⟨session, final, success, phase, image, owner, newRef⟩ :=
    reopenWith_installsPrepared (descriptor := descriptor) (unlock := unlock)
      (finish := fun boundedPlan size =>
        finishBoundedMarkedOpen directory boundedPlan size removeFile write sync renameFile)
      liveRefs fresh acquisition read barrier (by rw [bounded]; exact repaired)
  exact ⟨session, final, success, phase, image.symm ▸ ready, image.symm ▸ trace, owner, newRef⟩

/-- An open that fails while reading or validating the selected WAL never
stabilizes a marker or repairs a keeper. Lock cleanup sees exactly the
state reached by preparation, including any read cursor effects. -/
theorem reopenWith_prepareError {image : Type} {directory : Storage.DiskDirectory}
    {descriptor nextRef : Nat} (unlock : UnlockReport)
    {before : LockedFileState image} {reached : image}
    {prepare : EStateM IO.Error image (Plan × Reopened × Nat)}
    {stabilize : EStateM IO.Error image Unit} {finish : Plan → Nat → EStateM IO.Error image Unit}
    {cause : IO.Error} (read : prepare before.image = .error cause reached) :
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
      (reopenWith prepare stabilize finish) before =
      match unlock with
      | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup applied => .error cleanup
          ⟨reached, before.owners.set (directory.file .lock) (if applied then none else some descriptor)⟩ := by
  have report : reopenWith prepare stabilize finish before.image = .error cause reached := by
    simp only [reopenWith_reports, read]
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired, report]
  cases unlock <;> rfl

private theorem prepareSelected_walReadError {state : Type} (directory : Storage.DiskDirectory)
    (marker : ByteArray) (frontier : UInt64) (decodes : Boundary.decode marker = .ok frontier)
    (readCheckpoint : EStateM IO.Error state (Option (Storage.PackedTable × UInt64)))
    (readWal : Nat → UInt64 → EStateM IO.Error state (Storage.WalSegmentMarkerReads × Nat))
    {before checked reached : state} {checkpoint : Option (Storage.PackedTable × UInt64)}
    (checkpointRead : readCheckpoint before = .ok checkpoint checked)
    {cause : IO.Error}
    (walRead : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat frontier checked =
      .error cause reached) :
    prepareBoundedMarkedFromReaders directory readCheckpoint
      (fun _ => pure (some marker)) readWal before =
      .error cause reached := by
  unfold prepareBoundedMarkedFromReaders
  change EStateM.bind readCheckpoint _ before = _
  rw [EStateM.bind, checkpointRead]
  have optionalRead :
      (pure (some marker) :
        EStateM IO.Error state (Option ByteArray)) checked =
        .ok (some marker) checked := rfl
  have decoded : (liftExcept ((Boundary.decode marker).mapError IO.userError) :
        EStateM IO.Error state UInt64) checked = .ok frontier checked := by
    rw [decodes]
    rfl
  cases h : checkpoint.getD (.empty, 0) with
  | mk base generation =>
    rw [h] at walRead
    change readWal base.committed.toNat frontier checked = _ at walRead
    simp only [h, Bind.bind, EStateM.bind, optionalRead, decoded, walRead]

/-- After the extent scan and the earlier seal reads, a keeper read
error aborts the shared reopen before marker sync or WAL repair. -/
theorem reopenWith_keeperReadError {state : Type} {directory : Storage.DiskDirectory}
    (selection : Selection)
    (readCheckpoint : EStateM IO.Error state (Option (Storage.PackedTable × UInt64)))
    (list : System.FilePath → EStateM IO.Error state (Array IO.FS.DirEntry))
    (lstat : System.FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    {readSeal : System.FilePath → Nat → EStateM IO.Error state ByteArray}
    (readKeeper : System.FilePath → Nat → Nat → EStateM IO.Error state ByteArray)
    (stabilize : EStateM IO.Error state Unit)
    (finish : Plan → Nat → EStateM IO.Error state Unit)
    {before checked listedState scannedState atKeeper reached : state}
    {checkpoint : Option (Storage.PackedTable × UInt64)}
    (checkpointRead : readCheckpoint before = .ok checkpoint checked)
    (aligned : selection.frontier.toNat % frameSize = 0 ∧
      (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ selection.frontier.toNat / frameSize)
    {entries : Array IO.FS.DirEntry}
    (listed : list directory.path checked = .ok entries listedState)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : Storage.readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName)) listedState =
      .ok extents scannedState)
    (selected : selectWalExtentsThrough extents (checkpoint.getD (.empty, 0)).1.committed.toNat
      (selection.frontier.toNat / frameSize) = some (required, newer))
    {keeper : Nat} {metadata : IO.FS.Metadata}
    (seals : CachedWalKeeperReached directory readSeal keeper metadata required scannedState atKeeper)
    {cause : IO.Error}
    (failed : readKeeper (directory.file (.walSegment keeper))
      ((selection.frontier.toNat / frameSize - keeper) * frameSize) metadata.byteSize.toNat atKeeper =
        .error cause reached) :
    reopenWith
      (prepareBoundedMarkedFromReaders directory readCheckpoint
        (fun _ => pure (some (Boundary.encode selection.frontier)))
        (fun watermark length =>
          readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper))
      stabilize finish before = .error cause reached := by
  have payloadError := seals.read_error (selection.frontier.toNat / frameSize) readKeeper failed
  have walError := readSelectedWithCachedExtents_payloadError directory _ selection.frontier
    list lstat readSeal readKeeper aligned listed scanned selected payloadError
  have read := prepareSelected_walReadError directory (Boundary.encode selection.frontier)
    selection.frontier (Boundary.decode_encode _) readCheckpoint
    (fun watermark length =>
      readSelectedWithCachedExtents directory watermark length list lstat readSeal readKeeper)
    checkpointRead walError
  simp only [reopenWith_reports, read]

/-- A failed file barrier returns exactly its reached file image through
lock cleanup. It cannot run keeper repair or allocate a ready session. -/
theorem reopenWith_markerSyncError {image : Type} {directory : Storage.DiskDirectory}
    {descriptor nextRef : Nat} (unlock : UnlockReport)
    {before : LockedFileState image} {prepared reached : image}
    {prepare : EStateM IO.Error image (Plan × Reopened × Nat)}
    {stabilize : EStateM IO.Error image Unit} {finish : Plan → Nat → EStateM IO.Error image Unit}
    {plan : Plan} {opened : Reopened} {size : Nat} {cause : IO.Error}
    (read : prepare before.image = .ok (plan, opened, size) prepared)
    (barrier : stabilize prepared = .error cause reached) :
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
      (reopenWith prepare stabilize finish) before =
      match unlock with
      | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup applied => .error cleanup
          ⟨reached, before.owners.set (directory.file .lock) (if applied then none else some descriptor)⟩ := by
  have report : reopenWith prepare stabilize finish before.image = .error cause reached := by
    simp only [reopenWith_reports, read, barrier]
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired, report]
  cases unlock <;> rfl

/-- A failed marker barrier either leaves the prepared file image alone
or settles only the observed marker. In either case cleanup returns an
unsettled retry image and leaves the keeper available for the next open. -/
theorem reopenWith_markerSyncError_retries {directory : Storage.DiskDirectory}
    {descriptor nextRef : Nat} (unlock : UnlockReport)
    {initial prepared reached : FileImage} {before : LockedFileState FileImage}
    (prior : UnsettledRetries initial prepared) (selection : Selection)
    (observed : prepared.directory.active.walBoundary = some (Boundary.encode selection.frontier))
    {prepare : EStateM IO.Error FileImage (Plan × Reopened × Nat)}
    {stabilize : EStateM IO.Error FileImage Unit} {finish : Plan → Nat → EStateM IO.Error FileImage Unit}
    {plan : Plan} {opened : Reopened} {size : Nat} {cause : IO.Error}
    (read : prepare before.image = .ok (plan, opened, size) prepared)
    (barrier : stabilize prepared = .error cause reached)
    (effect : reached = prepared ∨ reached = { prepared with directory := settleMarker prepared.directory selection }) :
    ∃ error final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (reopenWith prepare stabilize finish) before = .error error final ∧
      UnsettledRetries initial final.image ∧ final.image.keeper = prepared.keeper := by
  have report := reopenWith_markerSyncError (directory := directory) (descriptor := descriptor)
    (nextRef := nextRef) (finish := finish) unlock read barrier
  have retry : UnsettledRetries initial reached := by
    rcases effect with rfl | rfl
    · exact prior
    · exact .settle prior selection observed
  have keeper : reached.keeper = prepared.keeper := by
    rcases effect with rfl | rfl <;> rfl
  cases unlock <;> exact ⟨_, _, report, retry, keeper⟩

/-- For an installed segmented replay of the selected frontier, the table
behind a fresh snapshot agrees with the client history at that frontier. -/
theorem installedSnapshot_reads
    {opened : Reopened} {session : SegmentedSession}
    (installed : session.phase = .ready opened.installed)
    {image : Storage.WalSegmentImage} {pair : Bindings} {range : Storage.MarkedWalRange}
    {history : List Write} {base : Storage.PackedTable}
    (recovery : Storage.WalSegmentRecovery image pair range history base opened.keeper opened.table)
    {reference : Alvoki.Sequential.SnapshotTable UInt64}
    (replayed : Storage.SnapshotWalReplay .empty (history.take range.through) reference)
    {snapshot : UInt64} (retained : opened.table.pins.floor ≤ snapshot)
    (within : snapshot.toNat ≤ range.through) :
    ∃ state pin pinned, session.phase = .ready state ∧
      state.table.acquireAt snapshot = some (pin, pinned) ∧
      (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
      ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  obtain ⟨pin, pinned, acquired, points, ranges⟩ := recovery.acquireReads replayed retained within
  exact ⟨opened.installed, pin, pinned, installed, acquired, points, ranges⟩

end Alvoki.WAL.TwoSlot
