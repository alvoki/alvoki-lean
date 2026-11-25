import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.WalSegmentReplayStability
import Alvoki.Storage.Disk.SegmentedSessionInstall

namespace Alvoki.WAL.TwoSlot

open Alvoki.Storage.DirectoryPublication

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
      (selected.frontier = old ∨ selected.frontier = new) := by
  have ⟨manifest, allowed⟩ := beforeBarrier.selectsOldOrNew checkpoint old new choices observed
  have ⟨valid, _⟩ := retries.preserves (firstRepair.valid pair keeper later)
  have same : survivor = target.pair := by
    simpa [valid.selected, valid.settled] using chosen
  rw [same, ← pair]
  exact ⟨manifest, by simp [settleMarker, observed], allowed⟩

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
