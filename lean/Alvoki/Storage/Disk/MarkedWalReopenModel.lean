import Alvoki.Storage.Disk.WalBoundaryModel
import Alvoki.Storage.Publication.DirectoryPublicationModel

namespace Alvoki.WAL.Boundary
open Storage

/-- Directory metadata remains paired. Until a shared directory sync, WAL
contents can conservatively be chosen independently of a metadata pair. -/
structure ReopenImage where
  directory : DirectoryPublication.Image
  wal : Publication.Image

/-- Each metadata pair has an expected prefix. Every possible WAL binding must
contain the prefix required by every still selectable metadata pair. -/
private def accepts (directory : DirectoryPublication.Image)
    (expected : DirectoryPublication.Bindings → ByteArray) (walBinding : Option ByteArray) : Prop :=
  ∀ pair ∈ directory.active :: directory.crashImages,
    ∃ marker contents length, pair.walBoundary = some marker ∧ walBinding = some contents ∧
      decode marker = .ok length ∧ select length contents = .ok (expected pair)

def ReopenImage.Valid (image : ReopenImage) (expected : DirectoryPublication.Bindings → ByteArray) : Prop :=
  image.wal.Valid (accepts image.directory expected)

/-- The visible marker covers the lengths stored in all selectable pairs. -/
def MarkerBound (directory : DirectoryPublication.Image) : Prop :=
  ∃ marker length, directory.active.walBoundary = some marker ∧ decode marker = .ok length ∧
    ∀ pair ∈ directory.active :: directory.crashImages,
      ∃ candidate count, pair.walBoundary = some candidate ∧ decode candidate = .ok count ∧
        count.toNat ≤ length.toNat

theorem ReopenImage.markerBound_of_write_cut {image : ReopenImage} {boundary : Publication.Image}
    {before : List WAL.Write} {event : WAL.Write} {wal : ByteArray}
    (cut : WriteCut before event wal boundary)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size)
    (activeAgrees : image.directory.active.walBoundary = boundary.active)
    (crashAgrees : ∀ pair ∈ image.directory.crashImages, pair.walBoundary ∈ boundary.crashImages) :
    MarkerBound image.directory := by
  obtain ⟨marker, length, present, decoded, bounded⟩ := write_cut_active_bounds_marker cut oldFits newFits
  refine ⟨marker, length, activeAgrees.trans present, decoded, ?_⟩
  intro pair chosen
  rcases List.mem_cons.mp chosen with rfl | survives
  · exact bounded _ (.inl activeAgrees)
  · exact bounded _ (.inr (crashAgrees pair survives))

private theorem MarkerBound.covers {directory : DirectoryPublication.Image}
    (bound : MarkerBound directory) {marker : ByteArray} {length : UInt64}
    (visible : directory.active.walBoundary = some marker) (decoded : decode marker = .ok length) :
    ∀ pair ∈ directory.active :: directory.crashImages,
      ∀ marker count, pair.walBoundary = some marker → decode marker = .ok count → count.toNat ≤ length.toNat := by
  obtain ⟨active, limit, present, activeDecode, bounded⟩ := bound
  have sameActive : active = marker := Option.some.inj (present.symm.trans visible)
  subst active
  have sameLimit : limit = length := Except.ok.inj (activeDecode.symm.trans decoded)
  subst limit
  intro pair chosen markerBytes count marked decodedCount
  obtain ⟨candidate, candidateCount, candidateMarked, candidateDecode, fits⟩ := bounded pair chosen
  have sameCandidate : candidate = markerBytes := Option.some.inj (candidateMarked.symm.trans marked)
  subst candidate
  have sameCount : candidateCount = count := Except.ok.inj (candidateDecode.symm.trans decodedCount)
  simpa only [sameCount] using fits

/-- The repair path takes its replacement from the visible marker and WAL.
Every marker that could still survive a crash must fit in that replacement. -/
structure ReopenImage.RepairsTo (image : ReopenImage) (length : UInt64) (trimmed : ByteArray) : Prop where
  visibleMarker : ∃ marker, image.directory.active.walBoundary = some marker ∧ decode marker = .ok length
  selected : ∃ contents, image.wal.active = some contents ∧ select length contents = .ok trimmed ∧
    trimmed.size < contents.size
  coversCandidates : ∀ pair ∈ image.directory.active :: image.directory.crashImages,
    ∀ marker count, pair.walBoundary = some marker → decode marker = .ok count → count.toNat ≤ length.toNat

theorem ReopenImage.repairsTo_of_markerBound {image : ReopenImage} {marker wal trimmed : ByteArray}
    {length : UInt64} (bound : MarkerBound image.directory)
    (visibleMarker : image.directory.active.walBoundary = some marker)
    (visibleWal : image.wal.active = some wal) (decoded : decode marker = .ok length)
    (selected : select length wal = .ok trimmed) (shorter : trimmed.size < wal.size) :
    image.RepairsTo length trimmed :=
  ⟨⟨marker, visibleMarker, decoded⟩, ⟨wal, visibleWal, selected, shorter⟩,
    bound.covers visibleMarker decoded⟩

/-- A marked reopen after a modeled write cut can trim to the visible prefix.
Each joint crash pair supplies a marker allowed by the one-write model. -/
theorem ReopenImage.repairsTo_of_write_cut {image : ReopenImage} {boundary : Publication.Image}
    {before : List WAL.Write} {event : WAL.Write} {wal marker trimmed : ByteArray}
    (cut : WriteCut before event wal boundary)
    (oldFits : (WAL.encode before).size < UInt64.size)
    (newFits : (WAL.encode (before ++ [event])).size < UInt64.size)
    (activeAgrees : image.directory.active.walBoundary = boundary.active)
    (crashAgrees : ∀ pair ∈ image.directory.crashImages, pair.walBoundary ∈ boundary.crashImages)
    (visibleMarker : image.directory.active.walBoundary = some marker)
    (visibleWal : image.wal.active = some wal)
    (selected : (do let length ← decode marker; select length wal) = .ok trimmed)
    (shorter : trimmed.size < wal.size) : ∃ length, image.RepairsTo length trimmed := by
  have bound := ReopenImage.markerBound_of_write_cut cut oldFits newFits activeAgrees crashAgrees
  have visibleBound := bound
  obtain ⟨active, length, present, decoded, _⟩ := visibleBound
  have sameVisibleMarker : marker = active := Option.some.inj (visibleMarker.symm.trans present)
  have visibleDecode : decode marker = .ok length := sameVisibleMarker.symm ▸ decoded
  rw [visibleDecode] at selected
  exact ⟨length, ReopenImage.repairsTo_of_markerBound bound visibleMarker visibleWal visibleDecode selected shorter⟩

/-- The WAL repair uses the ordinary replacement schedule. A cut before its
last operation leaves both metadata bindings unsettled. A cut including the
successful directory sync settles them together with the repaired WAL name. -/
def ReopenImage.repairCut (image : ReopenImage) (trimmed : ByteArray) (cut : Nat) : Option ReopenImage :=
  (image.wal.execute trimmed (Publication.steps.take cut)).map fun wal =>
    ⟨if Publication.steps.length ≤ cut then image.directory.syncDirectory else image.directory, wal⟩

/-- On the aligned reopen path, syncing the directory settles all three names
after the visible WAL has been synced. -/
def ReopenImage.syncDirectory (image : ReopenImage) : ReopenImage :=
  ⟨image.directory.syncDirectory, { image.wal with crashImages := [image.wal.active] }⟩

/-- A directory sync without a guaranteed WAL file sync settles the metadata
pair while retaining the previous overapproximation of crash WAL contents. -/
def ReopenImage.syncMetadata (image : ReopenImage) : ReopenImage :=
  { image with directory := image.directory.syncDirectory }

/-- A file sync can preserve the visible contents even when the directory
binding is unresolved. Keep all earlier candidates as well. -/
def ReopenImage.allowVisibleWal (image : ReopenImage) : ReopenImage :=
  { image with wal := { image.wal with crashImages := image.wal.active :: image.wal.crashImages } }

def ReopenImage.crash (pair : DirectoryPublication.Bindings) (wal : Option ByteArray) : ReopenImage :=
  ⟨.settled pair, .settled wal⟩

private theorem accepts_syncDirectory {directory : DirectoryPublication.Image}
    {expected : DirectoryPublication.Bindings → ByteArray} {wal : Option ByteArray}
    (valid : accepts directory expected wal) : accepts directory.syncDirectory expected wal := by
  intro pair chosen
  have current : pair = directory.active := by
    simpa [DirectoryPublication.Image.syncDirectory] using chosen
  exact valid pair (List.mem_cons.mpr (.inl current))

private theorem accepts_repair {image : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    {length : UInt64} {trimmed : ByteArray}
    (valid : image.Valid expected) (repair : image.RepairsTo length trimmed) :
    accepts image.directory expected (some trimmed) := by
  obtain ⟨contents, present, selected, _⟩ := repair.selected
  intro pair chosen
  obtain ⟨marker, old, count, bound, same, decoded, selectedPrefix⟩ := valid.activeValid pair chosen
  rw [present] at same
  cases same
  have fits := repair.coversCandidates pair chosen marker count bound decoded
  exact ⟨marker, trimmed, count, bound, rfl, decoded,
    (select_shorter_after_trim selected fits).trans selectedPrefix⟩

theorem ReopenImage.repairCut_valid {image after : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} {length : UInt64} {trimmed : ByteArray}
    (valid : image.Valid expected) (repair : image.RepairsTo length trimmed)
    (cut : Nat) (ran : image.repairCut trimmed cut = some after) : after.Valid expected := by
  unfold repairCut at ran
  obtain ⟨wal, replaced, rfl⟩ := Option.map_eq_some_iff.mp ran
  have path : Publication.Retry (fun _ bytes => bytes = trimmed) image.wal wal :=
    .attempt (.refl _) rfl cut replaced
  have acceptsReplacement := accepts_repair valid repair
  have walValid := Publication.retry_preserves
    (fun _ _ _ equal => equal.symm ▸ acceptsReplacement) valid path
  by_cases complete : Publication.steps.length ≤ cut
  · simpa only [Valid, ite_eq_left complete] using
      (show wal.Valid (accepts image.directory.syncDirectory expected) from
        ⟨walValid.hasCrashImage, accepts_syncDirectory walValid.activeValid,
          fun candidate survives => accepts_syncDirectory (walValid.crashValid candidate survives)⟩)
  · simpa only [Valid, ite_eq_right complete] using walValid

theorem ReopenImage.repair_complete (image : ReopenImage) (trimmed : ByteArray) :
    image.repairCut trimmed Publication.steps.length =
      some ⟨image.directory.syncDirectory, .settled (some trimmed)⟩ := by
  simp [repairCut, Publication.successful_replace]

theorem ReopenImage.syncDirectory_valid {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected) :
    image.syncDirectory.Valid expected := by
  refine ⟨by simp [syncDirectory], accepts_syncDirectory valid.activeValid, ?_⟩
  intro wal survives
  have selected : wal = image.wal.active := List.mem_singleton.mp survives
  exact selected.symm ▸ accepts_syncDirectory valid.activeValid

theorem ReopenImage.syncMetadata_valid {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected) :
    image.syncMetadata.Valid expected :=
  ⟨valid.hasCrashImage, accepts_syncDirectory valid.activeValid,
    fun candidate survives => accepts_syncDirectory (valid.crashValid candidate survives)⟩

theorem ReopenImage.allowVisibleWal_valid {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected) :
    image.allowVisibleWal.Valid expected := by
  refine ⟨by simp [allowVisibleWal], valid.activeValid, ?_⟩
  intro wal survives
  rcases List.mem_cons.mp survives with rfl | prior
  · exact valid.activeValid
  · exact valid.crashValid wal prior

theorem ReopenImage.crash_valid {image : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    (valid : image.Valid expected) {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataSurvives : pair ∈ image.directory.crashImages) (walSurvives : wal ∈ image.wal.crashImages) :
    (crash pair wal).Valid expected := by
  apply Publication.Image.settled_valid
  intro installed chosen
  have selected : installed = pair := by
    simpa [crash, DirectoryPublication.Image.settled] using chosen
  exact valid.crashValid wal walSurvives installed (List.mem_cons.mpr (.inr (selected.symm ▸ metadataSurvives)))

/-- A failed repair can retry from any schedule cut, including one whose
directory sync took effect. A crash chooses a metadata pair and a WAL binding. -/
inductive ReopenRetry (initial : ReopenImage) : ReopenImage → Prop where
  | start : ReopenRetry initial initial
  | repair (path : ReopenRetry initial before) (choice : before.RepairsTo length trimmed)
      (ran : before.repairCut trimmed cut = some after) : ReopenRetry initial after
  | syncDirectory (path : ReopenRetry initial before) : ReopenRetry initial before.syncDirectory
  | syncMetadata (path : ReopenRetry initial before) : ReopenRetry initial before.syncMetadata
  | allowVisibleWal (path : ReopenRetry initial before) : ReopenRetry initial before.allowVisibleWal
  | crash (path : ReopenRetry initial before) (pairSurvives : pair ∈ before.directory.crashImages)
      (walSurvives : wal ∈ before.wal.crashImages) : ReopenRetry initial (.crash pair wal)

/-- Every metadata pair available after reopen was already visible or could
survive a crash before the first attempt. Sync settles the visible pair, and a
crash settles one of its saved pairs. -/
theorem ReopenRetry.chosen_pair_from_initial {initial after : ReopenImage}
    (path : ReopenRetry initial after) {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ after.directory.active :: after.directory.crashImages) :
    pair ∈ initial.directory.active :: initial.directory.crashImages := by
  have fromSync (directory : DirectoryPublication.Image)
      (selected : pair ∈ directory.syncDirectory.active :: directory.syncDirectory.crashImages) :
      pair ∈ directory.active :: directory.crashImages := by
    have visible : pair = directory.active := by
      simpa [DirectoryPublication.Image.syncDirectory] using selected
    exact List.mem_cons.mpr (.inl visible)
  induction path with
  | start => exact chosen
  | repair _ _ ran earlier =>
    apply earlier
    unfold ReopenImage.repairCut at ran
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp ran
    dsimp only at chosen
    split at chosen
    · exact fromSync _ chosen
    · exact chosen
  | syncDirectory _ earlier => exact earlier (fromSync _ chosen)
  | syncMetadata _ earlier => exact earlier (fromSync _ chosen)
  | allowVisibleWal _ earlier => exact earlier chosen
  | crash _ survives _ earlier =>
    apply earlier
    simp [ReopenImage.crash, DirectoryPublication.Image.settled] at chosen
    cases chosen
    exact List.mem_cons.mpr (.inr survives)

private theorem markerBound_single {directory : DirectoryPublication.Image}
    {marker : ByteArray} {count : UInt64} (single : directory.crashImages = [directory.active])
    (visible : directory.active.walBoundary = some marker) (decoded : decode marker = .ok count) :
    MarkerBound directory := by
  refine ⟨marker, count, visible, decoded, ?_⟩
  intro pair chosen
  have same : pair = directory.active := by simpa [single] using chosen
  exact ⟨marker, count, same.symm ▸ visible, decoded, Nat.le_refl _⟩

private theorem MarkerBound.syncDirectory {directory : DirectoryPublication.Image}
    (bound : MarkerBound directory) : MarkerBound directory.syncDirectory := by
  obtain ⟨marker, count, visible, decoded, _⟩ := bound
  exact markerBound_single rfl visible decoded

/-- An attempt preserves the marker bound. Settlement or crash reduces the
directory choices to one decoded pair, which covers itself. -/
theorem ReopenRetry.markerBound {initial after : ReopenImage}
    (path : ReopenRetry initial after) (bound : MarkerBound initial.directory) :
    MarkerBound after.directory := by
  induction path with
  | start => exact bound
  | repair _ _ ran earlier =>
    unfold ReopenImage.repairCut at ran
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp ran
    dsimp only
    split
    · exact earlier.syncDirectory
    · exact earlier
  | syncDirectory _ earlier => exact earlier.syncDirectory
  | syncMetadata _ earlier => exact earlier.syncDirectory
  | allowVisibleWal _ earlier => exact earlier
  | crash _ survives _ earlier =>
    obtain ⟨_, _, _, _, choices⟩ := earlier
    obtain ⟨marker, count, visible, decoded, _⟩ := choices _ (List.mem_cons.mpr (.inr survives))
    exact markerBound_single rfl visible decoded

theorem reopenRetry_valid {initial after : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    (valid : initial.Valid expected) (path : ReopenRetry initial after) : after.Valid expected := by
  induction path with
  | start => exact valid
  | repair _ choice ran earlier => exact ReopenImage.repairCut_valid earlier choice _ ran
  | syncDirectory _ earlier => exact ReopenImage.syncDirectory_valid earlier
  | syncMetadata _ earlier => exact ReopenImage.syncMetadata_valid earlier
  | allowVisibleWal _ earlier => exact ReopenImage.allowVisibleWal_valid earlier
  | crash _ pairSurvives walSurvives earlier =>
    exact ReopenImage.crash_valid earlier pairSurvives walSurvives

/-- Every selectable metadata pair and WAL binding selects its expected prefix. -/
theorem ReopenImage.select_chosen {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected)
    {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataChosen : pair ∈ image.directory.active :: image.directory.crashImages)
    (walChosen : wal ∈ image.wal.active :: image.wal.crashImages) :
    ∃ marker contents, pair.walBoundary = some marker ∧ wal = some contents ∧
      (do let length ← decode marker; select length contents) = .ok (expected pair) := by
  have accepted : accepts image.directory expected wal := by
    rcases List.mem_cons.mp walChosen with rfl | survives
    · exact valid.activeValid
    · exact valid.crashValid _ survives
  obtain ⟨marker, contents, length, boundary, present, decoded, selected⟩ := accepted pair metadataChosen
  refine ⟨marker, contents, boundary, present, ?_⟩
  rw [decoded]
  exact selected

/-- Given the checkpoint that belongs to the chosen metadata pair, its replay
input is unchanged by retries, even if the physical WAL name selects the old file. -/
theorem ReopenImage.recover_chosen {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected)
    (checkpoint : PackedTable) {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataChosen : pair ∈ image.directory.active :: image.directory.crashImages)
    (walChosen : wal ∈ image.wal.active :: image.wal.crashImages) :
    ∃ marker contents, pair.walBoundary = some marker ∧ wal = some contents ∧
      (do
        let length ← decode marker
        let selected ← select length contents
        recoverSelected checkpoint selected) = recoverSelected checkpoint (expected pair) := by
  obtain ⟨marker, contents, boundary, present, selected⟩ := ReopenImage.select_chosen valid metadataChosen walChosen
  refine ⟨marker, contents, boundary, present, ?_⟩
  rw [← bind_assoc, selected]
  rfl

/-- An error may be reported before or after the modeled step takes effect.
A partially written temporary file can use the no-effect abstraction: it
changes no active binding and the next attempt overwrites it before use. -/
inductive RepairReport where
  | success
  | failure (message : String) (tookEffect : Bool)

private def ReopenImage.repairStep (image : ReopenImage) (trimmed : ByteArray)
    (action : Publication.Step) : Option ReopenImage :=
  (image.wal.step trimmed action).map fun wal =>
    ⟨if action = .syncDirectory then image.directory.syncDirectory else image.directory, wal⟩

private def ReopenImage.repairSteps (image : ReopenImage) (trimmed : ByteArray)
    (actions : List Publication.Step) : Option ReopenImage :=
  actions.foldlM (fun current action => current.repairStep trimmed action) image

private theorem ReopenImage.repairSteps_prefix (image : ReopenImage) (trimmed : ByteArray)
    (cut : Nat) : image.repairSteps trimmed (Publication.steps.take cut) = image.repairCut trimmed cut := by
  rcases cut with _ | _ | _ | _ | cut
  · rfl
  · rfl
  · rfl
  · rfl
  · have complete : Publication.steps.length ≤ cut + 1 + 1 + 1 + 1 := by
      simp [Publication.steps]
    rw [List.take_of_length_le complete, repairCut, List.take_of_length_le complete, ite_eq_left complete]
    rfl

/-- Interpret one reported operation of the shared WAL replacement schedule. -/
def performRepair (report : Publication.Step → RepairReport) (trimmed : ByteArray)
    (action : Publication.Step) : EStateM String ReopenImage Unit := fun image =>
  match report action with
  | .success =>
    match image.repairStep trimmed action with
    | some after => .ok () after
    | none => .error "invalid repair operation" image
  | .failure message tookEffect =>
    .error message (if tookEffect then (image.repairStep trimmed action).getD image else image)

private def settleMetadataResult :
    EStateM.Result String ReopenImage α → EStateM.Result String ReopenImage α
  | .ok value image => .ok value image.syncMetadata
  | .error message image => .error message image.syncMetadata

private theorem ReopenImage.repairStep_syncMetadata (image : ReopenImage)
    (trimmed : ByteArray) (step : Publication.Step) :
    image.syncMetadata.repairStep trimmed step =
      (image.repairStep trimmed step).map ReopenImage.syncMetadata := by
  unfold repairStep
  change (image.wal.step trimmed step).map _ = ((image.wal.step trimmed step).map _).map _
  cases image.wal.step trimmed step <;> cases step <;> rfl

private theorem performRepair_syncMetadata (report : Publication.Step → RepairReport)
    (trimmed : ByteArray) (step : Publication.Step) (image : ReopenImage) :
    performRepair report trimmed step image.syncMetadata =
      settleMetadataResult (performRepair report trimmed step image) := by
  unfold performRepair
  rw [image.repairStep_syncMetadata]
  cases report step with
  | success => cases image.repairStep trimmed step <;> rfl
  | failure _ tookEffect => cases tookEffect <;> cases image.repairStep trimmed step <;> rfl

private theorem repairSchedule_syncMetadata (report : Publication.Step → RepairReport)
    (trimmed : ByteArray) (actions : List Publication.Step) (image : ReopenImage) :
    (actions.forM (performRepair report trimmed)) image.syncMetadata =
      settleMetadataResult ((actions.forM (performRepair report trimmed)) image) := by
  induction actions generalizing image with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind]
    rw [performRepair_syncMetadata]
    cases performRepair report trimmed step image with
    | ok _ next => exact ih next
    | error _ _ => rfl

private theorem performRepair_outcome (report : Publication.Step → RepairReport) (trimmed : ByteArray)
    (action : Publication.Step) (image : ReopenImage) :
    match performRepair report trimmed action image with
    | .ok _ after => image.repairStep trimmed action = some after
    | .error _ after => after = image ∨ image.repairStep trimmed action = some after := by
  cases reported : report action with
  | success => cases applied : image.repairStep trimmed action <;> simp [performRepair, reported, applied]
  | failure message tookEffect =>
    cases tookEffect
    · simp [performRepair, reported]
    · cases applied : image.repairStep trimmed action <;> simp [performRepair, reported, applied]

private theorem repairSchedule_outcome (report : Publication.Step → RepairReport) (trimmed : ByteArray)
    (actions : List Publication.Step) (image : ReopenImage) :
    match (actions.forM (performRepair report trimmed)) image with
    | .ok _ after => image.repairSteps trimmed actions = some after
    | .error _ after => ∃ cut, image.repairSteps trimmed (actions.take cut) = some after := by
  have outcome := Publication.run_effects_outcome
    (State := ReopenImage) (Action := Publication.Step) (Error := String)
    (fun state action => state.repairStep trimmed action) (performRepair report trimmed)
    (by
      intro action state
      have effect := performRepair_outcome report trimmed action state
      cases ran : performRepair report trimmed action state <;> simpa only [ran] using effect) actions image
  cases ran : (actions.forM (performRepair report trimmed)) image <;>
    simpa only [ran, ReopenImage.repairSteps] using outcome

/-- The aligned path asks for both the WAL file and the directory sync.
A reported failure may follow completion of any subset of those requests. -/
inductive AlignedSyncReport where
  | success
  | failure (message : String) (walSynced directorySynced : Bool)

/-- Interpret the grouped sync's reported effects on the WAL and directory. -/
def performAlignedSync (walAlreadySynced : Bool) (report : AlignedSyncReport) :
    EStateM String ReopenImage Unit := fun image =>
  match report with
  | .success => .ok () image.syncDirectory
  | .failure message walSynced directorySynced =>
    .error message (if directorySynced then
      if walAlreadySynced || walSynced then image.syncDirectory else image.syncMetadata.allowVisibleWal
    else if walSynced then image.allowVisibleWal else image)

private theorem performAlignedSync_syncMetadata (walAlreadySynced : Bool)
    (report : AlignedSyncReport) (image : ReopenImage) :
    performAlignedSync walAlreadySynced report image.syncMetadata =
      settleMetadataResult (performAlignedSync walAlreadySynced report image) := by
  cases report with
  | success => rfl
  | failure _ walSynced directorySynced =>
    cases directorySynced <;> cases walSynced <;> cases walAlreadySynced <;> rfl

/-- The validated WAL and the table computed before any reopen effects. -/
structure MarkedPreflight where
  contents : ByteArray
  selected : ByteArray
  table : PackedTable

/-- Read-only preflight of an already marked database. The checkpoint input
is the result of opening its manifest and run set, with an empty base on
absence. The marker and WAL inputs include metadata and read errors. -/
def markedReopenPreflight (checkpoint : Except String PackedTable)
    (marker wal : Except String (Option ByteArray)) : Except String MarkedPreflight := do
  let base ← checkpoint
  withOpenWal marker wal id (fun _ => .error missingOpenWal) fun boundary contents => do
    let some count := boundary | throw "marked reopen is missing its WAL boundary"
    let (selected, table) ← recoverMarked base count contents
    return ⟨contents, selected, table⟩

theorem markedReopenPreflight_selected {checkpoint : Except String PackedTable}
    {marker wal : Except String (Option ByteArray)} {validated : MarkedPreflight}
    (ready : markedReopenPreflight checkpoint marker wal = .ok validated) :
    ∃ base markerBytes length, checkpoint = .ok base ∧ marker = .ok (some markerBytes) ∧
      wal = .ok (some validated.contents) ∧ decode markerBytes = .ok length ∧
      select length validated.contents = .ok validated.selected ∧
      recoverSelected base validated.selected = .ok validated.table := by
  cases checkpoint with
  | error => contradiction
  | ok base =>
    rcases marker with _ | (_ | markerBytes)
    · contradiction
    · rcases wal with _ | (_ | _) <;> contradiction
    · dsimp only [markedReopenPreflight, Bind.bind, Except.bind] at ready
      rw [withOpenWal_marked] at ready
      cases decoded : decode markerBytes with
      | error => rw [decoded] at ready; contradiction
      | ok length =>
        rw [decoded] at ready
        rcases wal with _ | (_ | bytes)
        · contradiction
        · contradiction
        · change (do
            let (selected, table) ← recoverMarked base length bytes
            pure (⟨bytes, selected, table⟩ : MarkedPreflight)) = .ok validated at ready
          simp only [recoverMarked, bind_assoc, pure_bind] at ready
          cases accepted : select length bytes with
          | error => rw [accepted] at ready; contradiction
          | ok selected =>
            rw [accepted] at ready
            change (do
              let table ← recoverSelected base selected
              pure (⟨bytes, selected, table⟩ : MarkedPreflight)) = .ok validated at ready
            cases replayed : recoverSelected base selected with
            | error => rw [replayed] at ready; contradiction
            | ok table =>
              rw [replayed] at ready
              cases Except.ok.inj ready
              exact ⟨base, markerBytes, length, rfl, rfl, rfl, decoded, accepted, replayed⟩

/-- A missing WAL after a valid marker is an error, so marked reopen never
creates a replacement WAL for a missing durable prefix. -/
theorem markedReopenPreflight_missingWal (base : PackedTable) {marker : ByteArray}
    {length : UInt64} (decoded : decode marker = .ok length) :
    markedReopenPreflight (.ok base) (.ok (some marker)) (.ok none) = .error missingOpenWal := by
  dsimp only [markedReopenPreflight, Bind.bind, Except.bind]
  rw [withOpenWal_marked, decoded]
  rfl

/-- Interpret the shared reopen decision in a state-and-error monad. The
`walAlreadySynced` fact may be used only when the caller knows the current
visible inode's bytes are durable. A file-only effect allows the visible
contents alongside prior crash choices. A directory-only effect settles
metadata and permits both prior and visible contents unless the visible
contents are known durable. -/
def runMarkedReopen (preflight : Except String MarkedPreflight)
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool)
    (aligned : AlignedSyncReport) : EStateM String ReopenImage PackedTable :=
  match preflight with
  | .error message => fun image => .error message image
  | .ok validated =>
    Publication.finishReopen validated.contents.size validated.selected.size
      (fun _ => Publication.run (performRepair report validated.selected))
      (fun _ => performAlignedSync walAlreadySynced aligned) validated.table

/-- A late fsync of the same database directory commutes with the reported
marked reopen. It settles the metadata that is visible when it runs. The
preflight bytes, return value or error, and WAL effects stay the same.
The model gives this extra event only directory effects. -/
theorem runMarkedReopen_syncMetadata (preflight : Except String MarkedPreflight)
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool)
    (aligned : AlignedSyncReport) (image : ReopenImage) :
    runMarkedReopen preflight report walAlreadySynced aligned image.syncMetadata =
      match runMarkedReopen preflight report walAlreadySynced aligned image with
      | .ok table after => .ok table after.syncMetadata
      | .error message after => .error message after.syncMetadata := by
  have asSettled (result : EStateM.Result String ReopenImage PackedTable) :
      (match result with
      | .ok table after => EStateM.Result.ok table after.syncMetadata
      | .error message after => EStateM.Result.error message after.syncMetadata) =
        settleMetadataResult result := by cases result <;> rfl
  rw [asSettled]
  cases preflight with
  | error => rfl
  | ok validated =>
    by_cases shorter : validated.selected.size < validated.contents.size
    · simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen_repair _ _ shorter,
        Bind.bind, EStateM.bind, Publication.run, repairSchedule_syncMetadata]
      cases (Publication.steps.forM (performRepair report validated.selected)) image <;> rfl
    · simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen_aligned _ _ shorter,
        Bind.bind, EStateM.bind, performAlignedSync_syncMetadata]
      cases performAlignedSync walAlreadySynced aligned image <;> rfl

/-- The successful durability phase only needs the validated contents and
selection. The repair branch replaces the WAL and settles its name, while
the aligned branch settles the WAL already visible to the caller. -/
theorem runMarkedReopen_durability_success (validated : MarkedPreflight)
    (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport) (before : ReopenImage)
    (repaired : validated.selected.size < validated.contents.size →
      ∀ step, report step = .success)
    (synced : ¬ validated.selected.size < validated.contents.size → aligned = .success) :
    runMarkedReopen (.ok validated) report false aligned before =
      .ok validated.table (if validated.selected.size < validated.contents.size then
        ⟨before.directory.syncDirectory, .settled (some validated.selected)⟩
        else before.syncDirectory) := by
  by_cases shorter : validated.selected.size < validated.contents.size
  · have reports : report = fun _ => .success := funext (repaired shorter)
    rw [ite_eq_left shorter, runMarkedReopen, Publication.finishReopen,
      Publication.runReopen_repair _ _ shorter, reports]
    rfl
  · rw [ite_eq_right shorter, runMarkedReopen, Publication.finishReopen,
      Publication.runReopen_aligned _ _ shorter, synced shorter]
    rfl

/-- Reported repair effects choose a prefix of the shared replacement
schedule. The entire replacement must have completed on success. -/
theorem runMarkedReopen_repair_outcome (validated : MarkedPreflight)
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool) (aligned : AlignedSyncReport)
    (before : ReopenImage) (shorter : validated.selected.size < validated.contents.size) :
    match runMarkedReopen (.ok validated) report walAlreadySynced aligned before with
    | .ok table after => table = validated.table ∧
        before.repairCut validated.selected Publication.steps.length = some after
    | .error _ after => ∃ cut, before.repairCut validated.selected cut = some after := by
  simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen_repair _ _ shorter]
  have outcome := repairSchedule_outcome report validated.selected Publication.steps before
  unfold Publication.run
  cases result : (Publication.steps.forM (performRepair report validated.selected)) before with
  | ok _ after =>
    rw [result] at outcome
    simp only [Bind.bind, EStateM.bind, result, Pure.pure, EStateM.pure]
    refine ⟨True.intro, ?_⟩
    rw [← before.repairSteps_prefix]
    simpa only [List.take_length] using outcome
  | error _ after =>
    rw [result] at outcome
    simp only [Bind.bind, EStateM.bind, result]
    obtain ⟨cut, ran⟩ := outcome
    exact ⟨cut, (before.repairSteps_prefix _ _).symm.trans ran⟩

theorem runMarkedReopen_preflight_error {checkpoint : Except String PackedTable}
    {marker wal : Except String (Option ByteArray)} {message : String}
    (failed : markedReopenPreflight checkpoint marker wal = .error message)
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool)
    (aligned : AlignedSyncReport) (image : ReopenImage) :
    runMarkedReopen (markedReopenPreflight checkpoint marker wal) report walAlreadySynced aligned image =
      .error message image := by
  rw [failed]
  rfl

/-- The shared schedule follows the retry relation, including when an error
is returned after some effects. A successful reopen settles both metadata
and WAL crash choices. The short branch requires the visible prefix to
cover all still possible markers, as established from a write-cut witness. -/
theorem ReopenRetry.runMarkedReopen_effect {initial before : ReopenImage}
    (path : ReopenRetry initial before) (preflight : Except String MarkedPreflight)
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool) (aligned : AlignedSyncReport)
    (repair : ∀ validated, preflight = .ok validated →
      validated.selected.size < validated.contents.size → ∃ length, before.RepairsTo length validated.selected) :
    match runMarkedReopen preflight report walAlreadySynced aligned before with
    | .ok table after => ReopenRetry initial after ∧ after.directory = before.directory.syncDirectory ∧
        after.wal.crashImages = [after.wal.active] ∧
        ∃ validated, preflight = .ok validated ∧ table = validated.table ∧
          after.wal.active = if validated.selected.size < validated.contents.size then
            some validated.selected else before.wal.active
    | .error _ after => ReopenRetry initial after := by
  cases preflight with
  | error message => exact path
  | ok validated =>
    by_cases shorter : validated.selected.size < validated.contents.size
    · obtain ⟨length, covers⟩ := repair validated rfl shorter
      have outcome := runMarkedReopen_repair_outcome validated report walAlreadySynced aligned before shorter
      cases result : runMarkedReopen (.ok validated) report walAlreadySynced aligned before with
      | ok table after =>
        rw [result] at outcome
        obtain ⟨rfl, complete⟩ := outcome
        have ran := before.repair_complete validated.selected
        rw [ran] at complete
        cases complete
        exact ⟨.repair path covers ran, rfl, rfl, validated, rfl, rfl, by
          simp [shorter, Publication.Image.settled]⟩
      | error _ after =>
        rw [result] at outcome
        obtain ⟨cut, ran⟩ := outcome
        exact .repair path covers ran
    · simp only [runMarkedReopen, Publication.finishReopen,
        Publication.runReopen_aligned _ _ shorter]
      cases aligned with
      | success =>
        exact ⟨.syncDirectory path, rfl, rfl, validated, rfl, rfl, by simp [ReopenImage.syncDirectory, shorter]⟩
      | failure message walSynced directorySynced =>
        simp only [Bind.bind, EStateM.bind, performAlignedSync]
        split
        · split
          · exact .syncDirectory path
          · exact .allowVisibleWal (.syncMetadata path)
        · split
          · exact .allowVisibleWal path
          · exact path

/-- Successful optional reads under the database lock observe the visible
bindings, including absence. A lookup or read error stays separate. -/
structure MarkedWalReads (image : ReopenImage) where
  marker : Except String (Option ByteArray)
  wal : Except String (Option ByteArray)
  markerVisible : ∀ found, marker = .ok found → image.directory.active.walBoundary = found
  walVisible : ∀ found, wal = .ok found → image.wal.active = found

/-- Opening the checkpoint supplies its own observed result before recovery
reads or repairs the WAL. -/
structure MarkedReopenReads (image : ReopenImage) extends MarkedWalReads image where
  checkpoint : Except String PackedTable

def MarkedReopenReads.preflight {image : ReopenImage} (reads : MarkedReopenReads image) :
    Except String MarkedPreflight :=
  markedReopenPreflight reads.checkpoint reads.marker reads.wal

/-- Successful primitive reads, selection and pure replay produce the exact
preflight used by the shared open. Durability is checked by its own reports. -/
theorem MarkedReopenReads.preflight_succeeds {before : ReopenImage}
    (reads : MarkedReopenReads before) {base table : PackedTable} {length : UInt64}
    {marker contents selected : ByteArray}
    (checkpointRead : reads.checkpoint = .ok base)
    (markerRead : reads.marker = .ok (some marker)) (walRead : reads.wal = .ok (some contents))
    (decoded : decode marker = .ok length) (selection : select length contents = .ok selected)
    (replay : recoverSelected base selected = .ok table) :
    reads.preflight = .ok ⟨contents, selected, table⟩ := by
  have recovered : recoverMarked base length contents = .ok (selected, table) := by
    unfold recoverMarked
    rw [selection]
    change (recoverSelected base selected >>= fun loaded => Except.ok (selected, loaded)) = _
    rw [replay]
    rfl
  unfold MarkedReopenReads.preflight markedReopenPreflight
  rw [checkpointRead]
  change (withOpenWal reads.marker reads.wal id _ _) = _
  rw [markerRead, withOpenWal_marked, decoded, walRead]
  change (recoverMarked base length contents >>= fun (chosen, loaded) =>
    Except.ok (⟨contents, chosen, loaded⟩ : MarkedPreflight)) = _
  rw [recovered]
  rfl

/-- A read observation still describes the same live files after an extra
directory sync. Only the crash choices of the metadata have changed. -/
def MarkedReopenReads.afterDirectorySync {before : ReopenImage} (reads : MarkedReopenReads before) :
    MarkedReopenReads before.syncMetadata :=
  ⟨⟨reads.marker, reads.wal, reads.markerVisible, reads.walVisible⟩, reads.checkpoint⟩

private theorem MarkedReopenReads.repair {before : ReopenImage}
    (reads : MarkedReopenReads before) (bound : MarkerBound before.directory)
    {validated : MarkedPreflight} (ready : reads.preflight = .ok validated)
    (shorter : validated.selected.size < validated.contents.size) :
    ∃ length, before.RepairsTo length validated.selected := by
  obtain ⟨_, marker, length, _, readMarker, readWal, decoded, accepted, _⟩ :=
    markedReopenPreflight_selected (checkpoint := reads.checkpoint) (marker := reads.marker)
      (wal := reads.wal) ready
  exact ⟨length, ReopenImage.repairsTo_of_markerBound bound (reads.markerVisible _ readMarker)
    (reads.walVisible _ readWal) decoded accepted shorter⟩

private theorem MarkedReopenReads.retry_effect {initial before : ReopenImage}
    (reads : MarkedReopenReads before) (path : ReopenRetry initial before)
    (bound : MarkerBound before.directory) (report : Publication.Step → RepairReport)
    (aligned : AlignedSyncReport) :
    match runMarkedReopen reads.preflight report false aligned before with
    | .ok _ after => ReopenRetry initial after
    | .error _ after => ReopenRetry initial after := by
  have effect := path.runMarkedReopen_effect reads.preflight report false aligned
    (fun _ => reads.repair bound)
  cases result : runMarkedReopen reads.preflight report false aligned before with
  | ok _ after =>
    rw [result] at effect
    exact effect.1
  | error message after =>
    rw [result] at effect
    exact effect

private theorem select_unchanged {length : UInt64} {contents selected : ByteArray}
    (accepted : select length contents = .ok selected)
    (aligned : ¬ selected.size < contents.size) : selected = contents := by
  have exactSize := select_size accepted
  unfold select at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · have same : contents.size = length.toNat := by omega
      rw [ite_eq_left same] at accepted
      exact (Except.ok.inj accepted).symm

/-- Successful marked reopen makes the selected bytes the live and durable
WAL. This concerns the completed durability action. The stronger bound on
other markers is needed when proving safety across interrupted repairs. -/
theorem MarkedReopenReads.success_selectedWal {before after : ReopenImage}
    (reads : MarkedReopenReads before) {validated : MarkedPreflight}
    (ready : reads.preflight = .ok validated)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport} {table : PackedTable}
    (ran : runMarkedReopen reads.preflight report false aligned before = .ok table after) :
    after.wal.active = some validated.selected ∧ after.wal.crashImages = [some validated.selected] := by
  rw [ready] at ran
  by_cases shorter : validated.selected.size < validated.contents.size
  · have outcome := runMarkedReopen_repair_outcome validated report false aligned before shorter
    rw [ran] at outcome
    have complete := outcome.2
    rw [before.repair_complete] at complete
    cases complete
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, readWal, _, selected, _⟩ :=
      markedReopenPreflight_selected (checkpoint := reads.checkpoint) (marker := reads.marker)
        (wal := reads.wal) ready
    have exactWal : before.wal.active = some validated.selected := by
      rw [select_unchanged selected shorter]
      exact reads.walVisible _ readWal
    simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen_aligned _ _ shorter] at ran
    cases aligned with
    | failure _ _ _ => contradiction
    | success =>
      change EStateM.Result.ok validated.table before.syncDirectory = .ok table after at ran
      cases ran
      exact ⟨exactWal, congrArg List.singleton exactWal⟩

/-- A successful attempt installs the exact replay result and settles both
file choices. Repair installs its selected prefix, and the aligned path
leaves the already exact prefix in place. -/
theorem MarkedReopenReads.success {before after : ReopenImage}
    (reads : MarkedReopenReads before) (bound : MarkerBound before.directory)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport} {table : PackedTable}
    (ran : runMarkedReopen reads.preflight report false aligned before = .ok table after) :
    ∃ base marker contents selected length,
      reads.checkpoint = .ok base ∧ before.directory.active.walBoundary = some marker ∧
      before.wal.active = some contents ∧ decode marker = .ok length ∧
      select length contents = .ok selected ∧ recoverSelected base selected = .ok table ∧
      after.directory = before.directory.syncDirectory ∧ after.wal.active = some selected ∧
      after.wal.crashImages = [some selected] := by
  have effect := ReopenRetry.start.runMarkedReopen_effect reads.preflight report false aligned
    (fun _ => reads.repair bound)
  rw [ran] at effect
  obtain ⟨_, directory, walChoices, validated, ready, rfl, walActive⟩ := effect
  obtain ⟨base, marker, length, checkpoint, markerRead, walRead, decoded, selected, replayed⟩ :=
    markedReopenPreflight_selected (checkpoint := reads.checkpoint) (marker := reads.marker)
      (wal := reads.wal) ready
  have contents := reads.walVisible _ walRead
  have settled : after.wal.active = some validated.selected := by
    rw [walActive]
    split
    · rfl
    · rename_i aligned
      rw [select_unchanged selected aligned]
      exact contents
  exact ⟨base, marker, validated.contents, validated.selected, length,
    checkpoint, reads.markerVisible _ markerRead, contents, decoded, selected, replayed,
    directory, settled, walChoices.trans (congrArg List.singleton settled)⟩

/-- A successful marked reopen has the exact same output when an
outstanding directory sync also completes before its observed operations.
The completed reopen already settles the resulting metadata. -/
theorem MarkedReopenReads.success_afterDirectorySync {before after : ReopenImage}
    (reads : MarkedReopenReads before) (bound : MarkerBound before.directory)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport} {table : PackedTable}
    (opened : runMarkedReopen reads.preflight report false aligned before = .ok table after) :
    runMarkedReopen reads.afterDirectorySync.preflight report false aligned before.syncMetadata =
      .ok table after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, directory, _⟩ := reads.success bound opened
  change runMarkedReopen reads.preflight report false aligned before.syncMetadata = _
  rw [runMarkedReopen_syncMetadata, opened]
  have settled : after.directory.syncDirectory = after.directory := by rw [directory]; rfl
  simp [ReopenImage.syncMetadata, settled]

/-- A finite sequence of observed marked reopen attempts and crashes.
An extra fsync of the stable database directory can take effect between
attempts, including a request made by an earlier process. It settles the
current metadata pair. Staging and WAL crash choices remain as modeled by
their own effects. -/
inductive MarkedReopenAttempts (initial : ReopenImage) : ReopenImage → Prop where
  | start : MarkedReopenAttempts initial initial
  | success (path : MarkedReopenAttempts initial before) (reads : MarkedReopenReads before)
      (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
      (ran : runMarkedReopen reads.preflight report false aligned before = .ok table after) :
      MarkedReopenAttempts initial after
  | failure (path : MarkedReopenAttempts initial before) (reads : MarkedReopenReads before)
      (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
      (ran : runMarkedReopen reads.preflight report false aligned before = .error message after) :
      MarkedReopenAttempts initial after
  | crash (path : MarkedReopenAttempts initial before)
      (pairSurvives : pair ∈ before.directory.crashImages) (walSurvives : wal ∈ before.wal.crashImages) :
      MarkedReopenAttempts initial (.crash pair wal)
  | delayedDirectorySync (path : MarkedReopenAttempts initial before) :
      MarkedReopenAttempts initial before.syncMetadata

/-- The initial marker bound suffices for the whole trace. Each short branch
derives its repair choice from the actual preflight bytes and current bound. -/
theorem MarkedReopenAttempts.toRetry {initial after : ReopenImage}
    (attempts : MarkedReopenAttempts initial after) (bound : MarkerBound initial.directory) :
    ReopenRetry initial after := by
  induction attempts with
  | start => exact .start
  | success _ reads report aligned ran earlier =>
    have effect := reads.retry_effect earlier (earlier.markerBound bound) report aligned
    rwa [ran] at effect
  | failure _ reads report aligned ran earlier =>
    have effect := reads.retry_effect earlier (earlier.markerBound bound) report aligned
    rwa [ran] at effect
  | crash _ pairSurvives walSurvives earlier => exact .crash earlier pairSurvives walSurvives
  | delayedDirectorySync _ earlier => exact .syncMetadata earlier

end Alvoki.WAL.Boundary
