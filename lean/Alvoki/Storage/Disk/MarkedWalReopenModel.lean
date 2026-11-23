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

/-- The repair path takes its replacement from the visible marker and WAL.
Every marker that could still survive a crash must fit in that replacement. -/
structure ReopenImage.RepairsTo (image : ReopenImage) (length : UInt64) (trimmed : ByteArray) : Prop where
  visibleMarker : ∃ marker, image.directory.active.walBoundary = some marker ∧ decode marker = .ok length
  selected : ∃ contents, image.wal.active = some contents ∧ select length contents = .ok trimmed ∧
    trimmed.size < contents.size
  coversCandidates : ∀ pair ∈ image.directory.active :: image.directory.crashImages,
    ∀ marker count, pair.walBoundary = some marker → decode marker = .ok count → count.toNat ≤ length.toNat

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
  obtain ⟨active, length, present, decoded, bounded⟩ := write_cut_active_bounds_marker cut oldFits newFits
  have sameVisibleMarker : marker = active :=
    Option.some.inj (visibleMarker.symm.trans (activeAgrees.trans present))
  have visibleDecode : decode marker = .ok length := sameVisibleMarker.symm ▸ decoded
  rw [visibleDecode] at selected
  refine ⟨length, ⟨⟨marker, visibleMarker, visibleDecode⟩, ⟨wal, visibleWal, selected, shorter⟩, ?_⟩⟩
  intro pair chosen markerBytes count marked decodedCount
  have markerChosen : pair.walBoundary = boundary.active ∨ pair.walBoundary ∈ boundary.crashImages := by
    rcases List.mem_cons.mp chosen with rfl | survives
    · exact .inl activeAgrees
    · exact .inr (crashAgrees pair survives)
  obtain ⟨candidate, candidateCount, sameMarker, candidateDecode, fits⟩ := bounded _ markerChosen
  have bytesAgree : markerBytes = candidate := Option.some.inj (marked.symm.trans sameMarker)
  have countAgree : count = candidateCount :=
    Except.ok.inj (decodedCount.symm.trans (bytesAgree.symm ▸ candidateDecode))
  simpa only [countAgree] using fits

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
  have accepted : accepts image.directory expected wal := by
    rcases List.mem_cons.mp walChosen with rfl | survives
    · exact valid.activeValid
    · exact valid.crashValid _ survives
  obtain ⟨marker, contents, length, boundary, present, decoded, selected⟩ := accepted pair metadataChosen
  refine ⟨marker, contents, boundary, present, ?_⟩
  rw [decoded]
  change (do let bytes ← select length contents; recoverSelected checkpoint bytes) = _
  rw [selected]
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

private def performRepair (report : Publication.Step → RepairReport) (trimmed : ByteArray)
    (action : Publication.Step) : EStateM String ReopenImage Unit := fun image =>
  match report action with
  | .success =>
    match image.repairStep trimmed action with
    | some after => .ok () after
    | none => .error "invalid repair operation" image
  | .failure message tookEffect =>
    .error message (if tookEffect then (image.repairStep trimmed action).getD image else image)

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
  induction actions generalizing image with
  | nil => rfl
  | cons action rest ih =>
    have effect := performRepair_outcome report trimmed action image
    change (match EStateM.bind (performRepair report trimmed action)
        (fun _ => rest.forM (performRepair report trimmed)) image with
      | .ok _ after => image.repairSteps trimmed (action :: rest) = some after
      | .error _ after => ∃ cut, image.repairSteps trimmed ((action :: rest).take cut) = some after)
    unfold EStateM.bind
    cases ran : performRepair report trimmed action image with
    | error message after =>
      rw [ran] at effect
      change ∃ cut, image.repairSteps trimmed ((action :: rest).take cut) = some after
      rcases effect with rfl | stepped
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp [ReopenImage.repairSteps, List.foldlM_cons, stepped]⟩
    | ok result next =>
      rw [ran] at effect
      have tail := ih next
      change (match (rest.forM (performRepair report trimmed)) next with
        | .ok _ after => image.repairSteps trimmed (action :: rest) = some after
        | .error _ after => ∃ cut, image.repairSteps trimmed ((action :: rest).take cut) = some after)
      cases remaining : (rest.forM (performRepair report trimmed)) next with
      | ok result after =>
        rw [remaining] at tail
        change image.repairSteps trimmed (action :: rest) = some after
        simp only [ReopenImage.repairSteps, List.foldlM_cons, effect]
        exact tail
      | error message after =>
        rw [remaining] at tail
        obtain ⟨cut, prefixRun⟩ := tail
        change ∃ cut, image.repairSteps trimmed ((action :: rest).take cut) = some after
        refine ⟨cut + 1, ?_⟩
        simp only [ReopenImage.repairSteps, List.take_succ_cons, List.foldlM_cons, effect]
        exact prefixRun

/-- The aligned path asks for both the WAL file and the directory sync.
A reported failure may follow completion of any subset of those requests. -/
inductive AlignedSyncReport where
  | success
  | failure (message : String) (walSynced directorySynced : Bool)

private def performAlignedSync (walAlreadySynced : Bool) (report : AlignedSyncReport) :
    EStateM String ReopenImage Unit := fun image =>
  match report with
  | .success => .ok () image.syncDirectory
  | .failure message walSynced directorySynced =>
    .error message (if directorySynced then
      if walAlreadySynced || walSynced then image.syncDirectory else image.syncMetadata.allowVisibleWal
    else if walSynced then image.allowVisibleWal else image)

/-- Read-only preflight of an already marked database. The checkpoint input
is the result of opening its manifest and run set, with an empty base on
absence. The marker and WAL inputs include metadata and read errors. -/
def markedReopenPreflight (checkpoint : Except String PackedTable)
    (marker wal : Except String ByteArray) : Except String (ByteArray × ByteArray) := do
  let base ← checkpoint
  let count ← marker >>= decode
  let contents ← wal
  let selected ← select count contents
  let _ ← recoverSelected base selected
  return (contents, selected)

theorem markedReopenPreflight_selected {checkpoint : Except String PackedTable}
    {marker wal : Except String ByteArray} {contents selected : ByteArray}
    (ready : markedReopenPreflight checkpoint marker wal = .ok (contents, selected)) :
    ∃ base markerBytes length recovered, checkpoint = .ok base ∧ marker = .ok markerBytes ∧
      wal = .ok contents ∧ decode markerBytes = .ok length ∧
      select length contents = .ok selected ∧ recoverSelected base selected = .ok recovered := by
  cases checkpoint with
  | error => contradiction
  | ok base =>
    cases marker with
    | error => contradiction
    | ok markerBytes =>
      change (do
        let length ← decode markerBytes
        let bytes ← wal
        let chosen ← select length bytes
        let _ ← recoverSelected base chosen
        pure (bytes, chosen)) = .ok (contents, selected) at ready
      cases decoded : decode markerBytes with
      | error => rw [decoded] at ready; contradiction
      | ok length =>
        rw [decoded] at ready
        cases wal with
        | error => contradiction
        | ok bytes =>
          change (do
            let chosen ← select length bytes
            let _ ← recoverSelected base chosen
            pure (bytes, chosen)) = .ok (contents, selected) at ready
          cases accepted : select length bytes with
          | error => rw [accepted] at ready; contradiction
          | ok chosen =>
            rw [accepted] at ready
            change ((fun _ : PackedTable => (bytes, chosen)) <$> recoverSelected base chosen) =
              .ok (contents, selected) at ready
            cases replayed : recoverSelected base chosen with
            | error => rw [replayed] at ready; contradiction
            | ok recovered =>
              rw [replayed] at ready
              have pair := Prod.mk.inj (Except.ok.inj ready)
              obtain ⟨rfl, rfl⟩ := pair
              exact ⟨base, markerBytes, length, recovered, rfl, rfl, rfl, decoded, accepted, replayed⟩

/-- Interpret the shared reopen decision in a state-and-error monad. The
`walAlreadySynced` fact may be used only when the caller knows the current
visible inode's bytes are durable. A file-only effect allows the visible
contents alongside prior crash choices. A directory-only effect settles
metadata and permits both prior and visible contents unless the visible
contents are known durable. -/
def runMarkedReopen (preflight : Except String (ByteArray × ByteArray))
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool)
    (aligned : AlignedSyncReport) : EStateM String ReopenImage Unit :=
  match preflight with
  | .error message => fun image => .error message image
  | .ok (contents, selected) =>
    Publication.runReopen contents.size selected.size
      (fun _ => Publication.run (performRepair report selected))
      (fun _ => performAlignedSync walAlreadySynced aligned)

theorem runMarkedReopen_preflight_error {checkpoint : Except String PackedTable}
    {marker wal : Except String ByteArray} {message : String}
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
    (path : ReopenRetry initial before) (preflight : Except String (ByteArray × ByteArray))
    (report : Publication.Step → RepairReport) (walAlreadySynced : Bool) (aligned : AlignedSyncReport)
    (repair : ∀ contents selected, preflight = .ok (contents, selected) →
      selected.size < contents.size → ∃ length, before.RepairsTo length selected) :
    match runMarkedReopen preflight report walAlreadySynced aligned before with
    | .ok _ after => ReopenRetry initial after ∧ after.directory = before.directory.syncDirectory ∧
        after.wal.crashImages = [after.wal.active]
    | .error _ after => ReopenRetry initial after := by
  cases preflight with
  | error message => exact path
  | ok checked =>
    obtain ⟨contents, selected⟩ := checked
    by_cases shorter : selected.size < contents.size
    · simp only [runMarkedReopen, Publication.runReopen_repair _ _ shorter]
      obtain ⟨length, covers⟩ := repair contents selected rfl shorter
      have outcome := repairSchedule_outcome report selected Publication.steps before
      unfold Publication.run
      cases result : (Publication.steps.forM (performRepair report selected)) before with
      | ok value after =>
        rw [result] at outcome
        have completed : before.repairCut selected Publication.steps.length = some after := by
          rw [← before.repairSteps_prefix]
          simpa only [List.take_length] using outcome
        have ran := before.repair_complete selected
        rw [ran] at completed
        cases completed
        exact ⟨.repair path covers ran, rfl, rfl⟩
      | error message after =>
        rw [result] at outcome
        obtain ⟨cut, ran⟩ := outcome
        rw [before.repairSteps_prefix] at ran
        exact .repair path covers ran
    · simp only [runMarkedReopen, Publication.runReopen_aligned _ _ shorter]
      cases aligned with
      | success => exact ⟨.syncDirectory path, rfl, rfl⟩
      | failure message walSynced directorySynced =>
        simp only [performAlignedSync]
        split
        · split
          · exact .syncDirectory path
          · exact .allowVisibleWal (.syncMetadata path)
        · split
          · exact .allowVisibleWal path
          · exact path

end Alvoki.WAL.Boundary
