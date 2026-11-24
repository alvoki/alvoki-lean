import Alvoki.Storage.Disk.LegacyMarkedBootstrap

namespace Alvoki.WAL.Boundary
open Storage

/-- The first marker carries the byte count of the full legacy prefix. The
checkpoint manifest binding stays fixed while the WAL is being adopted. -/
def LegacyBootstrapBindings (manifest : Option ByteArray) (history : List WAL.Write)
    (pair : DirectoryPublication.Bindings) : Prop :=
  pair.manifest = manifest ∧
    (pair.walBoundary = none ∨ pair.walBoundary = some (encode (WAL.encode history).size.toUInt64))

/-- Every legacy WAL choice contains an existing file with the same complete
ordinal history. Its incomplete terminal bytes may differ. -/
def LegacyWalBinding (history : List WAL.Write) (wal : Option ByteArray) : Prop :=
  ∃ bytes, wal = some bytes ∧ WAL.decodeOrdinals bytes = .ok history

/-- The selected WAL prefix is the only possible live or durable binding. -/
def ReopenImage.ExactLegacyWal (image : ReopenImage) (history : List WAL.Write) : Prop :=
  ∀ wal ∈ image.wal.active :: image.wal.crashImages, wal = some (WAL.encode history)

/-- A marker may be absent from some crash images and present in others
after rename and before directory sync. A present marker is only possible
once all WAL choices are the exact canonical prefix. -/
structure ReopenImage.LegacyBootstrapValid (image : ReopenImage)
    (manifest : Option ByteArray) (history : List WAL.Write) : Prop where
  metadata : image.directory.Valid (LegacyBootstrapBindings manifest history)
  wal : image.wal.Valid (LegacyWalBinding history)
  markedWal : ∀ pair ∈ image.directory.crashImages, pair.walBoundary ≠ none →
    image.ExactLegacyWal history

/-- The starting durability contract for an existing unmarked WAL. Every
admitted checkpoint name and every admitted complete WAL history agree. -/
theorem ReopenImage.LegacyBootstrapValid.ofUnmarked {image : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (metadata : image.directory.Valid fun pair => pair.manifest = manifest ∧ pair.walBoundary = none)
    (wal : image.wal.Valid (LegacyWalBinding history)) : image.LegacyBootstrapValid manifest history := by
  refine ⟨⟨metadata.activeMaySurvive, ?_⟩, wal, ?_⟩
  · intro pair chosen
    obtain ⟨checkpoint, unmarked⟩ := metadata.crashValid pair chosen
    exact ⟨checkpoint, Or.inl unmarked⟩
  · intro pair chosen marked
    exact False.elim (marked (metadata.crashValid pair chosen).2)

private theorem ReopenImage.LegacyBootstrapValid.ordinals {image : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : image.LegacyBootstrapValid manifest history) : WAL.OrdinalsFrom 1 history := by
  obtain ⟨_, _, decoded⟩ := valid.wal.activeValid
  exact WAL.decodeOrdinals_sound decoded

private theorem ReopenImage.LegacyBootstrapValid.selected {image : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write} {base table : PackedTable}
    {bytes selected : ByteArray} (valid : image.LegacyBootstrapValid manifest history)
    (visible : image.wal.active = some bytes)
    (recovered : recoverLegacy base bytes = .ok (selected, table)) : selected = WAL.encode history := by
  obtain ⟨old, oldVisible, oldDecoded⟩ := valid.wal.activeValid
  have sameInput := Option.some.inj (visible.symm.trans oldVisible)
  subst old
  obtain ⟨decodedHistory, decoded, canonical, _⟩ := recoverLegacy_exact recovered
  have sameHistory := Except.ok.inj (decoded.symm.trans oldDecoded)
  exact canonical.trans (congrArg WAL.encode sameHistory)

/-- An interrupted repair can expose the old WAL or the exact selected
replacement. Both have the same ordinal history. If the WAL needs repair,
no possible metadata pair already carries a marker. -/
theorem ReopenImage.LegacyBootstrapValid.repairCut {before after : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {base table : PackedTable} {bytes selected : ByteArray}
    (valid : before.LegacyBootstrapValid manifest history) (visible : before.wal.active = some bytes)
    (recovered : recoverLegacy base bytes = .ok (selected, table)) (shorter : selected.size < bytes.size)
    {cut : Nat} (ran : before.repairCut selected cut = some after) : after.LegacyBootstrapValid manifest history := by
  have canonical := valid.selected visible recovered
  have oldUnmarked (pair : DirectoryPublication.Bindings) (chosen : pair ∈ before.directory.crashImages) :
      pair.walBoundary = none := by
    by_cases marked : pair.walBoundary = none
    · exact marked
    have exactBinding := valid.markedWal pair chosen marked _ (List.mem_cons_self ..)
    have exactBytes := Option.some.inj (visible.symm.trans exactBinding)
    rw [canonical, exactBytes] at shorter
    exact False.elim (Nat.lt_irrefl _ shorter)
  unfold ReopenImage.repairCut at ran
  obtain ⟨wal, repaired, rfl⟩ := Option.map_eq_some_iff.mp ran
  have repairedWal := Publication.retry_preserves (acceptable := LegacyWalBinding history)
    (mayReplace := fun _ replacement => replacement = selected)
    (fun _ replacement _ chosen => ⟨replacement, rfl, by
      rw [chosen, canonical, WAL.decodeOrdinals_encode _ valid.ordinals]⟩)
    valid.wal (.attempt (.refl _) rfl cut repaired)
  by_cases complete : Publication.steps.length ≤ cut
  · refine ⟨?_, repairedWal, ?_⟩
    · simpa only [ite_eq_left complete] using valid.metadata.syncDirectory
    · intro pair chosen marked
      rw [ite_eq_left complete] at chosen
      obtain rfl := List.mem_singleton.mp chosen
      exact False.elim (marked (oldUnmarked _ valid.metadata.activeMaySurvive))
  · refine ⟨?_, repairedWal, ?_⟩
    · simpa only [ite_eq_right complete] using valid.metadata
    · intro pair chosen marked
      rw [ite_eq_right complete] at chosen
      exact False.elim (marked (oldUnmarked _ chosen))

private theorem ReopenImage.LegacyBootstrapValid.syncDirectory {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) :
    before.syncDirectory.LegacyBootstrapValid manifest history := by
  refine ⟨valid.metadata.syncDirectory, ⟨by simp [ReopenImage.syncDirectory], valid.wal.activeValid, ?_⟩, ?_⟩
  · intro contents chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact valid.wal.activeValid
  · intro pair chosen marked contents possible
    obtain rfl := List.mem_singleton.mp chosen
    have same : contents = before.wal.active := by
      simpa [ReopenImage.syncDirectory] using possible
    exact same.trans (valid.markedWal _ valid.metadata.activeMaySurvive marked _ (List.mem_cons_self ..))

private theorem ReopenImage.LegacyBootstrapValid.syncMetadata {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) :
    before.syncMetadata.LegacyBootstrapValid manifest history := by
  refine ⟨valid.metadata.syncDirectory, valid.wal, ?_⟩
  intro pair chosen marked
  obtain rfl := List.mem_singleton.mp chosen
  exact valid.markedWal _ valid.metadata.activeMaySurvive marked

private theorem ReopenImage.LegacyBootstrapValid.allowVisibleWal {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) :
    before.allowVisibleWal.LegacyBootstrapValid manifest history := by
  refine ⟨valid.metadata, ⟨by simp [ReopenImage.allowVisibleWal], valid.wal.activeValid, ?_⟩, ?_⟩
  · intro contents chosen
    rcases List.mem_cons.mp chosen with rfl | old
    · exact valid.wal.activeValid
    · exact valid.wal.crashValid _ old
  · intro pair chosen marked contents possible
    have earlier : contents ∈ before.wal.active :: before.wal.crashImages := by
      rcases List.mem_cons.mp possible with rfl | previous
      · exact List.mem_cons_self
      · exact previous
    exact valid.markedWal _ chosen marked _ earlier

private theorem ReopenImage.LegacyBootstrapValid.aligned {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) (report : AlignedSyncReport) :
    match performAlignedSync false report before with
    | .ok _ after | .error _ after => after.LegacyBootstrapValid manifest history := by
  cases report with
  | success => exact valid.syncDirectory
  | failure _ walSynced directorySynced =>
    cases walSynced <;> cases directorySynced
    · exact valid
    · exact valid.syncMetadata.allowVisibleWal
    · exact valid.allowVisibleWal
    · exact valid.syncDirectory

/-- In the shared durability schedule, repair and aligned-sync failures
retain the legacy invariant. If the schedule succeeds, only the exact
selected WAL binding can be read or survive, so marker publication may start. -/
theorem ReopenImage.LegacyBootstrapValid.durabilityReport {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    {base table : PackedTable} {bytes selected : ByteArray}
    (valid : before.LegacyBootstrapValid manifest history) (visible : before.wal.active = some bytes)
    (recovered : recoverLegacy base bytes = .ok (selected, table))
    (repair : Publication.Step → RepairReport) (aligned : AlignedSyncReport) :
    let preflight : MarkedPreflight := ⟨bytes, selected, table⟩
    match runMarkedReopen (.ok preflight) repair false aligned before with
    | .ok _ after => after.LegacyBootstrapValid manifest history ∧ after.ExactLegacyWal history
    | .error _ after => after.LegacyBootstrapValid manifest history := by
  let preflight : MarkedPreflight := ⟨bytes, selected, table⟩
  have canonical := valid.selected visible recovered
  by_cases shorter : selected.size < bytes.size
  · have outcome := runMarkedReopen_repair_outcome preflight repair false aligned before shorter
    change (match runMarkedReopen (.ok preflight) repair false aligned before with
      | .ok _ after => after.LegacyBootstrapValid manifest history ∧ after.ExactLegacyWal history
      | .error _ after => after.LegacyBootstrapValid manifest history)
    cases ran : runMarkedReopen (.ok preflight) repair false aligned before with
    | ok _ after =>
      rw [ran] at outcome
      refine ⟨valid.repairCut visible recovered shorter outcome.2, ?_⟩
      have complete := outcome.2
      change before.repairCut selected Publication.steps.length = some after at complete
      rw [before.repair_complete] at complete
      cases complete
      simp [ReopenImage.ExactLegacyWal, Publication.Image.settled, canonical]
    | error _ after =>
      rw [ran] at outcome
      obtain ⟨cut, applied⟩ := outcome
      exact valid.repairCut visible recovered shorter applied
  · have same := recoverLegacy_selected_eq_of_aligned recovered shorter
    simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen_aligned _ _ shorter]
    have exactWal : before.syncDirectory.ExactLegacyWal history := by
      rw [ReopenImage.ExactLegacyWal]
      change ∀ wal ∈ [before.wal.active, before.wal.active], wal = some (WAL.encode history)
      simp [visible, ← same, canonical]
    have safe := valid.aligned aligned
    cases applied : performAlignedSync false aligned before with
    | ok _ after =>
      rw [applied] at safe
      have settled : after = before.syncDirectory := by
        cases aligned <;> cases applied
        rfl
      simp only [Bind.bind, EStateM.bind, applied, Pure.pure, EStateM.pure]
      exact ⟨safe, settled.symm ▸ exactWal⟩
    | error _ after =>
      rw [applied] at safe
      simp only [Bind.bind, EStateM.bind, applied]
      exact safe

private theorem legacyMarkerCut_valid {before after : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write} {cut : Nat}
    (valid : before.directory.Valid (LegacyBootstrapBindings manifest history))
    (ran : (Publication.steps.take cut).foldlM (legacyMarkerStep (encode (WAL.encode history).size.toUInt64))
      before = some after) :
    after.directory.Valid (LegacyBootstrapBindings manifest history) ∧ after.wal = before.wal := by
  let bytes := encode (WAL.encode history).size.toUInt64
  have replacement (pair : DirectoryPublication.Bindings) (accepted : LegacyBootstrapBindings manifest history pair) :
      LegacyBootstrapBindings manifest history (pair.replace .walBoundary bytes) :=
    ⟨accepted.1, Or.inr rfl⟩
  rcases cut with _ | _ | _ | _ | cut
  · cases ran
    exact ⟨valid, rfl⟩
  · cases ran
    exact ⟨⟨valid.activeMaySurvive, valid.crashValid⟩, rfl⟩
  · cases ran
    exact ⟨⟨valid.activeMaySurvive, valid.crashValid⟩, rfl⟩
  · cases ran
    refine ⟨⟨List.mem_append_left _ (List.mem_map_of_mem valid.activeMaySurvive), ?_⟩, rfl⟩
    intro pair chosen
    rcases List.mem_append.mp chosen with updated | unchanged
    · obtain ⟨earlier, survived, rfl⟩ := List.mem_map.mp updated
      exact replacement _ (valid.crashValid _ survived)
    · exact valid.crashValid _ unchanged
  · simp only [Publication.steps, List.take_succ_cons, List.take_nil] at ran
    cases ran
    refine ⟨⟨List.mem_cons_self, ?_⟩, rfl⟩
    intro pair chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact replacement _ valid.activeValid

private theorem performLegacyMarker_outcome (report : Publication.Step → RepairReport) (bytes : ByteArray)
    (action : Publication.Step) (before : ReopenImage) :
    match performLegacyMarker report bytes action before with
    | .ok _ after => legacyMarkerStep bytes before action = some after
    | .error _ after => after = before ∨ legacyMarkerStep bytes before action = some after := by
  cases reported : report action with
  | success =>
    cases applied : legacyMarkerStep bytes before action <;> simp [performLegacyMarker, reported, applied]
  | failure message tookEffect =>
    cases tookEffect
    · simp [performLegacyMarker, reported]
    · cases applied : legacyMarkerStep bytes before action <;> simp [performLegacyMarker, reported, applied]

/-- Any reported success or error of the actual marker schedule leaves the
same WAL and an admissible optional marker. Its WAL must already be durable
before any marker step is attempted. -/
theorem ReopenImage.LegacyBootstrapValid.publishMarker {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) (durable : before.ExactLegacyWal history)
    (report : Publication.Step → RepairReport) :
    match Publication.run (performLegacyMarker report (encode (WAL.encode history).size.toUInt64)) before with
    | .ok _ after | .error _ after => after.LegacyBootstrapValid manifest history := by
  let bytes := encode (WAL.encode history).size.toUInt64
  have outcome := Publication.run_effects_outcome (legacyMarkerStep bytes) (performLegacyMarker report bytes)
    (by
      intro action state
      have observed := performLegacyMarker_outcome report bytes action state
      cases ran : performLegacyMarker report bytes action state <;> simpa only [ran] using observed)
    Publication.steps before
  change (match (Publication.steps.forM (performLegacyMarker report bytes)) before with
      | .ok _ after | .error _ after => after.LegacyBootstrapValid manifest history)
  cases ran : (Publication.steps.forM (performLegacyMarker report bytes)) before with
  | ok _ after =>
    rw [ran] at outcome
    have complete : (Publication.steps.take Publication.steps.length).foldlM
        (legacyMarkerStep bytes) before = some after := by
      simpa only [List.take_length] using outcome
    obtain ⟨metadata, sameWal⟩ := legacyMarkerCut_valid valid.metadata complete
    refine ⟨metadata, sameWal.symm ▸ valid.wal, fun _ _ _ => ?_⟩
    unfold ReopenImage.ExactLegacyWal
    rw [sameWal]
    exact durable
  | error _ after =>
    rw [ran] at outcome
    obtain ⟨cut, executed⟩ := outcome
    obtain ⟨metadata, sameWal⟩ := legacyMarkerCut_valid valid.metadata executed
    refine ⟨metadata, sameWal.symm ▸ valid.wal, fun _ _ _ => ?_⟩
    unfold ReopenImage.ExactLegacyWal
    rw [sameWal]
    exact durable

/-- All results of the actual legacy-branch schedule preserve the admissible
legacy history and directory pairs. The existing WAL and absent marker are
the successful locked lookup observations. Read, replay and size validation
can fail without risking installation of an invalid marker. -/
theorem ReopenImage.LegacyBootstrapValid.adoptReport {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write} {image : CheckpointPublication.Image}
    (valid : before.LegacyBootstrapValid manifest history)
    (checkpointReads : CheckpointReadObservations image manifest)
    (walReads : MarkedWalReads before) (unmarked : walReads.marker = .ok none)
    {bytes : ByteArray} (readWal : walReads.wal = .ok (some bytes)) (reports : LegacyOpenReports) :
    match runLegacyMarkedOpen checkpointReads.result walReads.marker walReads.wal reports before with
    | .ok _ after | .error _ after => after.LegacyBootstrapValid manifest history := by
  have visible := walReads.walVisible _ readWal
  rw [unmarked, readWal]
  cases loaded : checkpointReads.result with
  | error message => exact valid
  | ok checkpoint =>
    cases recovered : recoverLegacy (checkpoint.getD (.empty, 0)).1 bytes with
    | error message =>
      unfold runLegacyMarkedOpen
      simp only [legacyPreflight, withOpenWal, Option.mapM, Bind.bind, Except.bind,
        Pure.pure, Except.pure, recovered]
      exact valid
    | ok selectedTable =>
      obtain ⟨selected, table⟩ := selectedTable
      let preflight : MarkedPreflight := ⟨bytes, selected, table⟩
      have checked : legacyPreflight (.ok checkpoint) (.ok none) (.ok (some bytes)) =
          .ok (preflight, (checkpoint.getD (.empty, 0)).2) := by
        simp [legacyPreflight, withOpenWal, Option.mapM, Bind.bind, Except.bind,
          Pure.pure, Except.pure, recovered, preflight]
      unfold runLegacyMarkedOpen
      rw [checked]
      have durability := valid.durabilityReport visible recovered reports.repair reports.aligned
      change (match runMarkedReopen (.ok preflight) reports.repair false reports.aligned before with
        | .ok _ after => after.LegacyBootstrapValid manifest history ∧ after.ExactLegacyWal history
        | .error _ after => after.LegacyBootstrapValid manifest history) at durability
      simp only [Bind.bind, EStateM.bind]
      cases repaired : runMarkedReopen (.ok preflight) reports.repair false reports.aligned before with
      | error _ after =>
        rw [repaired] at durability
        exact durability
      | ok _ after =>
        rw [repaired] at durability
        by_cases fits : selected.size < UInt64.size
        · have canonical := valid.selected visible recovered
          simp only [show preflight.selected = selected from rfl, fits, ite_true, Pure.pure]
          rw [canonical]
          have marker := durability.1.publishMarker durability.2 reports.marker
          cases published : Publication.run (performLegacyMarker reports.marker
              (encode (WAL.encode history).size.toUInt64)) after <;>
            simpa only [EStateM.bind, published, EStateM.pure] using marker
        · simp only [show preflight.selected = selected from rfl, fits, ite_false]
          exact durability.1

/-- A power cut chooses one allowed pair of metadata names and one allowed
WAL binding. No surviving marker can select an absent or torn WAL. -/
theorem ReopenImage.LegacyBootstrapValid.crash {before : ReopenImage}
    {manifest : Option ByteArray} {history : List WAL.Write}
    (valid : before.LegacyBootstrapValid manifest history) {pair : DirectoryPublication.Bindings}
    {wal : Option ByteArray} (metadata : pair ∈ before.directory.crashImages)
    (contents : wal ∈ before.wal.crashImages) :
    (ReopenImage.crash pair wal).LegacyBootstrapValid manifest history := by
  refine ⟨DirectoryPublication.Image.settled_valid (valid.metadata.crashValid _ metadata),
    Publication.Image.settled_valid (valid.wal.crashValid _ contents), ?_⟩
  intro candidate chosen marked binding selected
  obtain rfl := List.mem_singleton.mp chosen
  have same : binding = wal := by simpa [ReopenImage.crash, Publication.Image.settled] using selected
  exact same.trans (valid.markedWal _ metadata marked _ (List.mem_cons_of_mem _ contents))

/-- With the same checkpoint base, either marker choice selects the exact
same bytes and table as replaying the complete legacy history. The caller
supplies the validated checkpoint base and successful extent check. -/
theorem ReopenImage.LegacyBootstrapValid.replay {image : ReopenImage} {manifest : Option ByteArray}
    {history : List WAL.Write} (valid : image.LegacyBootstrapValid manifest history)
    {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadata : pair ∈ image.directory.active :: image.directory.crashImages)
    (contents : wal ∈ image.wal.active :: image.wal.crashImages) {base table : PackedTable}
    (recovered : recoverSelected base (WAL.encode history) = .ok table)
    (fits : (WAL.encode history).size < UInt64.size) :
    pair.manifest = manifest ∧ ∃ bytes, wal = some bytes ∧
      (match pair.walBoundary with
      | none => recoverLegacy base bytes
      | some marker => do
        let length ← decode marker
        recoverMarked base length bytes) = .ok (WAL.encode history, table) ∧
      (pair.walBoundary = none ∨ bytes = WAL.encode history) := by
  have canSurvive : pair ∈ image.directory.crashImages := (List.mem_cons.mp metadata).elim
    (fun same => same.symm ▸ valid.metadata.activeMaySurvive) id
  have ⟨sameManifest, marker⟩ := valid.metadata.crashValid _ canSurvive
  have ⟨bytes, present, decoded⟩ := (List.mem_cons.mp contents).elim
    (fun same => same.symm ▸ valid.wal.activeValid) (valid.wal.crashValid wal)
  refine ⟨sameManifest, bytes, present, ?_⟩
  rcases marker with absent | published
  · refine ⟨?_, Or.inl absent⟩
    rw [absent]
    have selected := (WAL.repairPrefix_getD_eq_extract bytes).trans (WAL.decodeOrdinals_reencode decoded).symm
    simp [recoverLegacy, selected, recovered, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have exactWal := valid.markedWal _ canSurvive (by rw [published]; simp) _ contents
    have exactBytes := Option.some.inj (present.symm.trans exactWal)
    refine ⟨?_, Or.inr exactBytes⟩
    rw [published, exactBytes]
    have selected := select_encoded history ByteArray.empty fits
    rw [ByteArray.append_empty] at selected
    change (do
      let count ← decode (encode (WAL.encode history).size.toUInt64)
      recoverMarked base count (WAL.encode history)) = _
    rw [decode_encode]
    change recoverMarked base (WAL.encode history).size.toUInt64 (WAL.encode history) = _
    simp only [recoverMarked, Bind.bind, Except.bind, selected, recovered, Pure.pure, Except.pure]

end Alvoki.WAL.Boundary
